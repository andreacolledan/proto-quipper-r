{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
{-# HLINT ignore "Use record patterns" #-}
module Checking.Language(
    TypingContext,
    runValueTypeInference,
    runTermTypeInference,
    runValueTypeChecking,
    runTermTypeChecking,
    emptyctx
) where

import AST.Bundle (Bundle, BundleType, Wide (wireCount), LabelId, isBundleSubtype)
import qualified AST.Bundle as Bundle
import AST.Circuit
import AST.Index
import AST.Language
import Checking.Bundle
    ( runBundleTypeInferenceWithRemaining,
      LabelContext,
      WireTypingError(..)
    )
import Checking.Circuit

import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Maybe (fromMaybe)
import Data.Either.Extra (mapLeft)
import Data.Map (Map)
import qualified Data.Map as Map
import PrettyPrinter
import Debug.Trace (traceId, traceShowId, traceShowM, traceShow)

-- Corresponds to Γ in the paper
type TypingContext = Map VariableId Type

-- The state of a typing derivation:
-- - the index context Θ (nonlinear)
-- - the typing context Γ (linear/nonlinear)
-- - the label context Q (linear)
-- - a counter for fresh type variables
data TypingEnvironment = TypingEnvironment {
    --indexContext :: IndexContext,
    typingContext :: TypingContext,
    labelContext :: LabelContext,
    freeVarCounter :: Int
}
-- check if a typing environment contains any linear variable.
envIsLinear :: TypingEnvironment -> Bool
envIsLinear TypingEnvironment{typingContext = gamma, labelContext = q} = (any isLinear . Map.elems) gamma || Map.size q > 0

emptyctx :: Map a b
emptyctx = Map.empty

--- TYPING ERRORS ---------------------------------------------------------------


-- Typing errors
data TypingError
    = WireTypingError WireTypingError
    | UnboundVariable VariableId
    | UnusedLinearVariable VariableId
    | ShadowedLinearVariable VariableId
    | LinearResourcesInLiftedTerm
    | UnexpectedType (Either Term Value) Type Type
    | MismatchedCircuitInterface CircuitInterfaceType Circuit LabelContext Bundle
    | UnexpectedWidthAnnotation Term Index Index
    | UnexpectedTypeConstructor (Either Term Value) Type Type
    | UnusedLinearResources TypingContext LabelContext
    | UnexpectedBoxingType Term Type BundleType
    | UnboxableType Value Type
    | UnfoldableType Value Type
    | NonincreasingStepFunction Value Type Type
    | IndexVariableCapture Value IndexVariableId Type
    deriving (Eq)

data CircuitInterfaceType = Input | Output deriving (Eq)
instance Show CircuitInterfaceType where
    show Input = "input"
    show Output = "output"

instance Show TypingError where
    show (WireTypingError err) = show err
    show (UnboundVariable id) = "Unbound variable " ++ id
    show (UnusedLinearVariable id) = "Unused linear variable " ++ id
    show (ShadowedLinearVariable id) = "Shadowed linear variable " ++ id
    show LinearResourcesInLiftedTerm = "Linear resources consumed in a lifted term"
    show (UnexpectedType exp typ1 typ2) =
        "Expected expression " ++ pretty exp ++ " to have type " ++ pretty typ1 ++ ", got " ++ pretty typ2 ++ " instead"
    show (MismatchedCircuitInterface interfaceType circ q b) =
        "Bundle " ++ pretty b ++ " is not a valid " ++ show interfaceType ++ " interface for circuit " ++ pretty circ
        ++ ", whose " ++ show interfaceType ++ " labels are " ++ pretty q
    show (UnexpectedWidthAnnotation m i j) =
        "Expected term " ++ pretty m ++ " to have width annotation " ++ pretty i ++ ", got " ++ pretty j ++ " instead"
    show (UnexpectedTypeConstructor exp typ1 typ2) =
        "Expected expression " ++ pretty exp ++ " to have " ++ printConstructor typ1 ++ ", got type " ++ pretty typ2 ++ " instead"
    show (UnusedLinearResources gamma q) = "Unused linear resources in typing contexts: " ++ pretty gamma ++ " ; " ++ pretty q
    show (UnexpectedBoxingType m btype1 btype2) =
        "Expected input type of boxed circuit " ++ pretty m ++ " to be " ++ pretty btype1 ++ ", got " ++ pretty btype2 ++ " instead"
    show (UnboxableType v typ) = "Cannot box value " ++ pretty v ++ " of type " ++ pretty typ
    show (UnfoldableType v typ) = "Cannot fold value " ++ pretty v ++ " of type " ++ pretty typ
    show (NonincreasingStepFunction v typ1 typ2) =
        "Expected step function " ++ pretty v ++ "'s output type to be" ++ pretty typ1 ++ ", got " ++ pretty typ2 ++ " instead"
    show (IndexVariableCapture v id typ) = "Index variable " ++ id ++ " cannot occur in type " ++ pretty typ ++ " of step function " ++ pretty v

-- Shows the name of the top level constructor of a type
printConstructor :: Type -> String
printConstructor UnitType = "unit type"
printConstructor (WireType _) = "wire type"
printConstructor (Tensor _ _) = "tensor type"
printConstructor (Circ {}) = "circuit type"
printConstructor (Arrow {}) = "arrow type"
printConstructor (Bang _) = "bang type"
printConstructor (List _ _) = "list type"
printConstructor (TypeVariable _) = "type variable"



--- TYPING ENVIRONMENT OPERATIONS ---------------------------------------------------------------


-- lookup a variable in the typing context, remove it if it is linear
-- throws an error if the variable is not found
typingContextLookup :: VariableId -> StateT TypingEnvironment (Either TypingError) Type
typingContextLookup id = do
    env@TypingEnvironment{typingContext = gamma} <- get
    typ <- maybe (throwError $ UnboundVariable id) return (Map.lookup id gamma)
    when (isLinear typ) $ put env{typingContext = Map.delete id gamma}
    return typ

labelContextLookup :: LabelId -> StateT TypingEnvironment (Either TypingError) Bundle.WireType
labelContextLookup id = do
    env@TypingEnvironment{labelContext = q} <- get
    outcome <- maybe (throwError $ WireTypingError $ UnboundLabel id) return (Map.lookup id q)
    put $ env{labelContext = Map.delete id q}
    return outcome

freshVariableName :: StateT TypingEnvironment (Either TypingError) VariableId
freshVariableName = do
    env@TypingEnvironment{freeVarCounter = c} <- get
    put $ env{freeVarCounter = c + 1}
    return $ "x" ++ show c

substituteInEnvironment :: TypeSubstitution -> StateT TypingEnvironment (Either TypingError) ()
substituteInEnvironment sub = do
    env@TypingEnvironment{typingContext = gamma} <- get
    let gamma' = Map.map (applyTypeSub sub) gamma
    put env{typingContext = gamma'}



--- DERIVATION COMBINATORS ---------------------------------------------------------------


-- locally bind a variable in the scope of an existing derivation
withBoundVariable :: VariableId -> Type -> StateT TypingEnvironment (Either TypingError) a
                    -> StateT TypingEnvironment (Either TypingError) a
withBoundVariable x typ der = do
    bindVariable x typ
    outcome <- der
    unbindVariable x --this throws an error if x is linear and der does not consume it
    return outcome
    where
        bindVariable :: VariableId -> Type -> StateT TypingEnvironment (Either TypingError) ()
        bindVariable id typ = do
            env@TypingEnvironment{typingContext = gamma} <- get
            when (Map.member id gamma) $ throwError $ ShadowedLinearVariable id
            let gamma' = Map.insert id typ gamma
            put env{typingContext = gamma'}
        unbindVariable :: VariableId -> StateT TypingEnvironment (Either TypingError) ()
        unbindVariable id = do
            env@TypingEnvironment{typingContext = gamma} <- get
            case Map.lookup id gamma of
                Nothing -> return ()
                Just t -> do
                    when (isLinear t) (throwError $ UnusedLinearVariable id)
                    put env{typingContext = Map.delete id gamma}

-- make an existing derivation also return the amount of wires it consumes
withWireCount :: StateT TypingEnvironment (Either TypingError) a
                    -> StateT TypingEnvironment (Either TypingError) (a, Index)
withWireCount der = do
    TypingEnvironment{typingContext = gamma, labelContext = q} <- get
    outcome <- der
    TypingEnvironment{typingContext = gamma', labelContext = q'} <- get
    -- count how many linear resources have disappeared from the contexts
    let gammaDiff = Map.difference gamma gamma'
    let qDiff = Map.difference q q'
    let resourceCount = wireCount gammaDiff `Plus` wireCount qDiff
    return (outcome, simplify resourceCount)

-- make an existing derivation fail if it consumes any linear resources from the pre-existing environment
withNonLinearContext :: StateT TypingEnvironment (Either TypingError) a
                        -> StateT TypingEnvironment (Either TypingError) a
withNonLinearContext der = do
    TypingEnvironment{typingContext = gamma, labelContext = q} <- get
    outcome <- der
    TypingEnvironment{typingContext = gamma', labelContext = q'} <- get
    let gammaDiff = Map.difference gamma gamma'
    let qDiff = Map.difference q q'
    when ((any isLinear . Map.elems) gammaDiff || Map.size qDiff > 0) $ throwError LinearResourcesInLiftedTerm
    return outcome

tryUnify :: Type -> Type -> TypingError -> StateT TypingEnvironment (Either TypingError) TypeSubstitution
tryUnify typ1 typ2 err = case mgtu typ1 typ2 of
    Just s -> return s
    Nothing -> throwError err



--- BUNDLE CHECKING WITHIN TYPE CHECKING ------------------------------------------------------------

-- Turns a wire bundle into an equivalent PQR value
embedWireBundle :: Bundle -> Value
embedWireBundle Bundle.UnitValue = UnitValue
embedWireBundle (Bundle.Label id) = Label id
embedWireBundle (Bundle.Pair b1 b2) = Pair (embedWireBundle b1) (embedWireBundle b2)
embedWireBundle Bundle.Nil = Nil
embedWireBundle (Bundle.Cons b1 b2) = Cons (embedWireBundle b1) (embedWireBundle b2)

-- Turns a bundle type into an equivalent PQR type
embedBundleType :: BundleType -> Type
embedBundleType Bundle.UnitType = UnitType
embedBundleType (Bundle.WireType wtype) = WireType wtype
embedBundleType (Bundle.Tensor b1 b2) = Tensor (embedBundleType b1) (embedBundleType b2)
embedBundleType (Bundle.List i b) = List i (embedBundleType b)
embedBundleType (Bundle.TypeVariable id) = TypeVariable id


--- PQR TYPE INFERENCE ---------------------------------------------------------------

inferValueType :: Value -> StateT TypingEnvironment (Either TypingError) (Type, TypeSubstitution)
inferValueType UnitValue = return (UnitType, Map.empty)
inferValueType (Label id) = do
    wtype <- labelContextLookup id
    return (WireType wtype, Map.empty)
inferValueType (Variable id) = do
    typ <- typingContextLookup id
    return (typ, Map.empty)
inferValueType (Pair v w) = do
    (typ1, sub1) <- inferValueType v
    substituteInEnvironment sub1
    (typ2, sub2) <- inferValueType w
    return (Tensor (applyTypeSub sub2 typ1) typ2, compose sub1 sub2)
inferValueType (BoxedCircuit inB circ outB) = lift $ do
    (inQ, outQ) <- mapLeft WireTypingError $ inferCircuitSignature circ
    (inBtype, inQ') <- mapLeft WireTypingError $ runBundleTypeInferenceWithRemaining inQ inB
    (outBtype, outQ') <- mapLeft WireTypingError $ runBundleTypeInferenceWithRemaining outQ outB
    unless (Map.null inQ') $ throwError $ MismatchedCircuitInterface Input circ inQ' inB
    unless (Map.null outQ') $ throwError $ MismatchedCircuitInterface Output circ outQ' outB
    return (Circ (Number $ width circ) inBtype outBtype, Map.empty)
inferValueType (Abs x intyp m) = do
    ((outtyp, i, sub), j) <- withWireCount $ withBoundVariable x intyp $ inferTermType m
    return (Arrow (applyTypeSub sub intyp) outtyp i j, sub)
inferValueType (Lift m) = do
    (typ, i, sub) <- withNonLinearContext $ inferTermType m
    unless (checkEq i (Number 0)) (throwError $ UnexpectedWidthAnnotation m (Number 0) i)
    return (Bang typ, sub)
inferValueType Nil = do
    a <- freshVariableName
    return (List (Number 0) (TypeVariable a), Map.empty)
inferValueType (Cons v w) = do
    (typ1, sub1) <- inferValueType v
    substituteInEnvironment sub1
    (typ2, sub2) <- inferValueType w
    case typ2 of
        List i typ1' -> do
            sub3 <- tryUnify typ1' (applyTypeSub sub2 typ1) $ UnexpectedType (Right w) (List i typ1) typ2
            return (List (Plus i (Number 1)) (applyTypeSub sub3 typ1), sub3 `compose` sub2 `compose` sub1)
        _ -> throwError $ UnexpectedTypeConstructor (Right w) (List (Number 0) UnitType) typ2
inferValueType (Fold id v w) = do
    (stepfuntyp, sub1) <- inferValueType v
    case stepfuntyp of
        Bang (Arrow (Tensor acctyp elemtyp) incacctyp i _) -> do
            when (id `elem` freeVariables elemtyp) $ throwError $ IndexVariableCapture v id elemtyp
            unless (checkTypeEq incacctyp (isub (Plus (IndexVariable id) (Number 1)) id acctyp)) $ throwError $ NonincreasingStepFunction v (isub (Plus (IndexVariable id) (Number 1)) id acctyp) incacctyp
            substituteInEnvironment sub1
            ((basetyp, sub2),resourceCount) <- withWireCount $ inferValueType w
            let (elemtyp', acctyp') = (applyTypeSub sub2 elemtyp, applyTypeSub sub2 acctyp)
            sub3 <- tryUnify basetyp (isub (Number 0) id acctyp) $ UnexpectedType (Right w) (isub (Number 0) id acctyp) basetyp
            let (elemtyp'',acctyp'') = (applyTypeSub sub3 elemtyp', applyTypeSub sub3 acctyp')
            id' <- freshVariableName
            let e = Max resourceCount (Maximum id (IndexVariable id') (Plus i (Mult (Minus (IndexVariable id') (Plus (IndexVariable id) (Number 1))) (wireCount elemtyp''))))
            return (Arrow (List (IndexVariable id') elemtyp'') (isub (IndexVariable id') id acctyp'') e resourceCount, sub2 `compose` sub1)
        _ -> throwError $ UnfoldableType v stepfuntyp
inferValueType (Anno v typ) = do
    (typ', sub) <- inferValueType v
    sub' <- tryUnify typ' typ $ UnexpectedType (Right v) typ typ'
    return (applyTypeSub sub' typ, sub' `compose` sub)


inferTermType :: Term -> StateT TypingEnvironment (Either TypingError) (Type, Index, TypeSubstitution)
inferTermType (Return v) = do
    ((typ, sub), i) <- withWireCount $ inferValueType v
    return (typ, i, sub)
inferTermType (App v w) = do
    (ftyp, sub1) <- inferValueType v
    case ftyp of
        Arrow intyp outtyp i _ -> do
            substituteInEnvironment sub1
            (argtyp, sub2) <- inferValueType w
            sub3 <- tryUnify intyp (applyTypeSub sub2 argtyp) $ UnexpectedType (Right w) intyp argtyp
            return (applyTypeSub sub3 outtyp, i, sub3 `compose` sub2 `compose` sub1)
        _ -> throwError $ UnexpectedTypeConstructor (Right v) (Arrow UnitType UnitType (Number 0) (Number 0)) ftyp
inferTermType (Force v) = do
    (vtyp, sub) <- inferValueType v
    case vtyp of
        Bang typ -> return (typ, Number 0, sub)
        _ -> throwError $ UnexpectedTypeConstructor (Right v) (Bang UnitType) vtyp
inferTermType (Let x m n) = do
    (ltype, i, sub1) <- inferTermType m
    substituteInEnvironment sub1
    ((rtype, j, sub2), rWireCount) <- withWireCount $ withBoundVariable x ltype $ inferTermType n
    return (rtype, Max (Plus i rWireCount) j, sub2 `compose` sub1)
inferTermType (Box inbtype v) = do
    (ftyp, sub1) <- inferValueType v
    case ftyp of
        Bang (Arrow intyp outtyp i _) -> do
            substituteInEnvironment sub1
            inbtype' <- maybe (throwError $ UnboxableType v ftyp) return (toBundleType intyp)
            unless (isBundleSubtype inbtype inbtype') $ throwError $ UnexpectedBoxingType (Box inbtype v) intyp inbtype
            outbtype <- maybe (throwError $ UnboxableType v ftyp) return (toBundleType outtyp)
            return (Circ i inbtype outbtype, Number 0, sub1)
        _ -> throwError $ UnboxableType v ftyp
inferTermType (Apply v w) = do
    (ctype, sub1) <- inferValueType v
    case ctype of
        Circ i inBtype outBtype -> do
            substituteInEnvironment sub1
            (inBtype', sub2) <- inferValueType w
            sub3 <- tryUnify inBtype' (embedBundleType inBtype) $ UnexpectedType (Right w) (embedBundleType inBtype) inBtype'
            return (embedBundleType outBtype, i, sub3 `compose` sub2 `compose` sub1)
        _ -> throwError $ UnexpectedTypeConstructor (Right v) (Circ (Number 0) Bundle.UnitType Bundle.UnitType) ctype
inferTermType (Dest x y v m) = do
    (ltyp, sub1) <- inferValueType v
    case ltyp of
        Tensor ltyp1 ltyp2 -> do
            substituteInEnvironment sub1
            (rtype, j, sub2) <- withBoundVariable x ltyp1 $ withBoundVariable y ltyp2 $ inferTermType m
            return (rtype, j, sub2 `compose` sub1)
        _ -> throwError $ UnexpectedTypeConstructor (Right v) (Tensor UnitType UnitType) ltyp


--- EXPOSED INFERENCE AND CHECKING FUNCTIONS --------------------------------------------------------------

runValueTypeInference :: TypingContext -> LabelContext -> Value -> Either TypingError Type
runValueTypeInference gamma q v = case runStateT (inferValueType v) (TypingEnvironment gamma q 0) of
    Right ((typ,_), env@TypingEnvironment{typingContext=gamma, labelContext=q}) -> do
        when (envIsLinear env) $ throwError $ UnusedLinearResources gamma q
        return typ
    Left err -> throwError err

runValueTypeChecking :: TypingContext -> LabelContext -> Value -> Type -> Either TypingError ()
runValueTypeChecking gamma q v typ = case runValueTypeInference gamma q v of
    --NOTE: for now we do not have type instantiation, so we do not try and unify the inferred type with the expected type
    Right typ' -> do
        let sub = fromMaybe Map.empty $ mgtu typ' typ
        unless (checkSubtype (applyTypeSub sub typ') typ) $ throwError $ UnexpectedType (Right v) typ typ'
    Left err -> throwError err

runTermTypeInference :: TypingContext -> LabelContext -> Term -> Either TypingError (Type, Index)
runTermTypeInference gamma q m = case runStateT (inferTermType m) (TypingEnvironment gamma q 0) of
    Right ((typ,i,_), env@TypingEnvironment{typingContext=gamma, labelContext=q}) -> do
        when (envIsLinear env) $ throwError $ UnusedLinearResources gamma q
        return (typ,i)
    Left err -> throwError err

runTermTypeChecking :: TypingContext -> LabelContext -> Term -> Type -> Index -> Either TypingError ()
runTermTypeChecking gamma q m typ i = case runTermTypeInference gamma q m of
    Right (typ',i') -> do
        let sub = fromMaybe Map.empty $ mgtu typ' typ
        unless (checkSubtype (applyTypeSub sub typ') typ) $ throwError $ UnexpectedType (Left m) typ typ'
        unless (checkLeq i' i) $ throwError $ UnexpectedWidthAnnotation m i i'
    Left err -> throwError err
