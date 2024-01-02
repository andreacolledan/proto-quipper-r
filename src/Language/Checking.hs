{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Language.Checking(
    checkValueType,
    synthesizeValueType,
    synthesizeTermType,
    checkTermType,
    TypingContext,
    TypingEnvironment(..),
    typingContextLookup,
    bindVariable,
    embedWireBundle,
    embedBundleType,
    embedBundleDerivation,
    containsLinearResources
) where
import Circuit.Checking
import Circuit.Syntax
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Map (Map)
import Index
import Language.Syntax
import PrettyPrinter
import qualified Data.Map as Map
import WireBundle.Checking
import WireBundle.Syntax (Bundle, BundleType, Wide (wireCount))
import qualified WireBundle.Syntax as Bundle
import Control.Monad

-- Corresponds to Γ in the paper
type TypingContext = Map VariableId Type

data TypingEnvironment = TypingEnvironment {
    indexContext :: IndexContext,
    typingContext :: TypingContext,
    labelContext :: LabelContext,
    consumedResources :: Int
}

-- check if a typing context contains any linear variable. Corresponds to Γ being written Φ in the paper
containsLinearResources :: TypingEnvironment -> Bool
containsLinearResources TypingEnvironment{typingContext = gamma, labelContext = q} = (any isLinear . Map.elems) gamma || Map.size q > 0

-- lookup a variable in the typing context, remove it if it is linear
typingContextLookup :: VariableId -> StateT TypingEnvironment (Either String) Type
typingContextLookup id = do
    env@TypingEnvironment{typingContext = gamma, consumedResources = cs} <- get
    outcome <- maybe (throwError $ "Unbound variable " ++ id) return (Map.lookup id gamma)
    when (isLinear outcome) $ put env{typingContext = Map.delete id gamma, consumedResources = cs + 1}
    return outcome

-- add a new binding to the typing context, fail if the variable is already bound
bindVariable :: VariableId -> Type -> StateT TypingEnvironment (Either String) ()
bindVariable id typ = do
    env@TypingEnvironment{typingContext = gamma} <- get
    when (Map.member id gamma) $ throwError $ "Cannot shadow existing variable " ++ id
    let gamma' = Map.insert id typ gamma
    put env{typingContext = gamma'}

-- remove a binding from the typing context, fail if the variable is linear
unbindVariable :: VariableId -> StateT TypingEnvironment (Either String) ()
unbindVariable id = do
    TypingEnvironment{typingContext = gamma} <- get
    case Map.lookup id gamma of
        Nothing -> return ()
        Just t -> when (isLinear t) (throwError $ "Cannot unbind linear variable " ++ id)

-- locally bind a variable in the typing context of an existing derivation
withBoundVariable :: VariableId -> Type -> StateT TypingEnvironment (Either String) a -> StateT TypingEnvironment (Either String) a
withBoundVariable x typ der = do
    bindVariable x typ
    outcome <- der
    unbindVariable x
    return outcome

-- make it so an existing derivation fails if it consumes any linear resources
withNonLinearContext :: StateT TypingEnvironment (Either String) a -> StateT TypingEnvironment (Either String) a
withNonLinearContext der = do
    TypingEnvironment{consumedResources = before} <- get
    outcome <- der
    TypingEnvironment{consumedResources = after} <- get
    when (after > before) (throwError "Linear resources consumed in a lifted term")
    return outcome

-- make it so an existing derivation also returns the amount of linear resources it makes use of
withResourceCount :: StateT TypingEnvironment (Either String) a -> StateT TypingEnvironment (Either String) (a, Int)
withResourceCount der = do
    TypingEnvironment{consumedResources = before} <- get
    outcome <- der
    TypingEnvironment{consumedResources = after} <- get
    return (outcome, after - before)

-- return the number of wires in the typing context, corresponds to #(Γ) in the paper
contextWireCount :: StateT TypingEnvironment (Either String) Index
contextWireCount = do
    TypingEnvironment{typingContext = gamma, labelContext = q} <- get
    return $ Plus (wireCount gamma) (wireCount q)


-- Turns a wire bundle into an equivalent language-level value
embedWireBundle :: Bundle -> Value
embedWireBundle Bundle.UnitValue = UnitValue
embedWireBundle (Bundle.Label id) = Label id
embedWireBundle (Bundle.Pair b1 b2) = Pair (embedWireBundle b1) (embedWireBundle b2)

-- Turns a wire bundle type into an equivalent language-level type
embedBundleType :: BundleType -> Type
embedBundleType Bundle.UnitType = UnitType
embedBundleType (Bundle.WireType wtype) = WireType wtype
embedBundleType (Bundle.Tensor b1 b2) = Tensor (embedBundleType b1) (embedBundleType b2)

-- turns a bundle type derivation (which only has a label context)
-- into a typing derivation that does not use the index or typing context
embedBundleDerivation :: StateT LabelContext (Either String) a
                        -> StateT TypingEnvironment (Either String) a
embedBundleDerivation der = do
    env@TypingEnvironment{labelContext = q, consumedResources = cs} <- get
    case runStateT der q of
        Left err -> throwError err
        Right (x,q') -> let usedLabels = Map.size q - Map.size q'
            in put env{labelContext=q', consumedResources = cs + usedLabels} >> return x

-- Θ;Γ;Q ⊢ V <= A (Fig. 12)
-- returns True iff there are linear resources left in the typing contexts
checkValueType :: Value -> Type -> StateT TypingEnvironment (Either String) ()
checkValueType UnitValue typ = case typ of
    UnitType -> return ()
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to unit value '*'"
checkValueType (Label id) typ = case typ of
    WireType wtype -> do
        wtype' <- embedBundleDerivation $ labelContextLookup id
        when (wtype /= wtype') $ throwError $ "Label " ++ id ++ "has type " ++ pretty wtype' ++ " but is required to have type " ++ pretty wtype
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to label " ++ id
checkValueType (Variable id) typ = do
    typ' <- typingContextLookup id
    when (typ /= typ') $ throwError $ "Variable " ++ id ++ " has type " ++ pretty typ' ++ " but is required to have type " ++ pretty typ
checkValueType (Pair v w) typ = case typ of
    Tensor typ1 typ2 -> do
        _ <- checkValueType v typ1
        checkValueType w typ2
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to pair " ++ pretty (Pair v w)
checkValueType (BoxedCircuit inB circ outB) typ = case typ of
    Circ i inBtype outBtype -> if Number (width circ) <= i
        then lift $ do
            (inQ, outQ) <- inferCircuitSignature circ
            inputCheck <- evalStateT (checkBundleType inB inBtype) inQ
            outputCheck <- evalStateT (checkBundleType outB outBtype) outQ
            when inputCheck  $ throwError $ "Input bundle " ++ pretty inB ++ " does not represent all of the circuits input wires"
            when outputCheck $ throwError $ "Output bundle " ++ pretty outB ++ " does not represent all of the circuits output wires"
        else throwError $ "Cannot conclude width (" ++ pretty circ ++ ") <= " ++ pretty i
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to a boxed circuit"
checkValueType (Abs x intyp m) typ = case typ of
    Arrow intyp' outtyp i j | intyp' == intyp -> do
        wireCountAnnotation <- contextWireCount
        when (j /= wireCountAnnotation) (throwError $ "Function captures " ++ pretty wireCountAnnotation ++ " wires but is required to capture " ++ pretty j)
        withBoundVariable x intyp $ checkTermType m outtyp i
    Arrow inTyp' _ _ _ -> throwError $ "Abstracted variable " ++ x ++ " is annotated with type " ++ pretty intyp ++ " but is required to have type " ++ pretty inTyp'
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to a function"
checkValueType (Lift m) typ = case typ of
    Bang typ' -> do
        withNonLinearContext $ checkTermType m typ' (Number 0)
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to a lifted term"


-- Θ;Γ;Q ⊢ M <= A ; I (Fig. 12)
-- returns True iff there are linear resources left in the typing contexts
checkTermType :: Term -> Type -> Index -> StateT TypingEnvironment (Either String) ()
checkTermType (Apply v w) typ i = do
        ctype <- synthesizeValueType v
        case ctype of
            Circ i' inBtype outBtype -> do
                inputCheck <- checkValueType w (embedBundleType inBtype)
                when (embedBundleType outBtype /= typ) (throwError $
                    "Term " ++ pretty (Apply v w) ++ " has type " ++ pretty outBtype ++ " but is required to have type " ++ pretty typ)
                when (i < i') (throwError $ "Circuit has width " ++ pretty i' ++ " but is required to have width at most " ++ pretty i)
                return inputCheck
            _ -> throwError $ "First argument of apply: " ++ pretty v ++ " is supposed to be a circuit, instead has type " ++ pretty ctype
checkTermType (Dest x y v m) typ i = do
        ltyp <- synthesizeValueType v
        case ltyp of
            Tensor ltyp1 ltyp2 -> do
                withBoundVariable x ltyp1 $ withBoundVariable y ltyp2 $ checkTermType m typ i
            _ -> throwError $ "Left hand side of destructuring let: " ++ pretty v ++ " is supposed to have tensor type, instead has type " ++ pretty ltyp
checkTermType (Return v) typ i = do
        (vtyp,resourceCount) <- withResourceCount $ synthesizeValueType v
        when (vtyp /= typ) (throwError $ "Return value " ++ pretty v ++ " has type " ++ pretty vtyp ++ " but is required to have type " ++ pretty typ)
        when (i /= Number resourceCount) (throwError $ "Return value has width " ++ pretty resourceCount ++ " but is required to have width " ++ pretty i)
checkTermType (App v w) typ i = do
        ftyp <- synthesizeValueType v
        case ftyp of
            Arrow intyp outtyp i' j -> do
                argcheck <- checkValueType w intyp
                when (outtyp /= typ) (throwError $ "Term " ++ pretty (App v w) ++ " has type " ++ pretty outtyp ++ " but is required to have type " ++ pretty typ)
                when (i < i') (throwError $ "Function produces a circuit of width " ++ pretty i' ++ " but is required to produce a circuit of width at most " ++ pretty i)
                return argcheck
            _ -> throwError $ "First argument of apply: " ++ pretty v ++ " is supposed to be a function, instead has type " ++ pretty ftyp
checkTermType (Force v) typ i = do
        when (i /= Number 0) (throwError $ "Forced term cannot produce a circuit of width " ++ pretty i)
        --the check for the context to be non-linear is pushed down into the type check for the bang-typed value
        checkValueType v (Bang typ)



-- Θ;Γ;Q ⊢ V => A (Fig. 12)
synthesizeValueType :: Value -> StateT TypingEnvironment (Either String) Type
synthesizeValueType UnitValue = return UnitType
synthesizeValueType (Label id) = do
    wtype <- embedBundleDerivation $ labelContextLookup id
    return $ WireType wtype
synthesizeValueType (Variable id) = typingContextLookup id
synthesizeValueType (Pair v w) = do
    typ1 <- synthesizeValueType v
    typ2 <- synthesizeValueType w
    return $ Tensor typ1 typ2
synthesizeValueType (BoxedCircuit inB circ outB) = lift $ do
        (inQ, outQ) <- inferCircuitSignature circ
        (inBtype, inQ') <- runStateT (synthesizeBundleType inB) inQ
        (outBtype, outQ') <- runStateT (synthesizeBundleType outB) outQ
        unless (Map.null inQ') $ throwError $ "Input bundle " ++ pretty inB ++ " does not represent all of the circuits input wires"
        unless (Map.null outQ') $ throwError $ "Output bundle " ++ pretty outB ++ " does not represent all of the circuits output wires"
        return $ Circ (Number $ width circ) inBtype outBtype
synthesizeValueType (Abs x intyp m) = do
    j <- contextWireCount
    (outtyp, i) <- withBoundVariable x intyp $ synthesizeTermType m
    return $ Arrow intyp outtyp i j
synthesizeValueType (Lift m) = do
    (typ, i) <- withNonLinearContext $ synthesizeTermType m
    when (i /= Number 0) (throwError $ "Lifted term produces a circuit of width " ++ pretty i ++ " but is required to produce a circuit of width 0")
    return $ Bang typ

-- Θ;Γ;Q ⊢ M => A ; I (Fig. 12)
synthesizeTermType :: Term -> StateT TypingEnvironment (Either String) (Type, Index)
synthesizeTermType (Apply v w) = do
    ctype <- synthesizeValueType v
    case ctype of
        Circ i inBtype outBtype -> do
            _ <- checkValueType w (embedBundleType inBtype)
            return (embedBundleType outBtype, i)
        _ -> throwError $ "First argument of apply: " ++ pretty v ++ " is supposed to be a circuit, instead has type " ++ pretty ctype
synthesizeTermType (Dest x y v m) = do
    ltyp <- synthesizeValueType v
    case ltyp of
        Tensor ltyp1 ltyp2 -> do
            withBoundVariable x ltyp1 $ withBoundVariable y ltyp2 $ synthesizeTermType m
        _ -> throwError $ "Left hand side of destructuring let: " ++ pretty v ++ " is supposed to have tensor type, instead has type " ++ pretty ltyp
synthesizeTermType (Return v) = do
    (vtyp, resourceCount) <- withResourceCount $ synthesizeValueType v
    return (vtyp, Number resourceCount)
synthesizeTermType (App v w) = do
    ftyp <- synthesizeValueType v
    case ftyp of
        Arrow intyp outtyp i _ -> do
            _ <- checkValueType w intyp
            return (outtyp, i)
        _ -> throwError $ "First argument of apply: " ++ pretty v ++ " is supposed to be a function, instead has type " ++ pretty ftyp
synthesizeTermType (Force v) = do
    --the check for the context to be non-linear is pushed down into the type synthesis for the bang-typed value
    vtyp <- synthesizeValueType v
    case vtyp of
        Bang typ -> return (typ, Number 0)
        _ -> throwError $ "Cannot force a value of type " ++ pretty vtyp