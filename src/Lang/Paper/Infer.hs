{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use uncurry" #-}
{-# HLINT ignore "Use record patterns" #-}
module Lang.Paper.Infer
  ( TypingContext,
    runValueTypeInference,
    runTermTypeInference,
    runValueTypeChecking,
    runTermTypeChecking,
    emptyctx,
  )
where

import Bundle.AST (Bundle, BundleType (..), LabelId, Wide (wireCount), isBundleSubtype, WireType)
import qualified Bundle.AST as Bundle
import Index.AST
import Lang.Paper.AST
import Bundle.Infer
  ( LabelContext,
    WireTypingError (..),
    runBundleTypeInferenceWithRemaining,
  )
import Circuit
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Either.Extra (mapLeft)
import qualified Data.HashMap.Strict as Map
import Data.Maybe (fromMaybe)
import PrettyPrinter
import Index.Semantics
import Lang.Type.Semantics
import Lang.Type.Unify


-- Corresponds to Γ in the paper
type TypingContext = Map.HashMap VariableId Type

-- The state of a typing derivation
data TypingEnvironment = TypingEnvironment
  { typingContext :: TypingContext, --attributes types to variable names (linear/nonlinear)
    labelContext :: LabelContext,   --attributes wire types to label names (linear)
    freeVarCounter :: Int           --the counter used to initialize fresh variable names
  }

-- check if a typing environment contains any linear variable.
envIsLinear :: TypingEnvironment -> Bool
envIsLinear TypingEnvironment {typingContext = gamma, labelContext = q} = (any isLinear . Map.elems) gamma || Map.size q > 0

emptyctx :: Map.HashMap a b
emptyctx = Map.empty


--- TYPING ERRORS ---------------------------------------------------------------

-- Errors that may be thrown during language-level type inference
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

-- Useful for error messages
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
    "Bundle "
      ++ pretty b
      ++ " is not a valid "
      ++ show interfaceType
      ++ " interface for circuit "
      ++ pretty circ
      ++ ", whose "
      ++ show interfaceType
      ++ " labels are "
      ++ pretty q
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
printConstructor TUnit = "unit type"
printConstructor (TWire {}) = "wire type"
printConstructor (TPair {}) = "TPair type"
printConstructor (TCirc {}) = "circuit type"
printConstructor (TArrow {}) = "TArrow type"
printConstructor (TBang {}) = "TBang type"
printConstructor (TList {}) = "TList type"
printConstructor (TVar {}) = "type variable"
printConstructor (TIForall {}) = "forall type"


--- TYPING ENVIRONMENT OPERATIONS ---------------------------------------------------------------

-- typingContextLookup x looks up variable x in the typing context
-- It removes it if its type is linear
-- throws UnboundVariable if the variable is absent
typingContextLookup :: VariableId -> StateT TypingEnvironment (Either TypingError) Type
typingContextLookup id = do
  env@TypingEnvironment {typingContext = gamma} <- get
  typ <- maybe (throwError $ UnboundVariable id) return (Map.lookup id gamma)
  when (isLinear typ) $ put env {typingContext = Map.delete id gamma}
  return typ

-- labelContextLookup l looks up label l in the label context and removes it
-- throws Unbound UnboundLabel if the label is absent
labelContextLookup :: LabelId -> StateT TypingEnvironment (Either TypingError) WireType
labelContextLookup id = do
  env@TypingEnvironment {labelContext = q} <- get
  outcome <- maybe (throwError $ WireTypingError $ UnboundLabel id) return (Map.lookup id q)
  put $ env {labelContext = Map.delete id q}
  return outcome

-- freshTypeVariableName returns a new fresh type variable name
freshTypeVariableName :: StateT TypingEnvironment (Either TypingError) TVarId
freshTypeVariableName = do
  env@TypingEnvironment {freeVarCounter = c} <- get
  put $ env {freeVarCounter = c + 1}
  return $ "a" ++ show c

-- freshIndexVariableName returns a new fresh index variable name
freshIndexVariableName :: StateT TypingEnvironment (Either TypingError) IndexVariableId
freshIndexVariableName = do
  env@TypingEnvironment {freeVarCounter = c} <- get
  put $ env {freeVarCounter = c + 1}
  return $ "i" ++ show c

-- substituteInEnvironment sub applies sub to the typing context 
substituteInEnvironment :: TypeSubstitution -> StateT TypingEnvironment (Either TypingError) ()
substituteInEnvironment sub = do
  env@TypingEnvironment {typingContext = gamma} <- get
  let gamma' = Map.map (tsub sub) gamma
  put env {typingContext = gamma'}


--- DERIVATION COMBINATORS ---------------------------------------------------------------

-- withBoundVariable x typ der describes derivation der
-- in which the variable name x is bound to type typ
withBoundVariable ::
  VariableId ->
  Type ->
  StateT TypingEnvironment (Either TypingError) a ->
  StateT TypingEnvironment (Either TypingError) a
withBoundVariable x typ der = do
  bindVariable x typ
  outcome <- der
  unbindVariable x -- this throws an error if x is linear and der does not consume it
  return outcome
  where
    bindVariable :: VariableId -> Type -> StateT TypingEnvironment (Either TypingError) ()
    bindVariable id typ = do
      env@TypingEnvironment {typingContext = gamma} <- get
      when (Map.member id gamma) $ throwError $ ShadowedLinearVariable id
      let gamma' = Map.insert id typ gamma
      put env {typingContext = gamma'}
    unbindVariable :: VariableId -> StateT TypingEnvironment (Either TypingError) ()
    unbindVariable id = do
      env@TypingEnvironment {typingContext = gamma} <- get
      case Map.lookup id gamma of
        Nothing -> return ()
        Just t -> do
          when (isLinear t) (throwError $ UnusedLinearVariable id)
          put env {typingContext = Map.delete id gamma}

-- withWireCount der describes derivation der
-- in which the result of the computation is paired with an index describing
-- how many wires have been consumed during der
withWireCount ::
  StateT TypingEnvironment (Either TypingError) a ->
  StateT TypingEnvironment (Either TypingError) (a, Index)
withWireCount der = do
  TypingEnvironment {typingContext = gamma, labelContext = q} <- get
  outcome <- der
  TypingEnvironment {typingContext = gamma', labelContext = q'} <- get
  -- count how many linear resources have disappeared from the contexts
  let gammaDiff = Map.difference gamma gamma'
  let qDiff = Map.difference q q'
  let resourceCount = wireCount gammaDiff `Plus` wireCount qDiff
  return (outcome, simplifyIndex resourceCount)

-- withNonLinearContext der describes a derivation like der which fails
-- if der consumes any linear resource
withNonLinearContext ::
  StateT TypingEnvironment (Either TypingError) a ->
  StateT TypingEnvironment (Either TypingError) a
withNonLinearContext der = do
  TypingEnvironment {typingContext = gamma, labelContext = q} <- get
  outcome <- der
  TypingEnvironment {typingContext = gamma', labelContext = q'} <- get
  let gammaDiff = Map.difference gamma gamma'
  let qDiff = Map.difference q q'
  when ((any isLinear . Map.elems) gammaDiff || Map.size qDiff > 0) $ throwError LinearResourcesInLiftedTerm
  return outcome

-- tryUnify t1 t2 error runs mgtu t1 t2 in a type inference (stateful) setting
-- If gmtu returns Nothing, it throws error
tryUnify :: Type -> Type -> TypingError -> StateT TypingEnvironment (Either TypingError) TypeSubstitution
tryUnify t1 t2 err = case mgtu t1 t2 of
  Just s -> return s
  Nothing -> throwError err


--- BUNDLE CHECKING WITHIN TYPE CHECKING ------------------------------------------------------------

-- embedWireBundle b returns the PQR value equivalent to b
embedWireBundle :: Bundle -> Value
embedWireBundle Bundle.UnitValue = UnitValue
embedWireBundle (Bundle.Label id) = Label id
embedWireBundle (Bundle.Pair b1 b2) = Pair (embedWireBundle b1) (embedWireBundle b2)
embedWireBundle (Bundle.Nil) = Nil
embedWireBundle (Bundle.Cons b1 b2) = Cons (embedWireBundle b1) (embedWireBundle b2)

-- embedBundleType bt returns the PQR type equivalent to bt
embedBundleType :: BundleType -> Type
embedBundleType BTUnit = TUnit
embedBundleType (BTWire wtype) = TWire wtype
embedBundleType (BTPair b1 b2) = TPair (embedBundleType b1) (embedBundleType b2)
embedBundleType (BTList i b) = TList i (embedBundleType b)
embedBundleType (BTVar id) = TVar id


--- PQR TYPE INFERENCE ---------------------------------------------------------------

-- inferValueType v describes the type inference computation on value v.
-- If succesful, it returns the type of v together with the substitution accumulated during inference
inferValueType :: Value -> StateT TypingEnvironment (Either TypingError) (Type, TypeSubstitution)
inferValueType UnitValue = return (TUnit, mempty)
inferValueType (Label id) = do
  wtype <- labelContextLookup id
  return (TWire wtype, mempty)
inferValueType (Variable id) = do
  typ <- typingContextLookup id
  return (typ, mempty)
inferValueType (Pair v w) = do
  (typ1, sub1) <- inferValueType v
  substituteInEnvironment sub1
  (typ2, sub2) <- inferValueType w
  return (TPair (tsub sub2 typ1) typ2, sub1 <> sub2)
inferValueType (BoxedCircuit inB circ outB) = lift $ do
  (inQ, outQ) <- mapLeft WireTypingError $ inferCircuitSignature circ
  (inBtype, inQ') <- mapLeft WireTypingError $ runBundleTypeInferenceWithRemaining inQ inB
  (outBtype, outQ') <- mapLeft WireTypingError $ runBundleTypeInferenceWithRemaining outQ outB
  unless (Map.null inQ') $ throwError $ MismatchedCircuitInterface Input circ inQ' inB
  unless (Map.null outQ') $ throwError $ MismatchedCircuitInterface Output circ outQ' outB
  return (TCirc (Number $ width circ) inBtype outBtype, mempty)
inferValueType (Abs x intyp m) = do
  ((outtyp, i, sub), j) <- withWireCount $ withBoundVariable x intyp $ inferTermType m
  return (TArrow (tsub sub intyp) outtyp i j, sub)
inferValueType (Lift m) = do
  (typ, i, sub) <- withNonLinearContext $ inferTermType m
  unless (checkEq undefined i (Number 0)) (throwError $ UnexpectedWidthAnnotation m (Number 0) i)
  return (TBang typ, sub)
inferValueType Nil = do
  a <- freshTypeVariableName
  return (TList (Number 0) (TVar a), mempty)
inferValueType (Cons v w) = do
  (typ1, sub1) <- inferValueType v
  substituteInEnvironment sub1
  (typ2, sub2) <- inferValueType w
  case typ2 of
    TList i typ1' -> do
      sub3 <- tryUnify typ1' (tsub sub2 typ1) $ UnexpectedType (Right w) (TList i typ1) typ2
      return (TList (Plus i (Number 1)) (tsub sub3 typ1), sub3 <> sub2 <> sub1)
    _ -> throwError $ UnexpectedTypeConstructor (Right w) (TList (Number 0) TUnit) typ2
inferValueType (Fold id v w) = do
  (stepfuntyp, sub1) <- inferValueType v
  case stepfuntyp of
    TBang (TArrow (TPair acctyp elemtyp) incacctyp i _) -> do
      when (id `elem` ifv elemtyp) $ throwError $ IndexVariableCapture v id elemtyp
      unless (checkTypeEq undefined incacctyp (isub (Plus (IndexVariable id) (Number 1)) id acctyp)) $ throwError $ NonincreasingStepFunction v (isub (Plus (IndexVariable id) (Number 1)) id acctyp) incacctyp
      substituteInEnvironment sub1
      ((basetyp, sub2), resourceCount) <- withWireCount $ inferValueType w
      let (elemtyp', acctyp') = (tsub sub2 elemtyp, tsub sub2 acctyp)
      sub3 <- tryUnify basetyp (isub (Number 0) id acctyp) $ UnexpectedType (Right w) (isub (Number 0) id acctyp) basetyp
      let (elemtyp'', acctyp'') = (tsub sub3 elemtyp', tsub sub3 acctyp')
      id' <- freshIndexVariableName
      let e = Max resourceCount (Maximum id (IndexVariable id') (Plus i (Mult (Minus (IndexVariable id') (Plus (IndexVariable id) (Number 1))) (wireCount elemtyp''))))
      return (TArrow (TList (IndexVariable id') elemtyp'') (isub (IndexVariable id') id acctyp'') e resourceCount, sub2 <> sub1)
    _ -> throwError $ UnfoldableType v stepfuntyp
inferValueType (Anno v typ) = do
  (typ', sub) <- inferValueType v
  sub' <- tryUnify typ' typ $ UnexpectedType (Right v) typ typ'
  return (tsub sub' typ, sub' <> sub)

-- inferTermType m describes the type inference computation on term m.
-- If succesful, it returns
--  - the type of m
--  - an index describing the upper bound to the width of the circuit built by m
--  - the type substitution accumulated during inference
inferTermType :: Term -> StateT TypingEnvironment (Either TypingError) (Type, Index, TypeSubstitution)
inferTermType (Return v) = do
  ((typ, sub), i) <- withWireCount $ inferValueType v
  return (typ, i, sub)
inferTermType (App v w) = do
  (ftyp, sub1) <- inferValueType v
  case ftyp of
    TArrow intyp outtyp i _ -> do
      substituteInEnvironment sub1
      (argtyp, sub2) <- inferValueType w
      sub3 <- tryUnify intyp (tsub sub2 argtyp) $ UnexpectedType (Right w) intyp argtyp
      return (tsub sub3 outtyp, i, sub3 <> sub2 <> sub1)
    _ -> throwError $ UnexpectedTypeConstructor (Right v) (TArrow TUnit TUnit (Number 0) (Number 0)) ftyp
inferTermType (Force v) = do
  (vtyp, sub) <- inferValueType v
  case vtyp of
    TBang typ -> return (typ, Number 0, sub)
    _ -> throwError $ UnexpectedTypeConstructor (Right v) (TBang TUnit) vtyp
inferTermType (Let x m n) = do
  (ltype, i, sub1) <- inferTermType m
  substituteInEnvironment sub1
  ((rtype, j, sub2), rWireCount) <- withWireCount $ withBoundVariable x ltype $ inferTermType n
  return (rtype, Max (Plus i rWireCount) j, sub2 <> sub1)
inferTermType (Box inbtype v) = do
  (ftyp, sub1) <- inferValueType v
  case ftyp of
    TBang (TArrow intyp outtyp i _) -> do
      substituteInEnvironment sub1
      inbtype' <- maybe (throwError $ UnboxableType v ftyp) return (toBundleType intyp)
      unless (isBundleSubtype inbtype inbtype') $ throwError $ UnexpectedBoxingType (Box inbtype v) intyp inbtype
      outbtype <- maybe (throwError $ UnboxableType v ftyp) return (toBundleType outtyp)
      return (TCirc i inbtype outbtype, Number 0, sub1)
    _ -> throwError $ UnboxableType v ftyp
inferTermType (Apply v w) = do
  (ctype, sub1) <- inferValueType v
  case ctype of
    TCirc i inBtype outBtype -> do
      substituteInEnvironment sub1
      (inBtype', sub2) <- inferValueType w
      sub3 <- tryUnify inBtype' (embedBundleType inBtype) $ UnexpectedType (Right w) (embedBundleType inBtype) inBtype'
      return (embedBundleType outBtype, i, sub3 <> sub2 <> sub1)
    _ -> throwError $ UnexpectedTypeConstructor (Right v) (TCirc (Number 0) BTUnit BTUnit) ctype
inferTermType (Dest x y v m) = do
  (ltyp, sub1) <- inferValueType v
  case ltyp of
    TPair ltyp1 ltyp2 -> do
      substituteInEnvironment sub1
      (rtype, j, sub2) <- withBoundVariable x ltyp1 $ withBoundVariable y ltyp2 $ inferTermType m
      return (rtype, j, sub2 <> sub1)
    _ -> throwError $ UnexpectedTypeConstructor (Right v) (TPair TUnit TUnit) ltyp



--- EXPOSED INFERENCE AND CHECKING FUNCTIONS --------------------------------------------------------------

-- runValueTypeInference gamma q v runs type inference on v using gamma and q as initial contexts
-- It additionally checks that there are no unused linear resources at the top level
runValueTypeInference :: TypingContext -> LabelContext -> Value -> Either TypingError Type
runValueTypeInference gamma q v = case runStateT (inferValueType v) (TypingEnvironment gamma q 0) of
  Right ((typ, _), env@TypingEnvironment {typingContext = gamma, labelContext = q}) -> do
    when (envIsLinear env) $ throwError $ UnusedLinearResources gamma q
    return typ
  Left err -> throwError err

-- runValueTypeChecking gamma q v typ runs type inference on v using famma and q as initial contexts
-- and checks that the result is a subtype of typ
runValueTypeChecking :: TypingContext -> LabelContext -> Value -> Type -> Either TypingError ()
runValueTypeChecking gamma q v typ = case runValueTypeInference gamma q v of
  -- NOTE: for now we do not have type instantiation, so we do not try and unify the inferred type with the expected type
  Right typ' -> do
    let sub = fromMaybe mempty $ mgtu typ' typ
    unless (checkSubtype undefined (tsub sub typ') typ) $ throwError $ UnexpectedType (Right v) typ typ'
  Left err -> throwError err

-- runTermTypeInference gamma q m runs type inference on m using gamma and q as initial contexts
-- It additionally checks that there are no unused linear resources at the top level
runTermTypeInference :: TypingContext -> LabelContext -> Term -> Either TypingError (Type, Index)
runTermTypeInference gamma q m = case runStateT (inferTermType m) (TypingEnvironment gamma q 0) of
  Right ((typ, i, _), env@TypingEnvironment {typingContext = gamma, labelContext = q}) -> do
    when (envIsLinear env) $ throwError $ UnusedLinearResources gamma q
    return (typ, i)
  Left err -> throwError err

-- runTermTypeChecking gamma q m typ i runs type inference on m using famma and q as initial contexts
-- and checks that the resulting type is a subtype of typ and that the resulting index is lesser or equal than i
runTermTypeChecking :: TypingContext -> LabelContext -> Term -> Type -> Index -> Either TypingError ()
runTermTypeChecking gamma q m typ i = case runTermTypeInference gamma q m of
  Right (typ', i') -> do
    let sub = fromMaybe mempty $ mgtu typ' typ
    unless (checkSubtype undefined (tsub sub typ') typ) $ throwError $ UnexpectedType (Left m) typ typ'
    unless (checkLeq undefined i' i) $ throwError $ UnexpectedWidthAnnotation m i i'
  Left err -> throwError err
