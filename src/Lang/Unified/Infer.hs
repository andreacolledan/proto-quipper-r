module Lang.Unified.Infer
  ( runTypeInference,
    runTypeInferenceWith,
    InferenceResult (..),
  )
where

import Bundle.AST (Bundle, BundleType, LabelId, Wide (wireCount), WireType (..))
import qualified Bundle.AST as Bundle
import Circuit ( Circuit, width, inferCircuitSignature )
import Index.AST
import Lang.Unified.AST
import Lang.Type.AST
import Bundle.Infer
import Control.Exception (assert)
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.State
import Data.Either.Extra (mapLeft)
import qualified Data.Map as Map
import qualified Data.Set as Set
import PrettyPrinter
import Index.Semantics

-- Corresponds to Γ in the paper
type TypingContext = Map.Map VariableId Type

emptyctx :: Map.Map a b
emptyctx = Map.empty

-- The state of a typing derivation
data TypingEnvironment = TypingEnvironment
  { typingContext :: TypingContext, -- attributes types to variable names (linear/nonlinear)
    labelContext :: LabelContext, -- attributes wire types to label names (linear)
    indexContext :: IndexContext, -- keeps track of the existing index variables in the environment
    freeVarCounter :: Int -- the counter used to initialize fresh variable names
  }

-- check if a typing environment contains any linear variable.
envIsLinear :: TypingEnvironment -> Bool
envIsLinear TypingEnvironment {typingContext = gamma, labelContext = q} = (any isLinear . Map.elems) gamma || Map.size q > 0

--- TYPING ERRORS ---------------------------------------------------------------

-- Errors that may be thrown during language-level type inference
data TypingError
  = WireTypingError WireTypingError
  | UnboundVariable VariableId
  | UnusedLinearVariable VariableId
  | ShadowedLinearVariable VariableId
  | LinearResourcesInLiftedExpression
  | UnexpectedType Expr Type Type
  | MismatchedCircuitInterface CircuitInterfaceType Circuit LabelContext Bundle
  | UnexpectedWidthAnnotation Expr Index Index
  | UnexpectedTypeConstructor Expr Type Type
  | UnusedLinearResources TypingContext LabelContext
  | UnexpectedBoxingType Expr Type BundleType
  | UnboxableType Expr Type
  | UnfoldableType Expr Type
  | NonincreasingStepFunction Expr Type Type
  | IndexVariableCapture Expr IndexVariableId Type
  | UnboundIndexVariable Type IndexVariableId
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
  show LinearResourcesInLiftedExpression = "Linear resources consumed in a lifted expression"
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
  show (UnboundIndexVariable t id) = "Unbound index variable " ++ id ++ " in type annotation " ++ pretty t

-- Shows the name of the top level constructor of a type
printConstructor :: Type -> String
printConstructor UnitType = "unit type"
printConstructor (WireType _) = "wire type"
printConstructor (Tensor _ _) = "tensor type"
printConstructor (Circ {}) = "circuit type"
printConstructor (Arrow {}) = "arrow type"
printConstructor (Bang _) = "bang type"
printConstructor (List _ _) = "list type"
printConstructor (TVar _) = "type variable"
printConstructor (TForall _ _) = "forall type"

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
labelContextLookup :: LabelId -> StateT TypingEnvironment (Either TypingError) Bundle.WireType
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

checkWellFormedness :: Type -> StateT TypingEnvironment (Either TypingError) ()
checkWellFormedness typ = do
  theta <- gets indexContext
  case ifv typ Set.\\ theta of
    fv | Set.null fv -> return () -- all the free variables in the type are also in the context, good
    fv -> throwError $ UnboundIndexVariable typ (Set.findMin fv) -- some free variables are not in scope, bad

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
  when ((any isLinear . Map.elems) gammaDiff || Map.size qDiff > 0) $ throwError LinearResourcesInLiftedExpression
  return outcome

-- tryUnify t1 t2 error runs mgtu t1 t2 in a type inference (stateful) setting
-- If gmtu returns Nothing, it throws error
tryUnify :: Type -> Type -> TypingError -> StateT TypingEnvironment (Either TypingError) TypeSubstitution
tryUnify t1 t2 err = case mgtu t1 t2 of
  Just s -> return s
  Nothing -> throwError err

--- BUNDLE CHECKING WITHIN TYPE CHECKING ------------------------------------------------------------

-- embedWireBundle b returns the PQR value equivalent to b
embedWireBundle :: Bundle -> Expr
embedWireBundle Bundle.UnitValue = EUnit
embedWireBundle (Bundle.Label id) = ELabel id
embedWireBundle (Bundle.Pair b1 b2) = EPair (embedWireBundle b1) (embedWireBundle b2)
embedWireBundle Bundle.Nil = ENil
embedWireBundle (Bundle.Cons b1 b2) = ECons (embedWireBundle b1) (embedWireBundle b2)

-- embedBundleType bt returns the PQR type equivalent to bt
embedBundleType :: BundleType -> Type
embedBundleType Bundle.UnitType = UnitType
embedBundleType (Bundle.WireType wtype) = WireType wtype
embedBundleType (Bundle.Tensor b1 b2) = Tensor (embedBundleType b1) (embedBundleType b2)
embedBundleType (Bundle.List i b) = List i (embedBundleType b)
embedBundleType (Bundle.TypeVariable id) = TVar id

--- TYPE INFERENCE ---------------------------------------------------------------

data InferenceResult = InferenceResult
  { inferredType :: Type,
    sub :: TypeSubstitution,
    index :: Index
  }

-- inferType e attempts to infer the type of expression e
-- If succesful, it returns an InferenceResult record containing
-- > the inferred type of e
-- > the substitution accumulated during inference
-- > the upper bound on the width of the circuit built by e
-- Otherwise it throws a TypingError
-- Note on variable nameing conventions:
-- > Expressions are indicated with e, e1, e2, etc.
-- > Types are indicated with typ, typ1, typ2, etc.
-- > Bundles are indicated with b, b1, b2, etc.
-- > Bundle types are indicated with bt, bt1, bt2, etc.
-- > indices are indicated with
-- >> i,i1,i2, etc. when they are effect annotations
-- >> j,j1,j2, etc. when they are type annotations
-- >> wc,wc1,wc2, etc. when they are wire counts
-- >> k,k1,k2, etc. when they are synthesized as part of the rule
inferType :: Expr -> StateT TypingEnvironment (Either TypingError) InferenceResult
inferType EUnit = return $ InferenceResult UnitType Map.empty (Number 0)
inferType (ELabel id) = do
  btype <- labelContextLookup id
  return $ InferenceResult (WireType btype) Map.empty (Number 1)
inferType (EVar id) = do
  typ <- typingContextLookup id
  return $ InferenceResult typ Map.empty (wireCount typ)
inferType (EPair e1 e2) = do
  InferenceResult typ1 sub1 i1 <- inferType e1
  substituteInEnvironment sub1
  (InferenceResult typ2 sub2 i2, wc) <- withWireCount $ inferType e2
  let typ1' = tsub sub2 typ1
  -- max(i1 + wires in e2, i2 + #(typ1'), #(typ1') + #(typ2)):
  let k = Max (Plus i1 wc) (Max (Plus i2 (wireCount typ1')) (Plus (wireCount typ1') (wireCount typ2)))
  return $ InferenceResult (Tensor typ1' typ2) (compose sub1 sub2) k
inferType ENil = do
  id <- freshTypeVariableName
  return $ InferenceResult (List (Number 0) (TVar id)) Map.empty (Number 0)
inferType (EAbs x annotyp e) = do
  checkWellFormedness annotyp
  (InferenceResult typ sub i, wc) <- withWireCount $ withBoundVariable x annotyp $ inferType e
  let annotyp' = tsub sub annotyp
  return $ InferenceResult (Arrow annotyp' typ i wc) sub wc
inferType (ELift e) = do
  InferenceResult typ sub i <- withNonLinearContext $ inferType e
  unless (checkEq i (Number 0)) $ throwError $ UnexpectedWidthAnnotation e (Number 0) i
  return $ InferenceResult (Bang typ) sub (Number 0)
inferType (ECons e1 e2) = do
  InferenceResult typ1 sub1 i1 <- inferType e1
  substituteInEnvironment sub1
  (InferenceResult typ2 sub2 i2, wc) <- withWireCount $ inferType e2
  let typ1' = tsub sub2 typ1
  case typ2 of
    List j typ3 -> do
      sub3 <- tryUnify typ1' typ3 $ UnexpectedType e2 (List j typ1') typ2
      let typ1'' = tsub sub3 typ1'
      -- max (i1 + wires in e2, i2 + #(typ1''), (j+1) * #(typ1'')):
      let k = Max (Plus i1 wc) (Max (Plus i2 (wireCount typ1'')) (Mult (Plus j (Number 1)) (wireCount typ1'')))
      return $ InferenceResult (List (Plus j (Number 1)) typ1'') (sub1 `compose` sub2 `compose` sub3) k
    _ -> throwError $ UnexpectedTypeConstructor e2 (List (Number 0) UnitType) typ2
inferType (EFold e1 e2) = do
  InferenceResult typ1 sub1 i1 <- inferType e1
  substituteInEnvironment sub1
  (InferenceResult typ2 sub2 i2, wc) <- withWireCount $ inferType e2
  let typ1' = tsub sub2 typ1
  case typ1' of
    Bang (TForall id (Arrow (Tensor acctyp elemtyp) acctyp' i j)) -> do
      undefined -- TODO
    _ -> throwError $ UnfoldableType e1 typ1'
inferType (ECirc b1 c b2) = do
  (inbt, inrem, outbt, outrem) <- lift $ mapLeft WireTypingError $ do
    (inlabels, outlabels) <- inferCircuitSignature c
    (inbt, inrem) <- runBundleTypeInferenceWithRemaining inlabels b1
    (outbt, outrem) <- runBundleTypeInferenceWithRemaining outlabels b2
    return (inbt, inrem, outbt, outrem)
  unless (null inrem) $ throwError $ MismatchedCircuitInterface Input c inrem b1
  unless (null outrem) $ throwError $ MismatchedCircuitInterface Output c outrem b2
  return $ InferenceResult (Circ (Number (width c)) inbt outbt) Map.empty (Number 0)
inferType (EApp e1 e2) = do
  -- function application
  InferenceResult typ1 sub1 i1 <- inferType e1
  substituteInEnvironment sub1
  (InferenceResult typ2 sub2 i2, wc) <- withWireCount $ inferType e2
  let typ1' = tsub sub2 typ1
  case typ1' of
    Arrow annotyp typ3 j1 j2 -> do
      sub3 <- tryUnify typ2 annotyp $ UnexpectedType e2 annotyp typ2
      -- max(i1 + wires in e2, i2 + j2, i1):
      let k = Max (Plus i1 wc) (Max (Plus i2 j2) j1)
      let typ3' = tsub sub3 typ3
      return $ InferenceResult typ3' (sub1 `compose` sub2 `compose` sub3) k
    _ -> throwError $ UnexpectedTypeConstructor e1 (Arrow UnitType UnitType (Number 0) (Number 0)) typ1'
inferType (EApply e1 e2) = do
  -- circuit application
  InferenceResult typ1 sub1 i1 <- inferType e1
  substituteInEnvironment sub1
  (InferenceResult typ2 sub2 i2, wc) <- withWireCount $ inferType e2
  let typ1' = tsub sub2 typ1
  case typ1' of
    Circ j inbt outbt -> do
      let intyp = embedBundleType inbt
      let outtyp = embedBundleType outbt
      sub3 <- tryUnify typ2 intyp $ UnexpectedType e2 (embedBundleType inbt) typ2
      let outtyp' = tsub sub3 outtyp
      -- max(i1 + wires in e2, i2, j):
      let k = Max (Plus i1 wc) (Max i2 j)
      return $ InferenceResult outtyp' (sub1 `compose` sub2 `compose` sub3) k
    _ -> throwError $ UnexpectedTypeConstructor e1 (Circ (Number 0) Bundle.UnitType Bundle.UnitType) typ1'
inferType (EBox bt e) = do
  InferenceResult typ1 sub1 i <- inferType e
  let annotyp = embedBundleType bt
  case typ1 of
    Bang (Arrow typ2 typ3 j1 _) -> do
      sub2 <- tryUnify annotyp typ2 $ UnboxableType e typ1
      let typ3' = tsub sub2 typ3
      case toBundleType typ3' of
        Just outbt -> return $ InferenceResult (Circ j1 bt outbt) (sub1 `compose` sub2) i
        _ -> throwError $ UnboxableType e typ1
    _ -> throwError $ UnboxableType e typ1
inferType (ELet x e1 e2) = do
  InferenceResult typ1 sub1 i1 <- inferType e1
  substituteInEnvironment sub1
  (InferenceResult typ2 sub2 i2, wc) <- withWireCount $ withBoundVariable x typ1 $ inferType e2
  -- max(i1 + wires in e2, i2):
  let k = Max (Plus i1 wc) i2
  return $ InferenceResult typ2 (sub1 `compose` sub2) k
inferType (EDest x y e1 e2) = do
  InferenceResult typ1 sub1 i1 <- inferType e1
  substituteInEnvironment sub1
  typ2 <- TVar <$> freshTypeVariableName
  typ3 <- TVar <$> freshTypeVariableName
  sub2 <- tryUnify typ1 (Tensor typ2 typ3) $ UnexpectedType e1 (Tensor typ2 typ3) typ1
  let typ2' = tsub sub2 typ2
  let typ3' = tsub sub2 typ3
  (InferenceResult typ5 sub3 i2, wc) <- withWireCount $ withBoundVariable x typ2' $ withBoundVariable y typ3' $ inferType e2
  let k = Max (Plus i1 wc) i2
  return $ InferenceResult typ5 (sub1 `compose` sub2 `compose` sub3) k
inferType (EAnno e annotyp) = do
  checkWellFormedness annotyp
  InferenceResult typ sub1 i <- inferType e
  sub2 <- tryUnify typ annotyp $ UnexpectedType e annotyp typ
  -- annotation type should change to the inferred type
  -- since we do not have type variables in the surface syntax, this should never happen, byt still:
  assert (tsub sub2 annotyp == annotyp) $ return ()
  return $ InferenceResult annotyp (sub1 `compose` sub2) i
inferType (EForce e) = do
  InferenceResult typ sub i <- inferType e
  case typ of
    Bang typ' -> return $ InferenceResult typ' sub i
    _ -> throwError $ UnexpectedTypeConstructor e (Bang UnitType) typ
inferType (EIAbs id e) = undefined
inferType (EIApp e i) = undefined
inferType (EConst c) =
  let typ = case c of
        QInit0 -> Circ (Number 1) Bundle.UnitType (Bundle.WireType Qubit)
        QInit1 -> Circ (Number 1) Bundle.UnitType (Bundle.WireType Qubit)
        QDiscard -> Circ (Number 1) (Bundle.WireType Qubit) Bundle.UnitType
        Meas -> Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Bit)
        Hadamard -> Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        PauliX -> Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        PauliY -> Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        PauliZ -> Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        CNot -> Circ (Number 2) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
        Toffoli -> Circ (Number 3) (Bundle.Tensor (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.WireType Qubit))
        MakeRGate -> Bang (Arrow TNat (Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Number 0) (Number 0))
        in return $ InferenceResult typ Map.empty (Number 0)

--- EXPORTED WRAPPER FUNCTIONS ---------------------------------------------------------------

runTypeInferenceWith :: TypingEnvironment -> Expr -> Either TypingError (Type, Index)
runTypeInferenceWith env e = do
  case runStateT (inferType e) env of
    Left err -> Left err
    Right (InferenceResult typ _ i, remaining) -> do
      when (envIsLinear remaining) $ throwError $ UnusedLinearResources (typingContext env) (labelContext env)
      return (typ, i)

runTypeInference :: Expr -> Either TypingError (Type, Index)
runTypeInference = runTypeInferenceWith (TypingEnvironment emptyctx Map.empty Set.empty 0)
