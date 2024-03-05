{-# LANGUAGE LambdaCase #-}
module Lang.Unified.Infer
  ( runTypeInference,
    runTypeInferenceWith,
    InferenceResult (..),
    makeEnv,
    makeEnvForall,
    emptyEnv,
    emptyctx,
    TypingError,
  )
where

import Bundle.AST hiding (compose)
import qualified Bundle.AST as Bundle
import Bundle.Infer
import Circuit (Circuit, inferCircuitSignature, width)
import Control.Exception (assert)
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.State
import Data.Either.Extra (mapLeft)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Index.AST
import Index.Semantics
import Lang.Type.AST
import Lang.Unified.AST
import PrettyPrinter
import Lang.Type.Semantics (simplifyType, checkSubtype)
import Data.List (intercalate)

-- The datatype of bindings (carries the type of a variable and whether it has been used yet)
data Binding = Binding {getType :: Type, isUsed :: Bool} deriving (Eq, Show)

instance Wide Binding where
  wireCount binding = if isUsed binding then Number 0 else wireCount (getType binding)

instance Pretty Binding where
  pretty = pretty . getType

canBeUsed :: Binding -> Bool
canBeUsed (Binding typ used) = not used || not (isLinear typ)

mustBeUsed :: Binding -> Bool
mustBeUsed (Binding typ used) = isLinear typ && not used

-- The datatype of typing contexts
-- Corresponds to Γ in the paper
type TypingContext = Map.Map VariableId [Binding]

emptyctx :: Map.Map a b
emptyctx = Map.empty

-- The state of a typing derivation
data TypingEnvironment = TypingEnvironment
  { typingContext :: TypingContext, -- attributes types to variable names (linear/nonlinear)
    labelContext :: LabelContext, -- attributes wire types to label names (linear)
    indexContext :: IndexContext, -- keeps track of the existing index variables in the environment
    freeVarCounter :: Int -- the counter used to initialize fresh variable names
  }

instance Wide TypingEnvironment where
  wireCount TypingEnvironment {typingContext = gamma, labelContext = q} = wireCount gamma `Plus` wireCount q

emptyEnv :: TypingEnvironment
emptyEnv = TypingEnvironment emptyctx emptyctx emptyictx 0

makeEnvForall :: [IndexVariableId] -> [(VariableId, Type)] -> [(LabelId, WireType)] -> TypingEnvironment
makeEnvForall theta gamma q = let gamma' = Map.fromList [(id, [Binding typ False]) | (id, typ) <- gamma]
  in TypingEnvironment gamma' (Map.fromList q) (Set.fromList theta) 0

makeEnv :: [(VariableId, Type)] -> [(LabelId, WireType)] -> TypingEnvironment
makeEnv = makeEnvForall []

-- check if a typing environment contains any linear variable.
envIsLinear :: TypingEnvironment -> Bool
envIsLinear TypingEnvironment {typingContext = gamma, labelContext = q} =
  let remainingVars = [id | (id,bs) <- Map.toList gamma, any mustBeUsed bs] --remaining linear variables
  in not (null remainingVars) || not (Map.null q)

--- TYPING ERRORS ---------------------------------------------------------------

-- Errors that may be thrown during language-level type inference
data TypingError
  = WireTypingError WireTypingError
  | UnboundVariable VariableId
  | UnusedLinearVariable VariableId
  | ShadowedLinearVariable VariableId
  | LinearResourcesInLiftedExpression
  | UnexpectedType Expr Type Type
  | MismatchedInputInterface Circuit LabelContext Bundle
  | MismatchedOutputInterface Circuit LabelContext Bundle
  | UnexpectedWidthAnnotation Expr Index Index
  | UnexpectedTypeConstructor Expr Type Type
  | UnusedLinearResources TypingContext LabelContext
  | UnexpectedBoxingType Expr Type BundleType
  | UnboxableType Expr Type
  | UnfoldableStepfunction Expr Type
  | UnfoldableAccumulator Expr Type
  | UnfoldableArg Expr Type
  | NonincreasingStepFunction Expr Type Type
  | IndexVariableCapture Expr IndexVariableId Type
  | UnboundIndexVariable Type IndexVariableId
  | ShadowedIndexVariable IndexVariableId
  | OverusedLinearVariable VariableId
  | UnexpectedEmptyList Expr Type
  deriving (Eq)

instance Show TypingError where
  show (WireTypingError err) = show err
  show (UnboundVariable id) = "Unbound variable " ++ id
  show (UnusedLinearVariable id) = "Unused linear variable " ++ id
  show (ShadowedLinearVariable id) = "Shadowed linear variable " ++ id
  show LinearResourcesInLiftedExpression = "Linear resources consumed in a lifted expression"
  show (UnexpectedType exp typ1 typ2) =
    "Expected expression " ++ pretty exp ++ " to have type " ++ pretty (simplifyType typ1) ++ ", got " ++ pretty (simplifyType typ2) ++ " instead"
  show (MismatchedInputInterface c q b) = "Bundle " ++ pretty b ++ " is not a valid input interface for TCircuit " ++ pretty c ++ ", whose input labels are " ++ pretty q
  show (MismatchedOutputInterface c q b) = "Bundle " ++ pretty b ++ " is not a valid output interface for TCircuit " ++ pretty c ++ ", whose output labels are " ++ pretty q
  show (UnexpectedWidthAnnotation m i j) =
    "Expected term " ++ pretty m ++ " to have width annotation " ++ pretty i ++ ", got " ++ pretty j ++ " instead"
  show (UnexpectedTypeConstructor exp typ1 typ2) =
    "Expected expression " ++ pretty exp ++ " to have " ++ printConstructor (simplifyType typ1) ++ ", got type " ++ pretty (simplifyType typ2) ++ " instead"
  show (UnusedLinearResources gamma q) = "Unused linear resources in typing contexts: " ++ intercalate ", " (map pretty (join $ Map.elems gamma)) ++ " ; " ++ pretty q
  show (UnexpectedBoxingType m btype1 btype2) =
    "Expected input type of boxed TCircuit " ++ pretty m ++ " to be " ++ pretty btype1 ++ ", got " ++ pretty btype2 ++ " instead"
  show (UnboxableType v typ) = "Cannot box value " ++ pretty v ++ " of type " ++ pretty (simplifyType typ)
  show (UnfoldableStepfunction v typ) = "Expression " ++ pretty v ++ " of type " ++ pretty (simplifyType typ) ++ " is not a valid step function"
  show (UnfoldableAccumulator v typ) = "Expression " ++ pretty v ++ " of type " ++ pretty (simplifyType typ) ++ " is not a valid accumulator"
  show (UnfoldableArg v typ) = "Expression " ++ pretty v ++ " of type " ++ pretty typ ++ " is not a valid fold argument"
  show (NonincreasingStepFunction v typ1 typ2) =
    "Expected step function " ++ pretty v ++ "'s output type to be" ++ pretty (simplifyType typ1) ++ ", got " ++ pretty (simplifyType typ2) ++ " instead"
  show (IndexVariableCapture v id typ) = "Index variable " ++ id ++ " cannot occur in type " ++ pretty (simplifyType typ) ++ " of step function " ++ pretty v
  show (UnboundIndexVariable t id) = "Unbound index variable " ++ id ++ " in type annotation " ++ pretty (simplifyType t)
  show (ShadowedIndexVariable id) = "Shadowed index variable " ++ id
  show (OverusedLinearVariable id) = "Linear variable " ++ id ++ " is used more than once"
  show (UnexpectedEmptyList e t) = "Cannot conclude that expression " ++ pretty e ++ " of type " ++ pretty (simplifyType t) ++ " is a non-empty list"

-- Shows the name of the top level constructor of a type
printConstructor :: Type -> String
printConstructor TUnit = "unit type"
printConstructor (TWire {}) = "wire type"
printConstructor (TPair {}) = "tensor type"
printConstructor (TCirc {}) = "circuit type"
printConstructor (TArrow {}) = "arrow type"
printConstructor (TBang {}) = "bang type"
printConstructor (TList {}) = "list type"
printConstructor (TVar {}) = "type variable"
printConstructor (TIForall {}) = "forall type"

--- TYPING ENVIRONMENT OPERATIONS ---------------------------------------------------------------

-- typingContextLookup x looks up variable x in the typing context
-- It removes it if its type is linear
-- throws UnboundVariable if the variable is absent
typingContextLookup :: VariableId -> StateT TypingEnvironment (Either TypingError) Type
typingContextLookup id = do
  env@TypingEnvironment {typingContext = gamma} <- get
  bindings <- maybe (throwError $ UnboundVariable id) return (Map.lookup id gamma)
  case bindings of
    (b:bs) -> if canBeUsed b
      then do
        put env {typingContext = Map.insert id (Binding (getType b) True : bs) gamma}
        return $ getType b
      else throwError $ OverusedLinearVariable id
    [] -> error "Internal error: empty binding list"
      

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
  let gamma' = Map.map (map (\(Binding t u) -> Binding (tsub sub t) u)) gamma
  put env {typingContext = gamma'}

--TODO: factor these two together

checkTypeWellFormedness :: Type -> StateT TypingEnvironment (Either TypingError) ()
checkTypeWellFormedness typ = do
  theta <- gets indexContext
  case ifv typ Set.\\ theta of
    fv | Set.null fv -> return () -- all the free variables in the type are also in the context, good
    fv -> throwError $ UnboundIndexVariable typ (Set.findMin fv) -- some free variables are not in scope, bad

checkIndexWellFormedness :: Index -> StateT TypingEnvironment (Either TypingError) ()
checkIndexWellFormedness i = do
  theta <- gets indexContext
  case ifv i Set.\\ theta of
    fv | Set.null fv -> return () -- all the free variables in the index are also in the context, good
    fv -> throwError $ UnboundIndexVariable (TVar "i") (Set.findMin fv) -- some free variables are not in scope, bad

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
      bs <- maybe (return []) return (Map.lookup id gamma)
      let gamma' = Map.insert id (Binding typ False : bs) gamma
      put env {typingContext = gamma'}
    unbindVariable :: VariableId -> StateT TypingEnvironment (Either TypingError) ()
    unbindVariable id = do
      env@TypingEnvironment {typingContext = gamma} <- get
      case Map.lookup id gamma of
        Nothing -> error "Internal error: tried to unbind non-existing variable"
        Just [] -> error "Internal error: tried to unbind variable with empty binding list"
        Just (b:bs) -> do
          when (mustBeUsed b) (throwError $ UnusedLinearVariable id)
          put env {typingContext = if null bs then Map.delete id gamma else Map.insert id bs gamma}

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
  let gammaDiff = diffcount gamma gamma'
  let qDiff = wireCount $ Map.difference q q'
  let resourceCount = gammaDiff `Plus` qDiff
  return (outcome, simplifyIndex resourceCount)
  where
    diffcount :: TypingContext -> TypingContext -> Index
    diffcount gamma1 gamma2 = wireCount $ Map.elems $ Map.differenceWith (\bs1 bs2 -> case (bs1,bs2) of
              -- it was an available linear resource in gamma1 and it is a used linear resource in gamma2:
              (b1:_,b2:_) -> if canBeUsed b1 && not (canBeUsed b2) then Just [b1] else Nothing
              (_,_) -> error "Internal error: empty binding list") gamma1 gamma2

-- withNonLinearContext der describes a derivation like der which fails
-- if der consumes any linear resource
withNonLinearContext ::
  StateT TypingEnvironment (Either TypingError) a ->
  StateT TypingEnvironment (Either TypingError) a
withNonLinearContext der = do
  TypingEnvironment {typingContext = gamma, labelContext = q} <- get
  outcome <- der
  TypingEnvironment {typingContext = gamma', labelContext = q'} <- get
  let gammaconsumed = linearconsumed gamma gamma'
  let qconsumed =  Map.difference q q'
  unless (Map.null gammaconsumed && Map.null qconsumed) $ throwError LinearResourcesInLiftedExpression
  return outcome
  where
    linearconsumed :: TypingContext -> TypingContext -> TypingContext
    linearconsumed = Map.differenceWith (\bs1 bs2 -> case (bs1,bs2) of
      -- it was an available linear resource in gamma1 and it is a used linear resource in gamma2:
      (b1:_,b2:_) -> if mustBeUsed b1 && not (canBeUsed b2) then Just [b1] else Nothing
      (_,_) -> error "Internal error: empty binding list")


-- tryUnify t1 t2 error runs mgtu t1 t2 in a type inference (stateful) setting
-- If gmtu returns Nothing, it throws error
tryUnify :: Type -> Type -> TypingError -> StateT TypingEnvironment (Either TypingError) TypeSubstitution
tryUnify t1 t2 err = case mgtu t1 t2 of
  Just s -> return s
  Nothing -> throwError err

withBoundIndexVariable :: IndexVariableId -> StateT TypingEnvironment (Either TypingError) a -> StateT TypingEnvironment (Either TypingError) a
withBoundIndexVariable id der = do
  env@TypingEnvironment {indexContext = theta} <- get
  when (Set.member id theta) $ throwError $ ShadowedIndexVariable id
  put env {indexContext = Set.insert id theta}
  outcome <- der
  env@TypingEnvironment {indexContext = theta} <- get
  put env {indexContext = Set.delete id theta}
  return outcome

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
embedBundleType BTUnit = TUnit
embedBundleType (BTWire wtype) = TWire wtype
embedBundleType (BTPair b1 b2) = TPair (embedBundleType b1) (embedBundleType b2)
embedBundleType (BTList i b) = TList i (embedBundleType b)
embedBundleType (BTVar id) = TVar id

--- TYPE INFERENCE ---------------------------------------------------------------

data InferenceResult = InferenceResult
  { inferredType :: Type,
    index :: Index
  }

-- inferType e attempts to infer the type of expression e
-- If succesful, it returns an InferenceResult record containing
-- > the inferred type of e
-- > the substitution accumulated during inference
-- > the upper bound on the width of the TCircuit built by e
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
-- >> g,g1,g2, etc. when they are used as terms (e.g. in index application)
inferType :: Expr -> StateT TypingEnvironment (Either TypingError) InferenceResult
-- UNIT
inferType EUnit = return $ InferenceResult TUnit (Number 0)
-- LABEL
inferType (ELabel id) = do
  btype <- labelContextLookup id
  return $ InferenceResult (TWire btype) (Number 1)
-- VARIABLE
inferType (EVar id) = do
  typ <- typingContextLookup id
  return $ InferenceResult typ (wireCount typ)
-- PAIR
inferType (EPair e1 e2) = do
  InferenceResult typ1 i1 <- inferType e1
  (InferenceResult typ2 i2, wc) <- withWireCount $ inferType e2
  -- max(i1 + wires in e2, i2 + #(typ1), #(typ1) + #(typ2)):
  let k = Max (Plus i1 wc) (Max (Plus i2 (wireCount typ1)) (Plus (wireCount typ1) (wireCount typ2)))
  return $ InferenceResult (TPair typ1 typ2) k
-- NIL
inferType ENil = return $ InferenceResult (TList (Number 0) TUnit) (Number 0)
-- ABSTRACTION
inferType (EAbs x annotyp e) = do
  checkTypeWellFormedness annotyp
  (InferenceResult typ i, wc) <- withWireCount $ withBoundVariable x annotyp $ inferType e
  return $ InferenceResult (TArrow annotyp typ i wc) wc
-- LIFT
inferType (ELift e) = do
  InferenceResult typ i <- withNonLinearContext $ inferType e
  unless (checkEq i (Number 0)) $ throwError $ UnexpectedWidthAnnotation e (Number 0) i
  return $ InferenceResult (TBang typ) (Number 0)
-- CONS
inferType (ECons e1 e2) = do
  InferenceResult typ1 i1 <- inferType e1
  (InferenceResult typ2 i2, wc) <- withWireCount $ inferType e2
  case typ2 of
    TList j typ1' -> do
      unless (checkSubtype (TList j typ1') (TList j typ1)) $ throwError $ UnexpectedType e2 (TList j typ1) typ2
      -- max (i1 + wires in e2, i2 + #(typ1), (j+1) * #(typ1)):
      let k = Max (Plus i1 wc) (Max (Plus i2 (wireCount typ1)) (Mult (Plus j (Number 1)) (wireCount typ1)))
      return $ InferenceResult (TList (Plus j (Number 1)) typ1) k
    _ -> throwError $ UnexpectedTypeConstructor e2 (TList (Number 0) TUnit) typ2
-- FOLD
inferType (EFold e1 e2 e3) = do --naming conventions are not satisfied here because the rule is HARD to parse
  InferenceResult steptyp i1 <- inferType e1
  case steptyp of
    TBang (TIForall id (TArrow (TPair acctyp elemtyp) acctyp' stepwidth o1) o2 o3) | checkEq o1 (Number 0) && checkEq o2 (Number 0) && checkEq o3 (Number 0) -> do
      unless (checkSubtype acctyp' (isub (Plus (IndexVariable id) (Number 1)) id acctyp)) $  throwError $ UnfoldableStepfunction e1 steptyp
      (InferenceResult acctyp'' i2, wc1) <-withWireCount $ inferType e2
      unless (checkSubtype acctyp'' (isub (Number 0) id acctyp)) $ throwError $ UnfoldableAccumulator e2 acctyp''
      (InferenceResult argtyp i3, wc2) <- withWireCount $ inferType e3
      case argtyp of
        TList arglen elemtyp' -> do
          unless (checkSubtype elemtyp' elemtyp) $ throwError $ UnfoldableArg e3 argtyp
          -- width upper bound of ONLY fold execution: max(#(acctyp{0/i},maximum[i<arglen] stepwidth + (arglen-(i+1))*#(elemtyp)))
          let k1 = Max (wireCount (isub (Number 0) id acctyp)) (Maximum id arglen (Plus stepwidth (Mult (Minus arglen (Plus (IndexVariable id) (Number 1))) (wireCount elemtyp))))
          -- the total upper bound takes into consideration the evaluation of e1, e2, e3 and the fold execution
          -- max(i1 + wires in e2 and e3, i2 + wires in e3, i3 + wires in the result of e2, k1):
          let k2 = Max (Plus i1 (Plus wc1 wc2)) (Max (Plus i2 wc2) (Max (Plus i3 (wireCount (isub (Number 0) id acctyp))) k1))
          return $ InferenceResult (isub arglen id acctyp) k2
        _ -> throwError $ UnfoldableArg e3 argtyp
    _ -> throwError $ UnfoldableStepfunction e1 steptyp
-- BOXED CIRCUIT
inferType (ECirc b1 c b2) = do
  (inbt, inrem, outbt, outrem) <- lift $ mapLeft WireTypingError $ do
    (inlabels, outlabels) <- inferCircuitSignature c
    (inbt, inrem) <- runBundleTypeInferenceWithRemaining inlabels b1
    (outbt, outrem) <- runBundleTypeInferenceWithRemaining outlabels b2
    return (inbt, inrem, outbt, outrem)
  unless (null inrem) $ throwError $ MismatchedInputInterface c inrem b1
  unless (null outrem) $ throwError $ MismatchedOutputInterface c outrem b2
  return $ InferenceResult (TCirc (Number (width c)) inbt outbt) (Number 0)
-- APPLICATION
inferType (EApp e1 e2) = do
  -- function application
  InferenceResult typ1 i1 <- inferType e1
  (InferenceResult typ2 i2, wc) <- withWireCount $ inferType e2
  case typ1 of
    TArrow annotyp typ3 j1 j2 -> do
      unless (checkSubtype typ2 annotyp) $ throwError $ UnexpectedType e2 annotyp typ2
      -- max(i1 + wires in e2, i2 + j2, j1):
      let k = Max (Plus i1 wc) (Max (Plus i2 j2) j1)
      return $ InferenceResult typ3 k
    _ -> throwError $ UnexpectedTypeConstructor e1 (TArrow TUnit TUnit (Number 0) (Number 0)) typ1
-- APPLY (Circuit application)
inferType (EApply e1 e2) = do
  InferenceResult typ1 i1 <- inferType e1
  (InferenceResult typ2 i2, wc) <- withWireCount $ inferType e2
  case typ1 of
    TCirc j inbt outbt -> do
      let intyp = embedBundleType inbt
      let outtyp = embedBundleType outbt
      unless (checkSubtype typ2 intyp) $ throwError $ UnexpectedType e2 (embedBundleType inbt) typ2
      -- max(i1 + wires in e2, i2, j):
      let k = Max (Plus i1 wc) (Max i2 j)
      return $ InferenceResult outtyp k
    _ -> throwError $ UnexpectedTypeConstructor e1 (TCirc (Number 0) BTUnit BTUnit) typ1
-- BOX
inferType (EBox bt e) = do
  InferenceResult typ1 i <- inferType e
  let annotyp = embedBundleType bt
  case typ1 of
    TBang (TArrow typ2 typ3 j1 _) -> do
      sub2 <- tryUnify annotyp typ2 $ UnboxableType e typ1
      let typ3' = tsub sub2 typ3
      case toBundleType typ3' of
        Just outbt -> return $ InferenceResult (TCirc j1 bt outbt) i
        _ -> throwError $ UnboxableType e typ1
    _ -> throwError $ UnboxableType e typ1
-- LET-IN
inferType (ELet x e1 e2) = do
  InferenceResult typ1 i1 <- inferType e1
  (InferenceResult typ2 i2, wc) <- withWireCount $ withBoundVariable x typ1 $ inferType e2
  -- max(i1 + wires in e2, i2):
  let k = Max (Plus i1 wc) i2
  return $ InferenceResult typ2 k
-- DESTRUCTURING LET-IN
inferType (EDest x y e1 e2) = do
  InferenceResult typ1 i1 <- inferType e1
  typ2 <- TVar <$> freshTypeVariableName
  typ3 <- TVar <$> freshTypeVariableName
  sub2 <- tryUnify typ1 (TPair typ2 typ3) $ UnexpectedType e1 (TPair typ2 typ3) typ1
  let typ2' = tsub sub2 typ2
  let typ3' = tsub sub2 typ3
  (InferenceResult typ5 i2, wc) <- withWireCount $ withBoundVariable x typ2' $ withBoundVariable y typ3' $ inferType e2
  let k = Max (Plus i1 wc) i2
  return $ InferenceResult typ5 k
-- ANNOTATION
inferType (EAnno e annotyp) = do
  checkTypeWellFormedness annotyp
  InferenceResult typ i <- inferType e
  sub2 <- tryUnify typ annotyp $ UnexpectedType e annotyp typ
  -- annotation type should change to the inferred type
  -- since we do not have type variables in the surface syntax, this should never happen, byt still:
  assert (tsub sub2 annotyp == annotyp) $ return ()
  return $ InferenceResult annotyp i
-- FORCE
inferType (EForce e) = do
  InferenceResult typ i <- inferType e
  case typ of
    TBang typ' -> return $ InferenceResult typ' i
    _ -> throwError $ UnexpectedTypeConstructor e (TBang TUnit) typ
-- INDEX ABSTRACTION
inferType (EIAbs id e) = do
  (InferenceResult typ i, wc) <- withWireCount $ withBoundIndexVariable id $ inferType e
  return $ InferenceResult (TIForall id typ i wc) i
-- INDEX APPLICATION
inferType (EIApp e g) = do
  InferenceResult typ1 i <- inferType e
  case typ1 of
    TIForall id typ2 j1 _ -> do
      checkIndexWellFormedness j1
      return $ InferenceResult (isub g id typ2) (Max i (isub g id j1))
    _ -> throwError $ UnexpectedTypeConstructor e (TIForall "i" TUnit (Number 0) (Number 0)) typ1
-- CONSTANTS
inferType (EConst c) =
  let typ = case c of
        QInit0 -> TCirc (Number 1) BTUnit (BTWire Qubit)
        QInit1 -> TCirc (Number 1) BTUnit (BTWire Qubit)
        QDiscard -> TCirc (Number 1) (BTWire Qubit) BTUnit
        Meas -> TCirc (Number 1) (BTWire Qubit) (BTWire Bit)
        Hadamard -> TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)
        PauliX -> TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)
        PauliY -> TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)
        PauliZ -> TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)
        CNot -> TCirc (Number 2) (BTPair (BTWire Qubit) (BTWire Qubit)) (BTPair (BTWire Qubit) (BTWire Qubit))
        Toffoli -> TCirc (Number 3) (BTPair (BTPair (BTWire Qubit) (BTWire Qubit)) (BTWire Qubit)) (BTPair (BTPair (BTWire Qubit) (BTWire Qubit)) (BTWire Qubit))
        MakeCRGate -> TIForall "i" (TCirc (Number 2) (BTPair (BTWire Qubit) (BTWire Qubit)) (BTPair (BTWire Qubit) (BTWire Qubit))) (Number 0) (Number 0)
   in return $ InferenceResult typ (Number 0)
-- LET-CONS
inferType (ELetCons x y e1 e2) = do
  InferenceResult typ1 i1 <- inferType e1
  case typ1 of
    TList j typ2 -> do
      unless (checkLeq (Number 1) j) $ throwError $ UnexpectedEmptyList e1 typ1
      (InferenceResult typ3 i2, wc) <- withWireCount $ withBoundVariable x typ2 $ withBoundVariable y (TList (Minus j (Number 1)) typ2) $ inferType e2
      let k = Max (i1 `Plus` wc) i2
      return $ InferenceResult typ3 k
    _ -> throwError $ UnexpectedTypeConstructor e1 (TList (Number 0) TUnit) typ1


--- EXPORTED WRAPPER FUNCTIONS ---------------------------------------------------------------

runTypeInferenceWith :: TypingEnvironment -> Expr -> Either TypingError (Type, Index)
runTypeInferenceWith env e = do
  case runStateT (inferType e) env of
    Left err -> Left err
    Right (InferenceResult typ i, remaining) -> do
      when (envIsLinear remaining) $ throwError $ UnusedLinearResources (typingContext env) (labelContext env)
      return (typ, i)

runTypeInference :: Expr -> Either TypingError (Type, Index)
runTypeInference = runTypeInferenceWith (TypingEnvironment emptyctx Map.empty Set.empty 0)
