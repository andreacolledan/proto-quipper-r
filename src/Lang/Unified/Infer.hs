module Lang.Unified.Infer
  ( runTypeInference,
    runTypeInferenceWith,
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
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.State
import Data.Either.Extra (mapLeft)
import Data.List.Extra (notNull)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Index.AST
import Index.Semantics
import Lang.Type.AST
import Lang.Type.Semantics (checkSubtype, simplifyType)
import Lang.Type.Unify
import Lang.Unified.AST
import Lang.Unified.Constant
import PrettyPrinter

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

removeUsed :: TypingContext -> TypingContext
removeUsed = Map.filter notNull . Map.map (filter canBeUsed)

-- The state of a typing derivation
data TypingEnvironment = TypingEnvironment
  { typingContext :: TypingContext, -- attributes types to variable names (linear/nonlinear)
    labelContext :: LabelContext, -- attributes wire types to label names (linear)
    indexContext :: IndexContext, -- keeps track of the existing index variables in the environment
    scopes :: [Expr], -- a list of the expressions enclosing the current one
    liftedExpression :: Bool, -- whether the current expression is in a nonlinear context
    freshCounter :: Int -- a counter for generating fresh index variables
  }

instance Eq TypingEnvironment where
  TypingEnvironment gamma1 q1 theta1 _ _ _ == TypingEnvironment gamma2 q2 theta2 _ _ _ =
    removeUsed gamma1 == removeUsed gamma2 && q1 == q2 && theta1 == theta2

instance Wide TypingEnvironment where
  wireCount TypingEnvironment {typingContext = gamma, labelContext = q} = wireCount gamma `Plus` wireCount q

makeEnvForall :: [IndexVariableId] -> [(VariableId, Type)] -> [(LabelId, WireType)] -> TypingEnvironment
makeEnvForall theta gamma q =
  let gamma' = Map.fromList [(id, [Binding typ False]) | (id, typ) <- gamma]
   in TypingEnvironment gamma' (Map.fromList q) (Set.fromList theta) [] True 0

makeEnv :: [(VariableId, Type)] -> [(LabelId, WireType)] -> TypingEnvironment
makeEnv = makeEnvForall []

emptyEnv :: TypingEnvironment
emptyEnv = makeEnv [] []

-- check if a typing environment contains any linear variable.
envIsLinear :: TypingEnvironment -> Bool
envIsLinear TypingEnvironment {typingContext = gamma, labelContext = q} =
  let remainingVars = [id | (id, bs) <- Map.toList gamma, any mustBeUsed bs] -- remaining linear variables
   in not (null remainingVars) || not (Map.null q)

--- TYPING ERRORS ---------------------------------------------------------------

-- Errors that may be thrown during language-level type inference
data TypingError
  = WireTypingError WireTypingError
  | UnboundVariable VariableId [Expr]
  | UnboundIndexVariable Type IndexVariableId [Expr]
  | UnexpectedType Expr Type Type [Expr]
  | UnexpectedTypeConstructor Expr Type Type [Expr]
  | UnexpectedWidthAnnotation Expr Index Index [Expr]
  | ExpectedBundleType Expr Type [Expr]
  | CannotSynthesizeType Expr [Expr]
   -- Linearity errors
  |  UnusedLinearVariable VariableId [Expr]
  | OverusedLinearVariable VariableId [Expr]
  | LiftedLinearVariable VariableId [Expr]
   -- Boxed circuit errors
  |  MismatchedInputInterface Circuit LabelContext Bundle [Expr]
  | MismatchedOutputInterface Circuit LabelContext Bundle [Expr]
   -- Box errors
  |  UnexpectedBoxingType Expr Type BundleType [Expr]
  | UnboxableType Expr Type [Expr]
   -- Fold errors
  |  UnfoldableStepfunction Expr Type [Expr]
  | UnfoldableAccumulator Expr Type [Expr]
  | UnfoldableArg Expr Type [Expr]
  | NonincreasingStepFunction Expr Type Type [Expr]
   -- Other
  |  ShadowedIndexVariable IndexVariableId [Expr]
  | UnexpectedEmptyList Expr Type [Expr]
  | MismatchingContextUsage [Expr]
  deriving (Eq)

instance Show TypingError where
  show (WireTypingError err) = show err
  show (UnboundVariable id surr) = "* Unbound variable '" ++ id ++ "'" ++ printSurroundings surr
  show (UnusedLinearVariable id surr) = "* Unused linear variable '" ++ id ++ "'" ++ printSurroundings surr
  show (LiftedLinearVariable id surr) = "* Linear variable '" ++ id ++ "' cannot be consumed in a lifted expression" ++ printSurroundings surr
  show (UnexpectedType exp typ1 typ2 surr) =
    "* Expected expression \n  " ++ pretty exp ++ "\n  to have type\n  " ++ pretty (simplifyType typ1) ++ "\n  got instead \n  " ++ pretty (simplifyType typ2) ++ printSurroundings surr
  show (MismatchedInputInterface c q b surr) = "* Bundle '" ++ pretty b ++ "' is not a valid input interface for circuit '" ++ pretty c ++ "', whose input labels are '" ++ pretty q ++ "'" ++ printSurroundings surr
  show (MismatchedOutputInterface c q b surr) = "* Bundle '" ++ pretty b ++ "' is not a valid output interface for circuit '" ++ pretty c ++ "', whose output labels are '" ++ pretty q ++ "'" ++ printSurroundings surr
  show (UnexpectedWidthAnnotation m i j surr) =
    "* Expected expression '" ++ pretty m ++ "' to have width annotation '" ++ pretty i ++ "', got '" ++ pretty j ++ "' instead" ++ printSurroundings surr
  show (UnexpectedTypeConstructor exp typ1 typ2 surr) =
    "* Expected expression '" ++ pretty exp ++ "' to have '" ++ printConstructor (simplifyType typ1) ++ "', got type '" ++ pretty (simplifyType typ2) ++ "' instead" ++ printSurroundings surr
  show (UnexpectedBoxingType m btype1 btype2 surr) =
    "* Expected input type of boxed circuit '" ++ pretty m ++ "' to be '" ++ pretty btype1 ++ "', got '" ++ pretty btype2 ++ "' instead" ++ printSurroundings surr
  show (UnboxableType v typ surr) = "* Cannot box value '" ++ pretty v ++ "' of type '" ++ pretty (simplifyType typ) ++ "'" ++ printSurroundings surr
  show (UnfoldableStepfunction v typ surr) = "* Expression '" ++ pretty v ++ "' of type '" ++ pretty (simplifyType typ) ++ "' is not a valid step function" ++ printSurroundings surr
  show (UnfoldableAccumulator v typ surr) = "* Expression '" ++ pretty v ++ "' of type '" ++ pretty (simplifyType typ) ++ "' is not a valid accumulator" ++ printSurroundings surr
  show (UnfoldableArg v typ surr) = "* Expression '" ++ pretty v ++ "' of type '" ++ pretty typ ++ "' is not a valid fold argument" ++ printSurroundings surr
  show (NonincreasingStepFunction v typ1 typ2 surr) =
    "* Expected step function '" ++ pretty v ++ "' output type to be '" ++ pretty (simplifyType typ1) ++ "', got " ++ pretty (simplifyType typ2) ++ " instead" ++ printSurroundings surr
  show (UnboundIndexVariable t id surr) = "* Unbound index variable '" ++ id ++ "' in type annotation '" ++ pretty (simplifyType t) ++ "'" ++ printSurroundings surr
  show (ShadowedIndexVariable id surr) = "* Shadowed index variable '" ++ id ++ "'" ++ printSurroundings surr
  show (OverusedLinearVariable id surr) = "* Linear variable '" ++ id ++ "' is used more than once" ++ printSurroundings surr
  show (UnexpectedEmptyList e t surr) = "* Cannot conclude that expression '" ++ pretty e ++ "' of type '" ++ pretty (simplifyType t) ++ "' is a non-empty list" ++ printSurroundings surr
  show (MismatchingContextUsage surr) = "* The linear context is not used correctly" ++ printSurroundings surr
  show (ExpectedBundleType e t surr) = "* Expected expression '" ++ pretty e ++ "' to have bundle type, got '" ++ pretty (simplifyType t) ++ "' instead" ++ printSurroundings surr
  show (CannotSynthesizeType e surr) = "* Cannot synthesize type for expression '" ++ pretty e ++ "'. Consider annotating it with a type" ++ printSurroundings surr

printSurroundings :: [Expr] -> String
printSurroundings [] = ""
printSurroundings (e : es) = "\n* While typing " ++ pretty e ++ printSurroundings' es 3
  where
    printSurroundings' :: [Expr] -> Int -> String
    printSurroundings' [] _ = ""
    printSurroundings' _ 0 = "\n..."
    printSurroundings' (e : es) n = "\n  In " ++ pretty e ++ printSurroundings' es (n - 1)

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

throwLocalError :: ([Expr] -> TypingError) -> StateT TypingEnvironment (Either TypingError) a
throwLocalError err = do
  exprs <- gets scopes
  throwError $ err exprs

--- TYPING ENVIRONMENT OPERATIONS ---------------------------------------------------------------

-- typingContextLookup x looks up variable x in the typing context
-- It removes it if its type is linear
-- throws UnboundVariable if the variable is absent
typingContextLookup :: VariableId -> StateT TypingEnvironment (Either TypingError) Type
typingContextLookup id = do
  env@TypingEnvironment {typingContext = gamma} <- get
  bindings <- maybe (throwLocalError $ UnboundVariable id) return (Map.lookup id gamma)
  case bindings of
    (b : bs) ->
      if canBeUsed b
        then do
          put env {typingContext = Map.insert id (Binding (getType b) True : bs) gamma}
          return $ getType b
        else throwLocalError $ OverusedLinearVariable id
    [] -> error "Internal error: empty binding list"

-- labelContextLookup l looks up label l in the label context and removes it
-- throws Unbound UnboundLabel if the label is absent
labelContextLookup :: LabelId -> StateT TypingEnvironment (Either TypingError) WireType
labelContextLookup id = do
  env@TypingEnvironment {labelContext = q} <- get
  outcome <- maybe (throwError $ WireTypingError $ UnboundLabel id) return (Map.lookup id q)
  put $ env {labelContext = Map.delete id q}
  return outcome

-- substituteInEnvironment sub applies sub to the typing context
substituteInEnvironment :: TypeSubstitution -> StateT TypingEnvironment (Either TypingError) ()
substituteInEnvironment sub = do
  env@TypingEnvironment {typingContext = gamma} <- get
  let gamma' = Map.map (map (\(Binding t u) -> Binding (tsub sub t) u)) gamma
  put env {typingContext = gamma'}

-- TODO: factor these two together

checkTypeWellFormedness :: Type -> StateT TypingEnvironment (Either TypingError) ()
checkTypeWellFormedness typ = do
  theta <- gets indexContext
  case ifv typ Set.\\ theta of
    fv | Set.null fv -> return () -- all the free variables in the type are also in the context, good
    fv -> throwLocalError $ UnboundIndexVariable typ (Set.findMin fv) -- some free variables are not in scope, bad

checkIndexWellFormedness :: Index -> StateT TypingEnvironment (Either TypingError) ()
checkIndexWellFormedness i = do
  theta <- gets indexContext
  case ifv i Set.\\ theta of
    fv | Set.null fv -> return () -- all the free variables in the index are also in the context, good
    fv -> throwLocalError $ UnboundIndexVariable (TVar "i") (Set.findMin fv) -- some free variables are not in scope, bad

makeFreshVariable :: String -> StateT TypingEnvironment (Either TypingError) VariableId
makeFreshVariable prefix = do
  env@TypingEnvironment {freshCounter = c} <- get
  put env {freshCounter = c + 1}
  return $ prefix ++ show c

unify :: Expr -> Type -> Type -> StateT TypingEnvironment (Either TypingError) TypeSubstitution
unify e t1 t2 = case mgtu t1 t2 of
  Just sub -> do
    substituteInEnvironment sub
    return sub
  Nothing -> throwLocalError $ UnexpectedType e t2 t1

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
        Just (b : bs) -> do
          when (mustBeUsed b) (throwLocalError $ UnusedLinearVariable id)
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
    diffcount gamma1 gamma2 =
      wireCount $
        Map.elems $
          Map.differenceWith
            ( \bs1 bs2 -> case (bs1, bs2) of
                -- it was an available linear resource in gamma1 and it is a used linear resource in gamma2:
                (b1 : _, b2 : _) -> if canBeUsed b1 && not (canBeUsed b2) then Just [b1] else Nothing
                (_, _) -> error "Internal error: empty binding list"
            )
            gamma1
            gamma2

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
  let qconsumed = Map.difference q q'
  unless (Map.null gammaconsumed && Map.null qconsumed) $ do
    let remainingNames = Map.keys gammaconsumed ++ Map.keys qconsumed
    throwLocalError $ LiftedLinearVariable (head remainingNames)
  return outcome
  where
    linearconsumed :: TypingContext -> TypingContext -> TypingContext
    linearconsumed =
      Map.differenceWith
        ( \bs1 bs2 -> case (bs1, bs2) of
            -- it was an available linear resource in gamma1 and it is a used linear resource in gamma2:
            (b1 : _, b2 : _) -> if mustBeUsed b1 && not (canBeUsed b2) then Just [b1] else Nothing
            (_, _) -> error "Internal error: empty binding list"
        )

withBoundIndexVariable :: IndexVariableId -> StateT TypingEnvironment (Either TypingError) a -> StateT TypingEnvironment (Either TypingError) a
withBoundIndexVariable id der = do
  env@TypingEnvironment {indexContext = theta} <- get
  when (Set.member id theta) $ throwLocalError $ ShadowedIndexVariable id
  put env {indexContext = Set.insert id theta}
  outcome <- der
  env@TypingEnvironment {indexContext = theta} <- get
  put env {indexContext = Set.delete id theta}
  return outcome

withSameContext :: StateT TypingEnvironment (Either TypingError) a -> StateT TypingEnvironment (Either TypingError) a -> StateT TypingEnvironment (Either TypingError) (a, a)
withSameContext der1 der2 = do
  env <- get
  outcome1 <- der1
  fenv1 <- get
  put env
  outcome2 <- der2
  fenv2 <- get
  unless (fenv1 == fenv2) $ throwLocalError MismatchingContextUsage
  return (outcome1, outcome2)

withScope :: Expr -> StateT TypingEnvironment (Either TypingError) a -> StateT TypingEnvironment (Either TypingError) a
withScope e der = do
  env@TypingEnvironment {scopes = es} <- get
  put env {scopes = e : es}
  outcome <- der
  env@TypingEnvironment {scopes = es} <- get
  put env {scopes = tail es}
  return outcome

--- BUNDLE CHECKING WITHIN TYPE CHECKING ------------------------------------------------------------

-- embedWireBundle b returns the PQR value equivalent to b
embedWireBundle :: Bundle -> Expr
embedWireBundle Bundle.UnitValue = EUnit
embedWireBundle (Bundle.Label id) = ELabel id
embedWireBundle (Bundle.Pair b1 b2) = EPair (embedWireBundle b1) (embedWireBundle b2)
embedWireBundle Bundle.Nil = ENil Nothing
embedWireBundle (Bundle.Cons b1 b2) = ECons (embedWireBundle b1) (embedWireBundle b2)



--- TYPE INFERENCE ---------------------------------------------------------------

-- inferType e attempts to infer the type of expression e
-- If succesful, it returns an  record containing
-- > the inferred type of e
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
inferType :: Expr -> StateT TypingEnvironment (Either TypingError) (Type, Index)
-- UNIT
inferType EUnit = withScope EUnit $ return (TUnit, Number 0)
-- LABEL
inferType e@(ELabel id) = withScope e $ do
  btype <- labelContextLookup id
  return (TWire btype, Number 1)
-- VARIABLE
inferType e@(EVar id) = withScope e $ do
  typ <- typingContextLookup id
  return (typ, wireCount typ)
-- PAIR
inferType e@(EPair e1 e2) = withScope e $ do
  (typ1, i1) <- inferType e1
  ((typ2, i2), wc) <- withWireCount $ inferType e2
  -- max(i1 + wires in e2, i2 + #(typ1), #(typ1) + #(typ2)):
  let k = Max (Plus i1 wc) (Max (Plus i2 (wireCount typ1)) (Plus (wireCount typ1) (wireCount typ2)))
  return (TPair typ1 typ2, k)
-- NIL
inferType e@(ENil anno) = withScope e $ case anno of
  Just (TVar _) -> throwLocalError $ CannotSynthesizeType e
  Just typ -> do
    checkTypeWellFormedness typ
    return (TList (Number 0) typ, Number 0)
  Nothing -> error "Internal error: nil without type annotation"
-- ABSTRACTION
inferType e@(EAbs x annotyp e1) = withScope e $ do
  checkTypeWellFormedness annotyp
  ((typ, i), wc) <- withWireCount $ withBoundVariable x annotyp $ inferType e1
  return (TArrow annotyp typ i wc, wc)
-- LIFT
inferType e@(ELift e1) = withScope e $ do
  (typ, i) <- withNonLinearContext $ inferType e1
  unless (checkEq i (Number 0)) $ throwLocalError $ UnexpectedWidthAnnotation e1 (Number 0) i
  return (TBang typ, Number 0)
-- CONS
inferType e@(ECons e1 e2) = withScope e $ do
  (typ1, i1) <- inferType e1
  ((typ2, i2), wc) <- withWireCount $ inferType e2
  case typ2 of
    TList j typ1' -> do
      unless (checkSubtype (TList j typ1') (TList j typ1)) $ throwLocalError $ UnexpectedType e2 (TList j typ1) typ2
      -- max (i1 + wires in e2, i2 + #(typ1), (j+1) * #(typ1)):
      let k = Max (Plus i1 wc) (Max (Plus i2 (wireCount typ1)) (Mult (Plus j (Number 1)) (wireCount typ1)))
      return (TList (Plus j (Number 1)) typ1, k)
    _ -> throwLocalError $ UnexpectedTypeConstructor e2 (TList (Number 0) TUnit) typ2
-- FOLD
inferType e@(EFold e1 e2 e3) = withScope e $ do
  -- naming conventions are not satisfied here because the rule is HARD to parse
  (steptyp, i1) <- inferType e1
  case steptyp of
    TBang (TIForall id (TArrow (TPair acctyp elemtyp) acctyp' stepwidth o1) o2 o3) | checkEq o1 (Number 0) && checkEq o2 (Number 0) && checkEq o3 (Number 0) -> do
      unless (checkSubtype acctyp' (isub (Plus (IndexVariable id) (Number 1)) id acctyp)) $ throwLocalError $ UnfoldableStepfunction e1 steptyp
      ((acctyp'', i2), wc1) <- withWireCount $ inferType e2
      unless (checkSubtype acctyp'' (isub (Number 0) id acctyp)) $ throwLocalError $ UnfoldableAccumulator e2 acctyp''
      ((argtyp, i3), wc2) <- withWireCount $ inferType e3
      case argtyp of
        TList arglen elemtyp' -> do
          unless (checkSubtype elemtyp' elemtyp) $ throwLocalError $ UnfoldableArg e3 argtyp
          -- width upper bound of ONLY fold execution: max(#(acctyp{0/i},maximum[i<arglen] stepwidth + (arglen-(i+1))*#(elemtyp)))
          let k1 = Max (wireCount (isub (Number 0) id acctyp)) (Maximum id arglen (Plus stepwidth (Mult (Minus arglen (Plus (IndexVariable id) (Number 1))) (wireCount elemtyp))))
          -- the total upper bound takes into consideration the evaluation of e1, e2, e3 and the fold execution
          -- max(i1 + wires in e2 and e3, i2 + wires in e3, i3 + wires in the result of e2, k1):
          let k2 = Max (Plus i1 (Plus wc1 wc2)) (Max (Plus i2 wc2) (Max (Plus i3 (wireCount (isub (Number 0) id acctyp))) k1))
          return (isub arglen id acctyp, k2)
        _ -> throwLocalError $ UnfoldableArg e3 argtyp
    _ -> throwLocalError $ UnfoldableStepfunction e1 steptyp
-- BOXED CIRCUIT
inferType e@(ECirc b1 c b2) = withScope e $ do
  (inbt, inrem, outbt, outrem) <- lift $ mapLeft WireTypingError $ do
    (inlabels, outlabels) <- inferCircuitSignature c
    (inbt, inrem) <- runBundleTypeInferenceWithRemaining inlabels b1
    (outbt, outrem) <- runBundleTypeInferenceWithRemaining outlabels b2
    return (inbt, inrem, outbt, outrem)
  unless (null inrem) $ throwLocalError $ MismatchedInputInterface c inrem b1
  unless (null outrem) $ throwLocalError $ MismatchedOutputInterface c outrem b2
  return (TCirc (Number (width c)) inbt outbt, Number 0)
-- APPLICATION (FUNCTIONS)
inferType e@(EApp e1 e2) = withScope e $ do
  (typ1, i1) <- inferType e1
  ((typ2, i2), wc) <- withWireCount $ inferType e2
  case typ1 of
    TArrow annotyp typ3 j1 j2 -> do
      unless (checkSubtype typ2 annotyp) $ throwLocalError $ UnexpectedType e2 annotyp typ2
      -- max(i1 + wires in e2, i2 + j2, j1):
      let k = Max (Plus i1 wc) (Max (Plus i2 j2) j1)
      return (typ3, k)
    _ -> throwLocalError $ UnexpectedTypeConstructor e1 (TArrow TUnit TUnit (Number 0) (Number 0)) typ1
-- APPLY (CIRCUITS)
inferType e@(EApply e1 e2) = withScope e $ do
  (typ1, i1) <- inferType e1
  ((typ2, i2), wc) <- withWireCount $ inferType e2
  case typ1 of
    TCirc j inbt outbt -> do
      let intyp = fromBundleType inbt
      let outtyp = fromBundleType outbt
      unless (checkSubtype typ2 intyp) $ throwLocalError $ UnexpectedType e2 (fromBundleType inbt) typ2
      -- max(i1 + wires in e2, i2, j):
      let k = Max (Plus i1 wc) (Max i2 j)
      return (outtyp, k)
    _ -> throwLocalError $ UnexpectedTypeConstructor e1 (TCirc (Number 0) BTUnit BTUnit) typ1
-- BOX
inferType e@(EBox bt e1) = withScope e $ do
  (typ1, i) <- inferType e1
  let annotyp = fromBundleType bt
  case typ1 of
    TBang (TArrow typ2 typ3 j1 _) -> do
      unless (checkSubtype annotyp typ2) $ throwLocalError $ UnboxableType e1 typ1
      case toBundleType typ3 of
        Just outbt -> return (TCirc j1 bt outbt, i)
        _ -> throwLocalError $ UnboxableType e1 typ1
    _ -> throwLocalError $ UnboxableType e1 typ1
-- LET-IN
inferType e@(ELet x e1 e2) = withScope e $ do
  (typ1, i1) <- inferType e1
  ((typ2, i2), wc) <- withWireCount $ withBoundVariable x typ1 $ inferType e2
  -- max(i1 + wires in e2, i2):
  let k = Max (Plus i1 wc) i2
  return (typ2, k)
-- DESTRUCTURING LET-IN
inferType e@(EDest x y e1 e2) = withScope e $ do
  (typ1, i1) <- inferType e1
  case typ1 of
    TPair typ2 typ3 -> do
      ((typ4, i2), wc) <- withWireCount $ withBoundVariable x typ2 $ withBoundVariable y typ3 $ inferType e2
      let k = Max (Plus i1 wc) i2
      return (typ4, k)
    _ -> throwLocalError $ UnexpectedTypeConstructor e1 (TPair TUnit TUnit) typ1
-- ANNOTATION
inferType e@(EAnno e1 annotyp) = withScope e $ do
  checkTypeWellFormedness annotyp
  (typ, i) <- inferType e1
  unless (checkSubtype typ annotyp) $ throwLocalError $ UnexpectedType e1 annotyp typ
  return (annotyp, i)
-- FORCE
inferType e@(EForce e1) = withScope e $ do
  (typ, i) <- inferType e1
  case typ of
    TBang typ' -> return (typ', i)
    _ -> throwLocalError $ UnexpectedTypeConstructor e1 (TBang TUnit) typ
-- INDEX ABSTRACTION
inferType e@(EIAbs id e1) = withScope e $ do
  ((typ, i), wc) <- withWireCount $ withBoundIndexVariable id $ inferType e1
  return (TIForall id typ i wc, i)
-- INDEX APPLICATION
inferType e@(EIApp e1 g) = withScope e $ do
  (typ1, i) <- inferType e1
  case typ1 of
    TIForall id typ2 j1 _ -> do
      checkIndexWellFormedness j1
      return (isub g id typ2, Max i (isub g id j1))
    _ -> throwLocalError $ UnexpectedTypeConstructor e1 (TIForall "i" TUnit (Number 0) (Number 0)) typ1
-- CONSTANTS
inferType e@(EConst c) = withScope e $ return (typeOf c, Number 0)
-- LET-CONS
inferType e@(ELetCons x y e1 e2) = withScope e $ do
  (typ1, i1) <- inferType e1
  case typ1 of
    TList j typ2 -> do
      unless (checkLeq (Number 1) j) $ throwLocalError $ UnexpectedEmptyList e1 typ1
      ((typ3, i2), wc) <- withWireCount $ withBoundVariable x typ2 $ withBoundVariable y (TList (Minus j (Number 1)) typ2) $ inferType e2
      let k = Max (Plus i1 wc) i2
      return (typ3, k)
    _ -> throwLocalError $ UnexpectedTypeConstructor e1 (TList (Number 0) TUnit) typ1

-------------------------------------------------------------------------------
--- Inference of Type Variables Required for Lists ----------------------------
-------------------------------------------------------------------------------

-- At this stage, placeholder for all indices, which are irrelevant
irr :: Index
irr = Number 0

-- annotateType :: Expr -> StateT TypingEnvironment (Either TypingError) Expr
-- annotateType e = case inferBaseType e of
--   Left err -> throwError err
--   Right (e', typ, sub) -> return $ subst sub e'

inferBaseType :: Expr -> StateT TypingEnvironment (Either TypingError) (Expr, Type, TypeSubstitution)
-- UNIT
inferBaseType EUnit = withScope EUnit $ return (EUnit, TUnit, mempty)
-- LABEL
inferBaseType e@(ELabel id) = withScope e $ do
  btype <- labelContextLookup id
  return (ELabel id, TWire btype, mempty)
-- VARIABLE
inferBaseType e@(EVar id) = withScope e $ do
  typ <- typingContextLookup id
  return (EVar id, typ, mempty)
-- PAIR
inferBaseType e@(EPair e1 e2) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  (e2', typ2, sub2) <- inferBaseType e2
  let sub = sub2 <> sub1
  return (tsub sub $ EPair e1' e2', tsub sub $ TPair typ1 typ2, sub)
-- NIL
inferBaseType e@(ENil _) = withScope e $ do
  typ <- TVar <$> makeFreshVariable "a"
  return (ENil (Just typ), TList irr typ, mempty)
-- ABSTRACTION
inferBaseType e@(EAbs x annotyp e1) = withScope e $ do
  (e1', typ1, sub1) <- withBoundVariable x annotyp $ inferBaseType e1
  return (EAbs x (tsub sub1 annotyp) e1', tsub sub1 (TArrow annotyp typ1 irr irr), sub1)
-- LIFT
inferBaseType e@(ELift e1) = withScope e $ do
  (e1', typ1, sub1) <- withNonLinearContext $ inferBaseType e1
  return (ELift e1', TBang typ1, sub1)
-- CONS
inferBaseType e@(ECons e1 e2) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  (e2', typ2, sub2) <- inferBaseType e2
  sub3 <- unify e2 typ2 (TList irr (tsub sub2 typ1))
  let sub = sub3 <> sub2 <> sub1
  return (tsub sub (ECons e1' e2'), TList irr (tsub sub typ1), sub)
-- LET-IN
inferBaseType e@(ELet x e1 e2) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  (e2', typ2, sub2) <- withBoundVariable x typ1 $ inferBaseType e2
  let sub = sub2 <> sub1
  return (tsub sub (ELet x e1' e2'), tsub sub typ2, sub)
-- DESTRUCTURING LET-IN
inferBaseType e@(EDest x y e1 e2) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  typ1l <- TVar <$> makeFreshVariable "a"
  typ1r <- TVar <$> makeFreshVariable "a"
  sub2 <- unify e1 typ1 (TPair typ1l typ1r)
  (e2', typ2, sub3) <- withBoundVariable x typ1l $ withBoundVariable y typ1r $ inferBaseType e2
  let sub = sub3 <> sub2 <> sub1
  return (tsub sub (EDest x y e1' e2'), tsub sub typ2, sub)
-- ANNOTATION
inferBaseType e@(EAnno e1 annotyp) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  sub2 <- unify e1 typ1 annotyp
  let sub = sub2 <> sub1
  return (tsub sub (EAnno e1' annotyp), tsub sub annotyp, sub)
-- FORCE
inferBaseType e@(EForce e1) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  typ1' <- TVar <$> makeFreshVariable "a"
  sub2 <- unify e1 typ1 (TBang typ1')
  let sub = sub2 <> sub1
  return (tsub sub (EForce e1'), tsub sub typ1', sub)
-- APPLICATION (FUNCTIONS)
inferBaseType e@(EApp e1 e2) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  (e2', typ2, sub2) <- inferBaseType e2
  typ1c <- TVar <$> makeFreshVariable "a"
  sub3 <- unify e1 (tsub sub2 typ1) (TArrow typ2 typ1c irr irr)
  let sub = sub3 <> sub2 <> sub1
  return (tsub sub (EApp e1' e2'), tsub sub typ1c, sub)
-- APPLY (CIRCUITS)
inferBaseType e@(EApply e1 e2) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  (e2', typ2, sub2) <- inferBaseType e2
  btc <- BTVar <$> makeFreshVariable "ba"
  let sub = sub2 <> sub1
  case toBundleType typ2 of
    Just bt2 -> do
      sub3 <- unify e1 (tsub sub typ1) (TCirc irr bt2 btc)
      let sub = sub3 <> sub2 <> sub1
      return (tsub sub (EApply e1' e2'), tsub sub (fromBundleType btc), sub)
    _ -> throwLocalError $ ExpectedBundleType e2 typ2
-- BOX
inferBaseType e@(EBox annobt e1) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  let annotyp = fromBundleType annobt
  typ1' <- TVar <$> makeFreshVariable "a"
  sub2 <- unify e1 typ1 (TBang (TArrow annotyp typ1' irr irr))
  let sub = sub2 <> sub1
  case toBundleType (tsub sub typ1') of
    Just btc -> return (tsub sub (EBox annobt e1'), tsub sub (TCirc irr annobt btc), sub)
    _ -> throwLocalError $ UnboxableType e1 (tsub sub typ1')
-- LET-CONS
inferBaseType e@(ELetCons x y e1 e2) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  typ1' <- TVar <$> makeFreshVariable "a"
  sub2 <- unify e1 typ1 (TList irr typ1')
  let sub = sub2 <> sub1
  (e2', typ2, sub3) <-
    withBoundVariable x (tsub sub typ1') $
      withBoundVariable y (tsub sub (TList irr typ1')) $
        inferBaseType (tsub sub2 e2)
  let sub = sub3 <> sub2 <> sub1
  return (tsub sub (ELetCons x y e1' e2'), tsub sub typ2, sub)
-- FOLD
inferBaseType e@(EFold e1 e2 e3) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  (e2', typ2, sub2) <- inferBaseType e2
  (e3', typ3, sub3) <- inferBaseType e3
  elemtyp <- TVar <$> makeFreshVariable "a"
  acctyp <- TVar <$> makeFreshVariable "a"
  let sub = sub3 <> sub2 <> sub1
  stepsub <- unify e1 (tsub sub typ1) (TBang (TIForall "i" (TArrow (TPair acctyp elemtyp) acctyp irr irr) irr irr))
  let sub = stepsub <> sub3 <> sub2 <> sub1
  accsub <- unify e2 (tsub sub typ2) acctyp
  let sub = accsub <> stepsub <> sub3 <> sub2 <> sub1
  argsub <- unify e3 (tsub sub typ3) (TList irr elemtyp)
  let sub = argsub <> accsub <> stepsub <> sub3 <> sub2 <> sub1
  return (tsub sub (EFold e1' e2' e3'), tsub sub acctyp, sub)
-- BOXED CIRCUIT
inferBaseType e@(ECirc b1 c b2) = withScope e $ do
  (inbt, inrem, outbt, outrem) <- lift $ mapLeft WireTypingError $ do
    (inlabels, outlabels) <- inferCircuitSignature c
    (inbt, inrem) <- runBundleTypeInferenceWithRemaining inlabels b1
    (outbt, outrem) <- runBundleTypeInferenceWithRemaining outlabels b2
    return (inbt, inrem, outbt, outrem)
  unless (null inrem) $ throwLocalError $ MismatchedInputInterface c inrem b1
  unless (null outrem) $ throwLocalError $ MismatchedOutputInterface c outrem b2
  return (ECirc b1 c b2, TCirc (Number (width c)) inbt outbt, mempty)
-- INDEX ABSTRACTION
inferBaseType e@(EIAbs id e1) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  return (EIAbs id e1', TIForall id typ1 irr irr, sub1)
-- INDEX APPLICATION
inferBaseType e@(EIApp e1 g) = withScope e $ do
  (e1', typ1, sub1) <- inferBaseType e1
  typ1' <- TVar <$> makeFreshVariable "a"
  sub2 <- unify e1 typ1 (TIForall "i" typ1' irr irr)
  let sub = sub2 <> sub1
  return (tsub sub (EIApp e1' g), tsub sub typ1', sub)
-- CONSTANTS
inferBaseType e@(EConst c) = withScope e $ return (EConst c, typeOf c, mempty)

--- EXPORTED WRAPPER FUNCTIONS ---------------------------------------------------------------

runTypeInferenceWith :: TypingEnvironment -> Expr -> Either TypingError (Type, Index)
runTypeInferenceWith env e = do
  (e', _, _) <- evalStateT (inferBaseType e) env
  ((typ, i), remaining) <- runStateT (inferType e') env
  when (envIsLinear remaining) $ do
    let remainingNames = [id | (id, bs) <- Map.toList (typingContext remaining), any mustBeUsed bs] ++ Map.keys (labelContext remaining)
    throwError $ UnusedLinearVariable (head remainingNames) [e]
  return (typ, i)

runTypeInference :: Expr -> Either TypingError (Type, Index)
runTypeInference = runTypeInferenceWith emptyEnv

empyEnv :: TypingEnvironment
empyEnv = makeEnv [] []