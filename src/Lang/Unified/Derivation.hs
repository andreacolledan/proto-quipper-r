{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Lang.Unified.Derivation
  ( TypeDerivation,
    TypeError (..),
    DerivationResult,
    TypingEnvironment (..),
    emptyEnv,
    makeEnv,
    mustBeUsed,
    makeEnvForall,
    envIsLinear,
    runTypeDerivation,
    evalTypeDerivation,
    execTypeDerivation,
    throwLocalError,
    typingContextLookup,
    labelContextLookup,
    substituteInEnvironment,
    checkWellFormedness,
    makeFreshVariable,
    unify,
    withBoundVariable,
    withWireCount,
    withNonLinearContext,
    withBoundIndexVariable,
    withScope,
    unlessSubtype,
    unlessEq,
    unlessLeq,
    unlessZero
  )
where

import Bundle.AST
import Bundle.Infer
import Circuit
import Control.Monad (unless, when)
import Control.Monad.Error.Class
import Control.Monad.State
import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set
import Index.AST
import Lang.Type.AST
import Lang.Type.Unify
import Lang.Unified.AST
import PrettyPrinter
import Control.Monad.Except
import Control.Monad.Identity
import Lang.Type.Semantics (checkSubtype)
import Index.Semantics
import Solving.CVC5 (SolverHandle)

--- TYPE DERIVATIONS MODULE --------------------------------------------------------------
---
--- This module contains base definitions to work with type derivations in
--- a linear setting. It defines the type of type derivation computations,
--- their environment, the basic operations used to manipulate it and
--- some useful combinators to build more complex derivations.
------------------------------------------------------------------------------------------

--- BINDINGS ------------------------------------------------------------------

-- | The datatype of bindings (carries the type of a variable and whether it has been used yet)
data BindingInfo = BindingInfo {getType :: Type, isUsed :: Bool} deriving (Eq, Show)

-- 
instance Wide BindingInfo where
  wireCount binding = if isUsed binding then Number 0 else wireCount (getType binding)

instance Pretty BindingInfo where
  pretty = pretty . getType

-- | @canBeUsed b@ returns 'True' if the binding @b@ is of a parameter type
-- or if it is a linear type and the corresponding variable has not been used yet.
canBeUsed :: BindingInfo -> Bool
canBeUsed (BindingInfo typ used) = not used || not (isLinear typ)

-- | @mustBeUsed b@ returns 'True' if the binding @b@ is of a linear type
-- and the corresponding variable has not been used yet.
mustBeUsed :: BindingInfo -> Bool
mustBeUsed (BindingInfo typ used) = not used && isLinear typ

--- TYPING CONTEXTS -----------------------------------------------------------

-- | The datatype of typing contexts (Corresponds to Γ or Φ in the paper)
type TypingContext = Map.HashMap VariableId [BindingInfo]

-- | The empty typing context
emptyctx :: Map.HashMap a b
emptyctx = Map.empty

--- TYPING ENVIRONMENTS --------------------------------------------------------

-- | The datatype of typing environments.
-- Represents the state of any linear type derivation
data TypingEnvironment = TypingEnvironment
  { typingContext :: TypingContext, -- attributes types to variable names (linear/nonlinear)
    labelContext :: LabelContext, -- attributes wire types to label names (linear)
    indexContext :: IndexContext, -- keeps track of the existing index variables in the environment
    scopes :: [Expr], -- a list of the expressions enclosing the current one
    liftedExpression :: Bool, -- whether the current expression is in a nonlinear context
    freshCounter :: Int -- a counter for generating fresh index variables
  }

instance Wide TypingEnvironment where
  wireCount TypingEnvironment {typingContext = gamma, labelContext = q} = wireCount gamma `Plus` wireCount q

-- | @makeEnvForall theta gamma q@ initializes a typing environment from the dictionary-like definitions of @gamma@ and @q@.
-- The index variables in @theta@ are considered to be in scope.
makeEnvForall :: [IndexVariableId] -> [(VariableId, Type)] -> [(LabelId, WireType)] -> TypingEnvironment
makeEnvForall theta gamma q =
  let gamma' = Map.fromList [(id, [BindingInfo typ False]) | (id, typ) <- gamma]
   in TypingEnvironment gamma' (Map.fromList q) (Set.fromList theta) [] True 0

-- | @makeEnv gamma q@ initializes a typing environment from the dictionary-like definitions of @gamma@ and @q@.
-- No index variables are considered to be in scope.
makeEnv :: [(VariableId, Type)] -> [(LabelId, WireType)] -> TypingEnvironment
makeEnv = makeEnvForall []

-- | The empty typing environment. No variables are in scope.
emptyEnv :: TypingEnvironment
emptyEnv = makeEnv [] []

-- | @envIsLinear env@ returns 'True' if the environment @env@ contains any linear variables or labels.
envIsLinear :: TypingEnvironment -> Bool
envIsLinear TypingEnvironment {typingContext = gamma, labelContext = q} =
  let remainingVars = [id | (id, bs) <- Map.toList gamma, any mustBeUsed bs] -- remaining linear variables
   in not (null remainingVars) || not (Map.null q)

--- TYPING ERRORS ---------------------------------------------------------------

-- The datatype of errors that can occur during a derivation
data TypeError
  = WireTypingError WireTypingError
  | UnboundVariable VariableId [Expr]
  | UnboundIndexVariable IndexVariableId [Expr]
  | UnexpectedType Expr Type Type [Expr]
  | UnexpectedIndex Index Index [Expr]
  | UnexpectedWidthAnnotation Expr Index Index [Expr]
  | ExpectedBundleType Expr Type [Expr]
  | CannotSynthesizeType Expr [Expr]
  | -- Linearity errors
    UnusedLinearVariable VariableId [Expr]
  | OverusedLinearVariable VariableId [Expr]
  | LiftedLinearVariable VariableId [Expr]
  | -- Boxed circuit errors
    MismatchedInputInterface Circuit LabelContext Bundle [Expr]
  | MismatchedOutputInterface Circuit LabelContext Bundle [Expr]
  | -- Box errors
    UnboxableType Expr Type [Expr]
  | -- Fold errors
    UnfoldableStepfunction Expr Type [Expr]
  | UnfoldableAccumulator Expr Type [Expr]
  | UnfoldableArg Expr Type [Expr]
  | -- Other
    ShadowedIndexVariable IndexVariableId [Expr]
  | UnexpectedEmptyList Expr Type [Expr]
  deriving (Eq)

instance Show TypeError where
  show (WireTypingError err) = show err
  show (UnboundVariable id surr) = "* Unbound variable '" ++ id ++ "'" ++ printSurroundings surr
  show (UnusedLinearVariable id surr) = "* Unused linear variable '" ++ id ++ "'" ++ printSurroundings surr
  show (LiftedLinearVariable id surr) = "* Linear variable '" ++ id ++ "' cannot be consumed in a lifted expression" ++ printSurroundings surr
  show (UnexpectedType exp typ1 typ2 surr) =
    "* Expected expression '" ++ trnc 80 (pretty exp) ++ "'\n   to have type '" ++ pretty typ1 ++ "',\n   got '" ++ pretty typ2 ++ " instead" ++ printSurroundings surr
  show (MismatchedInputInterface c q b surr) = "* Bundle '" ++ pretty b ++ "' is not a valid input interface for circuit '" ++ pretty c ++ "', whose input labels are '" ++ pretty q ++ "'" ++ printSurroundings surr
  show (MismatchedOutputInterface c q b surr) = "* Bundle '" ++ pretty b ++ "' is not a valid output interface for circuit '" ++ pretty c ++ "', whose output labels are '" ++ pretty q ++ "'" ++ printSurroundings surr
  show (UnexpectedWidthAnnotation m i j surr) =
    "* Expected expression '" ++ pretty m ++ "' to have width annotation '" ++ pretty i ++ "', got '" ++ pretty j ++ "' instead" ++ printSurroundings surr
  show (UnexpectedIndex i1 i2 surr) = "* Expected index '" ++ pretty i1 ++ "', got '" ++ pretty i2 ++ "' instead" ++ printSurroundings surr
  show (UnboxableType v typ surr) = "* Cannot box value '" ++ pretty v ++ "' of type '" ++ pretty typ ++ "'" ++ printSurroundings surr
  show (UnfoldableStepfunction v typ surr) = "* Expression '" ++ pretty v ++ "' of type '" ++ pretty typ ++ "' is not a valid step function" ++ printSurroundings surr
  show (UnfoldableAccumulator v typ surr) = "* Expression '" ++ pretty v ++ "' of type '" ++ pretty typ ++ "' is not a valid accumulator" ++ printSurroundings surr
  show (UnfoldableArg v typ surr) = "* Expression '" ++ pretty v ++ "' of type '" ++ pretty typ ++ "' is not a valid fold argument" ++ printSurroundings surr
  show (UnboundIndexVariable id surr) = "* Unbound index variable '" ++ id ++ "'" ++ printSurroundings surr
  show (ShadowedIndexVariable id surr) = "* Shadowed index variable '" ++ id ++ "'" ++ printSurroundings surr
  show (OverusedLinearVariable id surr) = "* Linear variable '" ++ id ++ "' is used more than once" ++ printSurroundings surr
  show (UnexpectedEmptyList e typ surr) = "* Cannot conclude that expression '" ++ pretty e ++ "' of type '" ++ pretty typ ++ "' is a non-empty list" ++ printSurroundings surr
  show (ExpectedBundleType e typ surr) = "* Expected expression '" ++ pretty e ++ "' to have bundle type, got '" ++ pretty typ ++ "' instead" ++ printSurroundings surr
  show (CannotSynthesizeType e surr) = "* Cannot synthesize type for expression '" ++ pretty e ++ "'. Consider annotating it with a type" ++ printSurroundings surr

-- | @printSurroundings es@ returns a string describing the expressions in @es@, if any
printSurroundings :: [Expr] -> String
printSurroundings [] = ""
printSurroundings (e : es) = "\n* While typing " ++ pretty e ++ go es 3
  where
    go :: [Expr] -> Int -> String
    go [] _ = ""
    go _ 0 = "\n..."
    go (e : es) n = "\n  In " ++ trnc 80 (pretty e) ++ go es (n - 1)

-- | @printConstructor t@ returns a string describing the top-level constructor of type @t@
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

-- | @trnc n s@ returns the first @n@ characters of @s@, followed by "..." if @s@ is longer than @n@
trnc :: Int -> String -> String
trnc n s = if length s > n then take n s ++ "..." else s

--- TYPE DERIVATIONS ---------------------------------------------------------------

type DerivationResult = ExceptT TypeError IO

-- The datatype of type derivations
-- Stateful computations with a typing environment, which may throw a type error
type TypeDerivation = StateT TypingEnvironment DerivationResult

runTypeDerivation :: TypeDerivation a -> TypingEnvironment -> DerivationResult (a, TypingEnvironment)
runTypeDerivation = runStateT

evalTypeDerivation :: TypeDerivation a -> TypingEnvironment -> DerivationResult a
evalTypeDerivation = evalStateT

execTypeDerivation :: TypeDerivation a -> TypingEnvironment -> DerivationResult TypingEnvironment
execTypeDerivation = execStateT

-- Basic derivation operators:

throwLocalError :: ([Expr] -> TypeError) -> TypeDerivation a
throwLocalError err = do
  exprs <- gets scopes
  throwError $ err exprs

-- typingContextLookup x looks up variable x in the typing context
-- It removes it if its type is linear
-- throws UnboundVariable if the variable is absent
typingContextLookup :: VariableId -> TypeDerivation Type
typingContextLookup id = do
  env@TypingEnvironment {typingContext = gamma} <- get
  bindings <- maybe (throwLocalError $ UnboundVariable id) return (Map.lookup id gamma)
  case bindings of
    (b : bs) ->
      if canBeUsed b
        then do
          put env {typingContext = Map.insert id (BindingInfo (getType b) True : bs) gamma}
          return $ getType b
        else throwLocalError $ OverusedLinearVariable id
    [] -> error "Internal error: empty binding list"

-- | @labelContextLookup id@ looks up label @id@ in the label context and removes it.
-- It throws 'UnboundLabel' if the label is absent.
labelContextLookup :: LabelId -> TypeDerivation WireType
labelContextLookup id = do
  env@TypingEnvironment {labelContext = q} <- get
  outcome <- maybe (throwError $ WireTypingError $ UnboundLabel id) return (Map.lookup id q)
  put $ env {labelContext = Map.delete id q}
  return outcome

-- | @substituteInEnvironment sub@ applies the substitution @sub@ to the typing environment
substituteInEnvironment :: TypeSubstitution -> TypeDerivation ()
substituteInEnvironment sub = do
  env@TypingEnvironment {typingContext = gamma} <- get
  let gamma' = Map.map (map (\(BindingInfo t u) -> BindingInfo (tsub sub t) u)) gamma
  put env {typingContext = gamma'}

-- | @checkWellFormedness x@ checks that all the index variables in @x@ are in scope.
-- It throws 'UnboundIndexVariable' if any of them is not.
checkWellFormedness :: (HasIndex a) => a -> TypeDerivation ()
checkWellFormedness x = do
  theta <- gets indexContext
  case ifv x Set.\\ theta of
    fv | Set.null fv -> return () -- all the free variables in the type are also in the context, good
    fv -> throwLocalError $ UnboundIndexVariable (Set.findMin fv) -- some free variables are not in scope, bad

-- | @makeFreshVariable prefix@ returns a fresh variable name with the given prefix.
-- TODO: using 'scopes', this function could also return a variable that is fresh in the current scope.
makeFreshVariable :: String -> TypeDerivation VariableId
makeFreshVariable prefix = do
  env@TypingEnvironment {freshCounter = c} <- get
  put env {freshCounter = c + 1}
  return $ prefix ++ show c

-- | @unify e t1 t2@ attempts to find the most general type substitution @sub@ such that @sub t1 == t2@.
-- If such a substitution does not exist, it throws 'UnexpectedType'. If it exists, the resulting substitution
-- is applied to the current typing environment and returned.
-- Expression @e@ is only used for error reporting.
unify :: Expr -> Type -> Type -> TypeDerivation TypeSubstitution
unify e t1 t2 = case mgtu t1 t2 of
  Just sub -> do
    substituteInEnvironment sub
    return sub
  Nothing -> throwLocalError $ UnexpectedType e t2 t1

--- DERIVATION COMBINATORS ------------------------------------------------------

-- | @withBoundVariable x typ der@ is derivation @der@ in which variable @x@ is bound to type @typ@.
withBoundVariable :: VariableId -> Type -> TypeDerivation a -> TypeDerivation a
withBoundVariable x typ der = do
  bindVariable x typ
  outcome <- der
  unbindVariable x -- this throws an error if x is linear and der does not consume it
  return outcome
  where
    bindVariable :: VariableId -> Type -> TypeDerivation ()
    bindVariable id typ = do
      env@TypingEnvironment {typingContext = gamma} <- get
      bs <- maybe (return []) return (Map.lookup id gamma)
      let gamma' = Map.insert id (BindingInfo typ False : bs) gamma
      put env {typingContext = gamma'}
    unbindVariable :: VariableId -> TypeDerivation ()
    unbindVariable id = do
      env@TypingEnvironment {typingContext = gamma} <- get
      case Map.lookup id gamma of
        Nothing -> error "Internal error: tried to unbind non-existing variable"
        Just [] -> error "Internal error: tried to unbind variable with empty binding list"
        Just (b : bs) -> do
          when (mustBeUsed b) (throwLocalError $ UnusedLinearVariable id)
          put env {typingContext = if null bs then Map.delete id gamma else Map.insert id bs gamma}

-- | @withWireCount der@ is derivation @der@ in which the result of the computation is paired with an index describing
-- how many wires have been consumed during @der@.
withWireCount :: TypeDerivation a -> TypeDerivation (a, Index)
withWireCount der = do
  TypingEnvironment {typingContext = gamma, labelContext = q} <- get
  outcome <- der
  TypingEnvironment {typingContext = gamma', labelContext = q'} <- get
  -- count how many linear resources have disappeared from the contexts
  let gammaDiff = diffcount gamma gamma'
  let qDiff = wireCount $ Map.difference q q'
  let resourceCount = gammaDiff `Plus` qDiff
  return (outcome, resourceCount)
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

-- | @withNonLinearContext der@ is derivation @der@ in which a 'LiftedLinearVariable' error is thrown if any linear resource from the
-- existing typing context is consumed. This is useful to ensure that a computation is not consuming linear resources.
withNonLinearContext :: TypeDerivation a -> TypeDerivation a
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

-- | @withBoundIndexVariable id der@ is derivation @der@ in which index variable @id@ is in scope.
withBoundIndexVariable :: IndexVariableId -> TypeDerivation a -> TypeDerivation a
withBoundIndexVariable id der = do
  env@TypingEnvironment {indexContext = theta} <- get
  when (Set.member id theta) $ throwLocalError $ ShadowedIndexVariable id
  put env {indexContext = Set.insert id theta}
  outcome <- der
  env@TypingEnvironment {indexContext = theta} <- get
  put env {indexContext = Set.delete id theta}
  return outcome

-- | @withScope e der@ is derivation @der@ in which expression the enclosing expression @e@ is visible.
-- This is only used to provide good error messages in case of failure and it has no effect on the contexts.
withScope :: Expr -> TypeDerivation a -> TypeDerivation a
withScope e der = do
  env@TypingEnvironment {scopes = es} <- get
  put env {scopes = e : es}
  outcome <- der
  env@TypingEnvironment {scopes = es} <- get
  put env {scopes = tail es}
  return outcome

unlessSubtype :: SolverHandle -> Type -> Type -> TypeDerivation () -> TypeDerivation ()
unlessSubtype qfh t1 t2 der = do
  c <- liftIO $ checkSubtype qfh t1 t2
  unless c der

unlessLeq :: SolverHandle -> Index -> Index -> TypeDerivation () -> TypeDerivation ()
unlessLeq qfh i j der = do
  c <- liftIO $ checkLeq qfh i j
  unless c der

unlessEq :: SolverHandle -> Index -> Index -> TypeDerivation () -> TypeDerivation ()
unlessEq qfh i j der = do
  c <- liftIO $ checkEq qfh i j
  unless c der

unlessZero :: SolverHandle -> Index -> TypeDerivation () -> TypeDerivation ()
unlessZero qfh i = unlessEq qfh i (Number 0)


--- OTHER STUFF ----------------------------------------------------------------

-- Necessary to avoid redundant case analysis in subsequent passes
instance MonadFail (Either TypeError) where
  fail _ = error "Internal error: unexpected type form in subsequent typing pass"


instance MonadFail Identity where
  fail _ = error "Internal error: unexpected type form in subsequent typing pass"