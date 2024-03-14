{-# LANGUAGE FlexibleInstances #-}

module Lang.Unified.Derivation (
  TypeDerivation,
  TypeError(..),
  TypingEnvironment(..),
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
  withScope

) where

import Bundle.AST
import Bundle.Infer
import Circuit
import Control.Monad (unless, when)
import Control.Monad.Error.Class
import Control.Monad.State
import Data.Foldable.Extra (notNull)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Index.AST
import Index.Semantics
import Lang.Type.AST
import Lang.Type.Semantics
import Lang.Type.Unify
import Lang.Unified.AST
import PrettyPrinter

--- TYPE DERIVATIONS MODULE --------------------------------------------------------------
---
--- This module contains base definitions to work with type derivations in
--- a linear setting. It defines the type of type derivation computations,
--- their environment, the basic operations used to manipulate it and
--- some useful combinators to build more complex derivations.
---
------------------------------------------------------------------------------------------

--- TYPING ENVIRONMENTS ------------------------------------------------------------------

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

-- The datatype of typing contexts (Corresponds to Γ or Φ in the paper)
type TypingContext = Map.Map VariableId [Binding]

emptyctx :: Map.Map a b
emptyctx = Map.empty

removeUsed :: TypingContext -> TypingContext
removeUsed = Map.filter notNull . Map.map (filter canBeUsed)

-- The datatype of typing environments
-- Represents the state of any derivation
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
    "* Expected expression \n  " ++ pretty exp ++ "\n  to have type\n  " ++ pretty (simplifyType typ1) ++ "\n  got instead \n  " ++ pretty (simplifyType typ2) ++ printSurroundings surr
  show (MismatchedInputInterface c q b surr) = "* Bundle '" ++ pretty b ++ "' is not a valid input interface for circuit '" ++ pretty c ++ "', whose input labels are '" ++ pretty q ++ "'" ++ printSurroundings surr
  show (MismatchedOutputInterface c q b surr) = "* Bundle '" ++ pretty b ++ "' is not a valid output interface for circuit '" ++ pretty c ++ "', whose output labels are '" ++ pretty q ++ "'" ++ printSurroundings surr
  show (UnexpectedWidthAnnotation m i j surr) =
    "* Expected expression '" ++ pretty m ++ "' to have width annotation '" ++ pretty i ++ "', got '" ++ pretty j ++ "' instead" ++ printSurroundings surr
  show (UnexpectedIndex i1 i2 surr) = "* Expected index '" ++ pretty i1 ++ "', got '" ++ pretty i2 ++ "' instead" ++ printSurroundings surr
  show (UnboxableType v typ surr) = "* Cannot box value '" ++ pretty v ++ "' of type '" ++ pretty (simplifyType typ) ++ "'" ++ printSurroundings surr
  show (UnfoldableStepfunction v typ surr) = "* Expression '" ++ pretty v ++ "' of type '" ++ pretty (simplifyType typ) ++ "' is not a valid step function" ++ printSurroundings surr
  show (UnfoldableAccumulator v typ surr) = "* Expression '" ++ pretty v ++ "' of type '" ++ pretty (simplifyType typ) ++ "' is not a valid accumulator" ++ printSurroundings surr
  show (UnfoldableArg v typ surr) = "* Expression '" ++ pretty v ++ "' of type '" ++ pretty typ ++ "' is not a valid fold argument" ++ printSurroundings surr
  show (UnboundIndexVariable id surr) = "* Unbound index variable '" ++ id ++ "'" ++ printSurroundings surr
  show (ShadowedIndexVariable id surr) = "* Shadowed index variable '" ++ id ++ "'" ++ printSurroundings surr
  show (OverusedLinearVariable id surr) = "* Linear variable '" ++ id ++ "' is used more than once" ++ printSurroundings surr
  show (UnexpectedEmptyList e t surr) = "* Cannot conclude that expression '" ++ pretty e ++ "' of type '" ++ pretty (simplifyType t) ++ "' is a non-empty list" ++ printSurroundings surr
  show (ExpectedBundleType e t surr) = "* Expected expression '" ++ pretty e ++ "' to have bundle type, got '" ++ pretty (simplifyType t) ++ "' instead" ++ printSurroundings surr
  show (CannotSynthesizeType e surr) = "* Cannot synthesize type for expression '" ++ pretty e ++ "'. Consider annotating it with a type" ++ printSurroundings surr

printSurroundings :: [Expr] -> String
printSurroundings [] = ""
printSurroundings (e : es) = "\n* While typing " ++ pretty e ++ go es 3
  where
    go :: [Expr] -> Int -> String
    go [] _ = ""
    go _ 0 = "\n..."
    go (e : es) n = "\n  In " ++ pretty e ++ go es (n - 1)

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

-- Necessary to avoid redundant case analysis in subsequent passes
instance MonadFail (Either TypeError) where
  fail _ = error "Internal error: base type changed from preprocessing to typechecking"


--- TYPE DERIVATIONS ---------------------------------------------------------------

-- The datatype of type derivations
-- Stateful computations with a typing environment, which may throw a type error
type TypeDerivation = StateT TypingEnvironment (Either TypeError)

runTypeDerivation :: TypeDerivation a -> TypingEnvironment -> Either TypeError (a, TypingEnvironment)
runTypeDerivation = runStateT

evalTypeDerivation :: TypeDerivation a -> TypingEnvironment -> Either TypeError a
evalTypeDerivation = evalStateT

execTypeDerivation :: TypeDerivation a -> TypingEnvironment -> Either TypeError TypingEnvironment
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
          put env {typingContext = Map.insert id (Binding (getType b) True : bs) gamma}
          return $ getType b
        else throwLocalError $ OverusedLinearVariable id
    [] -> error "Internal error: empty binding list"

-- labelContextLookup l looks up label l in the label context and removes it
-- throws Unbound UnboundLabel if the label is absent
labelContextLookup :: LabelId -> TypeDerivation WireType
labelContextLookup id = do
  env@TypingEnvironment {labelContext = q} <- get
  outcome <- maybe (throwError $ WireTypingError $ UnboundLabel id) return (Map.lookup id q)
  put $ env {labelContext = Map.delete id q}
  return outcome

-- substituteInEnvironment sub applies sub to the typing context
substituteInEnvironment :: TypeSubstitution -> TypeDerivation ()
substituteInEnvironment sub = do
  env@TypingEnvironment {typingContext = gamma} <- get
  let gamma' = Map.map (map (\(Binding t u) -> Binding (tsub sub t) u)) gamma
  put env {typingContext = gamma'}

checkWellFormedness :: (HasIndex a) => a -> TypeDerivation ()
checkWellFormedness x = do
  theta <- gets indexContext
  case ifv x Set.\\ theta of
    fv | Set.null fv -> return () -- all the free variables in the type are also in the context, good
    fv -> throwLocalError $ UnboundIndexVariable (Set.findMin fv) -- some free variables are not in scope, bad

makeFreshVariable :: String -> TypeDerivation VariableId
makeFreshVariable prefix = do
  env@TypingEnvironment {freshCounter = c} <- get
  put env {freshCounter = c + 1}
  return $ prefix ++ show c

unify :: Expr -> Type -> Type -> TypeDerivation TypeSubstitution
unify e t1 t2 = case mgtu t1 t2 of
  Just sub -> do
    substituteInEnvironment sub
    return sub
  Nothing -> throwLocalError $ UnexpectedType e t2 t1


-- Derivation combinators:

-- withBoundVariable x typ der describes derivation der
-- in which the variable name x is bound to type typ
withBoundVariable :: VariableId -> Type -> TypeDerivation a -> TypeDerivation a
withBoundVariable x typ der = do
  bindVariable x typ
  outcome <- der
  unbindVariable x -- this throws an error if x is linear and der does not consume it
  return outcome
  where
    bindVariable :: VariableId -> Type -> StateT TypingEnvironment (Either TypeError) ()
    bindVariable id typ = do
      env@TypingEnvironment {typingContext = gamma} <- get
      bs <- maybe (return []) return (Map.lookup id gamma)
      let gamma' = Map.insert id (Binding typ False : bs) gamma
      put env {typingContext = gamma'}
    unbindVariable :: VariableId -> StateT TypingEnvironment (Either TypeError) ()
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
withWireCount :: TypeDerivation a -> TypeDerivation (a, Index)
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

withBoundIndexVariable :: IndexVariableId -> TypeDerivation a -> TypeDerivation a
withBoundIndexVariable id der = do
  env@TypingEnvironment {indexContext = theta} <- get
  when (Set.member id theta) $ throwLocalError $ ShadowedIndexVariable id
  put env {indexContext = Set.insert id theta}
  outcome <- der
  env@TypingEnvironment {indexContext = theta} <- get
  put env {indexContext = Set.delete id theta}
  return outcome

withScope :: Expr -> TypeDerivation a -> TypeDerivation a
withScope e der = do
  env@TypingEnvironment {scopes = es} <- get
  put env {scopes = e : es}
  outcome <- der
  env@TypingEnvironment {scopes = es} <- get
  put env {scopes = tail es}
  return outcome