module Checking.Bundle
  ( LabelContext,
    synthesizeLabelContext,
    runBundleTypeInference,
    runBundleTypeInferenceWithRemaining,
    runBundleTypeChecking,
    runBundleTypeCheckingWithRemaining,
    WireTypingError (..),
    isBundleSubtype,
  )
where

import AST.Bundle
import AST.Index
import Control.Monad (unless)
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Map (Map)
import qualified Data.Map as Map
import PrettyPrinter

-- Corresponds to Q in the paper
type LabelContext = Map LabelId WireType

data WireTypingError
  = UnboundLabel LabelId
  | BundleTypeMismatch Bundle BundleType BundleType
  | ContextSynthesisMismatch Bundle BundleType
  | UnusedLabels LabelContext
  | UnexpectedBundleTypeContstructor Bundle BundleType BundleType
  deriving (Eq)

instance Show WireTypingError where
  show (UnboundLabel id) = "Unbound label " ++ show id
  show (BundleTypeMismatch b btype1 btype2) = "Expected bundle " ++ pretty b ++ " to have type " ++ pretty btype1 ++ ", got" ++ pretty btype2 ++ " instead"
  show (ContextSynthesisMismatch b btype) = "Cannot match structure of bundle " ++ pretty b ++ " and bundle type " ++ pretty btype ++ " to produce a label context"
  show (UnusedLabels q) = "Unused labels in label context: " ++ pretty q
  show (UnexpectedBundleTypeContstructor b btype1 btype2) = "Expected bundle " ++ pretty b ++ " to have type " ++ printConstructor btype1 ++ ", got type " ++ pretty btype2 ++ " instead"

printConstructor :: BundleType -> String
printConstructor UnitType = "unit type"
printConstructor (WireType _) = "wire type"
printConstructor (Tensor _ _) = "tensor type"
printConstructor (List _ _) = "list type"
printConstructor (TypeVariable _) = "type variable"

--- BUNDLE TYPE INFERENCE ---------------------------------------------------------------------------------

data InferenceEnv = InferenceEnv
  { labelContext :: LabelContext,   --the label context, attributes wire types to labels
    freeVarCounter :: Int           --the free variable counter used in inference
  }

-- freshTypeVariableName describes a computation returning a fresh type variable name
freshTypeVariableName :: StateT InferenceEnv (Either WireTypingError) BundleTypeVariableId
freshTypeVariableName = do
  env@InferenceEnv {freeVarCounter = c} <- get
  put $ env {freeVarCounter = c + 1}
  return $ "a" ++ show c

-- tryUnify bt1 bt2 error runs mgbtu bt1 bt2 in a bundle type inference (stateful) setting
-- If mgbtu returns Nothing, it throws error
tryUnify :: BundleType -> BundleType -> WireTypingError -> StateT InferenceEnv (Either WireTypingError) BundleTypeSubstitution
tryUnify bt1 bt2 err = case mgbtu bt1 bt2 of
  Just s -> return s
  Nothing -> throwError err

-- Lookup a label in the label context and remove it (labels are linear)
-- Returns the type of the label, throws an error if the label is not found
labelContextLookup :: LabelId -> StateT InferenceEnv (Either WireTypingError) WireType
labelContextLookup id = do
  env@InferenceEnv {labelContext = q} <- get
  outcome <- maybe (throwError $ UnboundLabel id) return (Map.lookup id q)
  put $ env {labelContext = Map.delete id q}
  return outcome

-- Q ⊢ l => T (Fig. 10)
-- inferBundleType b describes the type inference computation on b.
-- If succesful, it returns the type of b together with the substitution accumulated during inference
inferBundleType :: Bundle -> StateT InferenceEnv (Either WireTypingError) (BundleType, BundleTypeSubstitution)
inferBundleType UnitValue = return (UnitType, Map.empty)
inferBundleType (Label id) = do
  btype <- labelContextLookup id
  return (WireType btype, Map.empty)
inferBundleType (Pair b1 b2) = do
  (btype1, sub1) <- inferBundleType b1
  (btype2, sub2) <- inferBundleType b2
  return (Tensor btype1 btype2, compose sub1 sub2)
inferBundleType Nil = do
  a <- freshTypeVariableName
  return (List (Number 0) (TypeVariable a), Map.empty)
inferBundleType b@(Cons b1 b2) = do
  (btype1, sub1) <- inferBundleType b1
  (btype2, sub2) <- inferBundleType b2
  case btype2 of
    List i btype1' -> do
      sub3 <- tryUnify (btsub sub1 btype1') (btsub sub2 btype1) $ BundleTypeMismatch b (List i btype1) btype2
      return (List (Plus i (Number 1)) (btsub sub3 btype1), sub3 `compose` sub2 `compose` sub1)
    _ -> throwError $ UnexpectedBundleTypeContstructor (Cons b1 b2) btype2 (List (Number 0) UnitType)

-- Q <== l : T
-- synthesizeLabelContext bundle bundleType returns the unique label context q such that q ⊢ bundle => bundleType, if it exists
-- Used in circuit signature checking
synthesizeLabelContext :: Bundle -> BundleType -> Either WireTypingError LabelContext
synthesizeLabelContext UnitValue UnitType = Right Map.empty
synthesizeLabelContext (Label id) (WireType wtype) = Right $ Map.fromList [(id, wtype)]
synthesizeLabelContext (Pair b1 b2) (Tensor btype1 btype2) = do
  q1 <- synthesizeLabelContext b1 btype1
  q2 <- synthesizeLabelContext b2 btype2
  return $ Map.union q1 q2
synthesizeLabelContext b btype = throwError $ ContextSynthesisMismatch b btype



--- EXPOSED INFERENCE AND CHECKING FUNCTIONS --------------------------------------------------------------

-- run type inference, if successful return both the type and the unused portion of thecontext
-- Used in boxed circuit inference
runBundleTypeInferenceWithRemaining :: LabelContext -> Bundle -> Either WireTypingError (BundleType, LabelContext)
runBundleTypeInferenceWithRemaining context bundle = do
  ((t, _), InferenceEnv {labelContext = remaining}) <- runStateT (inferBundleType bundle) (InferenceEnv context 0)
  return (t, remaining)

-- run the top-level type inference, if successful return the type
-- This fails if there are unused labels in the context
runBundleTypeInference :: LabelContext -> Bundle -> Either WireTypingError BundleType
runBundleTypeInference context bundle = case runBundleTypeInferenceWithRemaining context bundle of
  Right (t, remaining) -> do
    unless (Map.null remaining) $ throwError $ UnusedLabels remaining
    return t
  Left err -> throwError err

-- run type checking, if successful return the unused portion of the context
-- Used in circuit signature inference
runBundleTypeCheckingWithRemaining :: LabelContext -> Bundle -> BundleType -> Either WireTypingError LabelContext
runBundleTypeCheckingWithRemaining context bundle expected = do
  ((t, _), InferenceEnv {labelContext = remaining}) <- runStateT (inferBundleType bundle) (InferenceEnv context 0)
  case mgbtu t expected of
    Just sub -> do
      unless (isBundleSubtype (btsub sub t) expected) $ throwError $ BundleTypeMismatch bundle expected t
      return remaining
    Nothing -> throwError $ BundleTypeMismatch bundle expected t

-- run the top-level type checking
-- This fails if there are unused labels in the context
runBundleTypeChecking :: LabelContext -> Bundle -> BundleType -> Either WireTypingError ()
runBundleTypeChecking context bundle expected = case runBundleTypeCheckingWithRemaining context bundle expected of
  Right remaining -> unless (Map.null remaining) $ throwError $ UnusedLabels remaining
  Left err -> throwError err