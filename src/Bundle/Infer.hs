module Bundle.Infer
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

import Bundle.AST
import Index.AST
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
  show (BundleTypeMismatch b btype1 btype2) = "Expected bundle " ++ pretty b ++ " to have type " ++ pretty btype1 ++ ", got " ++ pretty btype2 ++ " instead"
  show (ContextSynthesisMismatch b btype) = "Cannot match structure of bundle " ++ pretty b ++ " and bundle type " ++ pretty btype ++ " to produce a label context"
  show (UnusedLabels q) = "Unused labels in label context: " ++ pretty q
  show (UnexpectedBundleTypeContstructor b btype1 btype2) = "Expected bundle " ++ pretty b ++ " to have type " ++ printConstructor btype1 ++ ", got type " ++ pretty btype2 ++ " instead"

printConstructor :: BundleType -> String
printConstructor BTUnit = "unit type"
printConstructor (BTWire _) = "wire type"
printConstructor (BTPair _ _) = "BTPair type"
printConstructor (BTList _ _) = "BTList type"
printConstructor (BTVar _) = "type variable"


--- BUNDLE TYPE INFERENCE ---------------------------------------------------------------------------------

data InferenceEnv = InferenceEnv
  { labelContext :: LabelContext,   --the label context, attributes wire types to labels
    freshVariableCounter :: Int           --the free variable counter used in inference
  }

-- freshBTVarName describes a computation returning a fresh type variable name
freshBTVarName :: StateT InferenceEnv (Either WireTypingError) BTVarId
freshBTVarName = do
  env@InferenceEnv {freshVariableCounter = c} <- get
  put $ env {freshVariableCounter = c + 1}
  return $ "a" ++ show c

-- unify bt1 bt2 error runs mgbtu bt1 bt2 in a bundle type inference (stateful) setting
-- If mgbtu returns Nothing, it throws error
unify :: Bundle -> BundleType -> BundleType -> StateT InferenceEnv (Either WireTypingError) BundleTypeSubstitution
unify b bt1 bt2 = case mgbtu bt1 bt2 of
  Just sub -> return sub
  Nothing -> throwError $ BundleTypeMismatch b bt2 bt1

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
inferBundleType :: Bundle -> StateT InferenceEnv (Either WireTypingError) BundleType
inferBundleType UnitValue = return BTUnit
inferBundleType (Label id) = do
  btype <- labelContextLookup id
  return (BTWire btype)
inferBundleType (Pair b1 b2) = do
  btype1 <- inferBundleType b1
  btype2 <- inferBundleType b2
  return (BTPair btype1 btype2)
inferBundleType Nil = BTList (Number 0) . BTVar <$> freshBTVarName
inferBundleType b@(Cons b1 b2) = do
  btype1 <- inferBundleType b1
  btype2 <- inferBundleType b2
  case btype2 of
    BTList i btype1' -> do
      sub3 <- unify b2 btype1' btype1
      return (BTList (Plus i (Number 1)) (btsub sub3 btype1))
    _ -> throwError $ UnexpectedBundleTypeContstructor (Cons b1 b2) btype2 (BTList (Number 0) BTUnit)

-- Q <== l : T
-- synthesizeLabelContext bundle bundleType returns the unique label context q such that q ⊢ bundle => bundleType, if it exists
-- Used in circuit signature checking
synthesizeLabelContext :: Bundle -> BundleType -> Either WireTypingError LabelContext
synthesizeLabelContext UnitValue BTUnit = Right Map.empty
synthesizeLabelContext (Label id) (BTWire wtype) = Right $ Map.fromList [(id, wtype)]
synthesizeLabelContext (Pair b1 b2) (BTPair btype1 btype2) = do
  q1 <- synthesizeLabelContext b1 btype1
  q2 <- synthesizeLabelContext b2 btype2
  return $ Map.union q1 q2
synthesizeLabelContext b btype = throwError $ ContextSynthesisMismatch b btype



--- EXPOSED INFERENCE AND CHECKING FUNCTIONS --------------------------------------------------------------

-- run type inference, if successful return both the type and the unused portion of thecontext
-- Used in boxed circuit inference
runBundleTypeInferenceWithRemaining :: LabelContext -> Bundle -> Either WireTypingError (BundleType, LabelContext)
runBundleTypeInferenceWithRemaining context bundle = do
  (t, InferenceEnv {labelContext = remaining}) <- runStateT (inferBundleType bundle) (InferenceEnv context 0)
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
  (t, InferenceEnv {labelContext = remaining}) <- runStateT (inferBundleType bundle) (InferenceEnv context 0)
  if isBundleSubtype t expected
    then return remaining
    else throwError $ BundleTypeMismatch bundle expected t

-- run the top-level type checking
-- This fails if there are unused labels in the context
runBundleTypeChecking :: LabelContext -> Bundle -> BundleType -> Either WireTypingError ()
runBundleTypeChecking context bundle expected = case runBundleTypeCheckingWithRemaining context bundle expected of
  Right remaining -> unless (Map.null remaining) $ throwError $ UnusedLabels remaining
  Left err -> throwError err