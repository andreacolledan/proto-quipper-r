module Checking.Bundle (
    LabelContext,
    synthesizeLabelContext,
    runBundleTypeInference,
    runBundleTypeInferenceWithRemaining,
    runBundleTypeChecking,
    runBundleTypeCheckingWithRemaining,
    WireTypingError(..)
) where

import AST.Bundle
import AST.Index

import Control.Monad (unless)
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Map (Map)
import qualified Data.Map as Map
import PrettyPrinter
import Inference.Unification


-- Corresponds to Q in the paper
type LabelContext = Map LabelId WireType

-- Wire typing errors
data WireTypingError
    = UnboundLabel LabelId
    | BundleTypeMismatch Bundle BundleType BundleType
    | ContextSynthesisMismatch Bundle BundleType
    | UnusedLabels LabelContext
    | UnexpectedBundleListLength Bundle Index Index
    | LengthZeroCons Bundle BundleType
    | UnexpectedBundleTypeContstructor Bundle BundleType BundleType
    deriving (Eq)

instance Show WireTypingError where
    show (UnboundLabel id) = "Unbound label " ++ show id
    show (BundleTypeMismatch b btype1 btype2) = "Expected bundle " ++ pretty b ++ " to have type " ++ pretty btype1 ++ ", got" ++ pretty btype2 ++ " instead"
    show (ContextSynthesisMismatch b btype) = "Cannot match structure of bundle " ++ pretty b ++ " and bundle type " ++ pretty btype ++ " to produce a label context"
    show (UnusedLabels q) = "Unused labels in label context: " ++ pretty q
    show (UnexpectedBundleListLength b i1 i2) = "Expected list bundle " ++ pretty b ++ " to have length " ++ pretty i1 ++ ", got " ++ pretty i2 ++ " instead"
    show (LengthZeroCons b btype) = "Non-empty list " ++ pretty b ++ " cannot be given the type " ++ pretty btype ++ " because it has length 0" 
    show (UnexpectedBundleTypeContstructor b btype1 btype2) = "Expected bundle " ++ pretty b ++ " to have type " ++ printConstructor btype1 ++ ", got type " ++ pretty btype2 ++ " instead"

printConstructor :: BundleType -> String
printConstructor UnitType = "unit type"
printConstructor (WireType _) = "wire type"
printConstructor (Tensor _ _) = "tensor type"
printConstructor (List _ _) = "list type"
printConstructor (TypeVariable _) = "type variable"


--- BUNDLE TYPE INFERENCE ---------------------------------------------------------------------------------

data InferenceEnv = InferenceEnv {
    labelContext :: LabelContext,
    freeVarCounter :: Int
}

freshTypeVariableName :: StateT InferenceEnv (Either WireTypingError) BTVarId
freshTypeVariableName = do
    env@InferenceEnv{freeVarCounter = c} <- get
    put $ env{freeVarCounter = c + 1}
    return $ "a" ++ show c

tryUnify :: BundleType -> BundleType -> WireTypingError -> StateT InferenceEnv (Either WireTypingError) (Substitution BTVarId BundleType)
tryUnify bt1 bt2 err = case mgu bt1 bt2 of
    Just s -> return s
    Nothing -> throwError err

-- Lookup a label in the label context and remove it
-- Returns the type of the label, throws an error if the label is not found
labelContextLookup :: LabelId -> StateT InferenceEnv (Either WireTypingError) WireType
labelContextLookup id = do
    env@InferenceEnv{labelContext = q} <- get
    outcome <- maybe (throwError $ UnboundLabel id) return (Map.lookup id q)
    put $ env{labelContext = Map.delete id q}
    return outcome

-- Q ⊢ l => T (Fig. 10)
inferBundleType :: Bundle -> StateT InferenceEnv (Either WireTypingError) (BundleType, Substitution BTVarId BundleType)
inferBundleType UnitValue = return (UnitType, emptySub)
inferBundleType (Label id) = do
    btype <- labelContextLookup id
    return (WireType btype, emptySub)
inferBundleType (Pair b1 b2) = do
    (btype1, sub1) <- inferBundleType b1
    (btype2, sub2) <- inferBundleType b2
    return (Tensor btype1 btype2, compose sub1 sub2)
inferBundleType Nil = do
    a <- freshTypeVariableName
    return (List (Number 0) (TypeVariable a), emptySub)
inferBundleType b@(Cons b1 b2) = do
    (btype1, sub1) <- inferBundleType b1
    (btype2, sub2) <- inferBundleType b2
    case btype2 of 
        List i btype1' -> do
            sub3 <- tryUnify (apply sub1 btype1') (apply sub2 btype1) $ BundleTypeMismatch b (List i btype1) btype2
            return (List (Plus i (Number 1)) (apply sub3 btype1), sub3 `compose` sub2 `compose` sub1)
        _ -> throwError $ UnexpectedBundleTypeContstructor (Cons b1 b2) btype2 (List (Number 0) UnitType)

-- Q <== l : T
synthesizeLabelContext :: Bundle -> BundleType -> Either WireTypingError LabelContext
synthesizeLabelContext UnitValue UnitType = Right Map.empty
synthesizeLabelContext (Label id) (WireType wtype) = Right $ Map.fromList [(id,wtype)]
synthesizeLabelContext (Pair b1 b2) (Tensor btype1 btype2) = do
    q1 <- synthesizeLabelContext b1 btype1
    q2 <- synthesizeLabelContext b2 btype2
    return $ Map.union q1 q2
synthesizeLabelContext b btype = throwError $ ContextSynthesisMismatch b btype



--- EXPOSED INFERENCE AND CHECKING FUNCTIONS --------------------------------------------------------------


runBundleTypeInferenceWithRemaining :: LabelContext -> Bundle -> Either WireTypingError (BundleType, LabelContext)
runBundleTypeInferenceWithRemaining context bundle = do
    ((t,_),InferenceEnv{labelContext = remaining}) <- runStateT (inferBundleType bundle) (InferenceEnv context 0)
    return (t, remaining)

runBundleTypeInference :: LabelContext -> Bundle -> Either WireTypingError BundleType
runBundleTypeInference context bundle = case runBundleTypeInferenceWithRemaining context bundle of
    Right (t, remaining) -> do
        unless (Map.null remaining) $ throwError $ UnusedLabels remaining
        return t
    Left err -> throwError err

runBundleTypeCheckingWithRemaining :: LabelContext -> Bundle -> BundleType -> Either WireTypingError LabelContext
runBundleTypeCheckingWithRemaining context bundle expected = do
    ((t,_), InferenceEnv{labelContext = remaining}) <- runStateT (inferBundleType bundle) (InferenceEnv context 0)
    case (mgu t expected :: Maybe (Substitution BTVarId BundleType)) of
        Just sub -> do
            unless (isBundleSubtype (apply sub t) expected) $ throwError $ BundleTypeMismatch bundle expected t
            return remaining
        Nothing -> throwError $ BundleTypeMismatch bundle expected t

runBundleTypeChecking :: LabelContext -> Bundle -> BundleType -> Either WireTypingError ()
runBundleTypeChecking context bundle expected = case runBundleTypeCheckingWithRemaining context bundle expected of
    Right remaining -> unless (Map.null remaining) $ throwError $ UnusedLabels remaining
    Left err -> throwError err