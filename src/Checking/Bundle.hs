module Checking.Bundle (
    LabelContext,
    synthesizeLabelContext,
    synthesizeBundleType,
    checkBundleType,
    labelContextLookup,
    WireTypingError(..)
) where

import AST.Bundle
import AST.Index

import Control.Monad (when, unless)
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import PrettyPrinter

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
    show (BundleTypeMismatch b btype1 btype2) = "Bundle " ++ pretty b ++ " has type " ++ pretty btype1 ++ " but is expected to have type " ++ pretty btype2
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

-- Lookup a label in the label context and remove it
-- Returns the type of the label, throws an error if the label is not found
labelContextLookup :: LabelId -> StateT LabelContext (Either WireTypingError) WireType
labelContextLookup id = do
    q <- get
    outcome <- maybe (throwError $ UnboundLabel id) return (Map.lookup id q)
    put $ Map.delete id q
    return outcome

-- Q ⊢ l => T (Fig. 10)
synthesizeBundleType :: Bundle -> StateT LabelContext (Either WireTypingError) BundleType
synthesizeBundleType UnitValue = return UnitType
synthesizeBundleType (Label id) = do
    btype <- labelContextLookup id
    return $ WireType btype
synthesizeBundleType (Pair b1 b2) = do
    btype1 <- synthesizeBundleType b1
    btype2 <- synthesizeBundleType b2
    return $ Tensor btype1 btype2

-- Returns the unique label context that attributes a given bundle type to a given bundle
-- matching the structure of the bundle with the structure of the bundle type
-- Throws an error if the bundle and the bundle type do not match
-- Q <== l : T
synthesizeLabelContext :: Bundle -> BundleType -> Either WireTypingError LabelContext
synthesizeLabelContext UnitValue UnitType = Right Map.empty
synthesizeLabelContext (Label id) (WireType wtype) = Right $ Map.fromList [(id,wtype)]
synthesizeLabelContext (Pair b1 b2) (Tensor btype1 btype2) = do
    q1 <- synthesizeLabelContext b1 btype1
    q2 <- synthesizeLabelContext b2 btype2
    return $ Map.union q1 q2
synthesizeLabelContext b btype = throwError $ ContextSynthesisMismatch b btype

-- Returns () if the wire bundle b type checks against the bundle type btype
-- Throws an error otherwise
-- Q ⊢ l <== T (Fig. 10)
checkBundleType :: Bundle -> BundleType -> StateT LabelContext (Either WireTypingError) ()
checkBundleType Nil btype = case btype of
    List i _ -> do
        unless (checkEq Set.empty i (Number 0)) $ throwError $ UnexpectedBundleListLength Nil i (Number 0)
    _ -> throwError $ UnexpectedBundleTypeContstructor Nil btype (List (Number 0) UnitType)
checkBundleType b@(Cons b1 b2) btype = case btype of
    List i btype' -> do
        when (checkLeq Set.empty i (Number 0)) $ throwError $ LengthZeroCons b btype
        checkBundleType b1 btype'
        checkBundleType b2 $ List (Minus i (Number 1)) btype'
    _ -> throwError $ UnexpectedBundleTypeContstructor (Cons b1 b2) btype (List (Number 0) UnitType)
checkBundleType b btype = do
    btype' <- synthesizeBundleType b
    unless (isBundleSubtype btype' btype) $ throwError $ BundleTypeMismatch b btype' btype