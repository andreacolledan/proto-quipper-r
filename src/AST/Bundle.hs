{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module AST.Bundle(
    Bundle(..),
    BundleType(..),
    WireType(..),
    LabelId,
    Wide(..),
    isBundleSubtype,
    BundleTypeVariableId,
    BundleTypeSubstitution,
    HasBundleTypeVariables(..),
    compose
) where

import AST.Index
import qualified Data.Set as Set
import PrettyPrinter
import qualified Data.Map as Map
import Data.Map (Map)

--- LANGUAGE ---------------------------------------------------------------------------------

type LabelId = String

data WireType
    = Bit
    | Qubit
    deriving (Eq, Show)
instance Pretty WireType

-- Wire Bundle Syntax
-- Fig. 9
data Bundle
    = UnitValue             -- *
    | Label LabelId         -- ℓ,k
    | Pair Bundle Bundle    -- (˜l,˜k)
    | Nil                   -- []
    | Cons Bundle Bundle    -- ˜l:˜k
    deriving (Eq, Show)
instance Pretty Bundle where
    pretty UnitValue = "*"
    pretty (Label id) = id
    pretty (Pair b1 b2) = "(" ++ pretty b1 ++ ", " ++ pretty b2 ++ ")"
    pretty Nil = "[]"
    pretty (Cons b1 b2) = "(" ++ pretty b1 ++ ":" ++ pretty b2 ++ ")"


--- BUNDLE TYPES ---------------------------------------------------------------------------------


type BundleTypeVariableId = String

-- Bundle Type Syntax
-- Fig. 9
data BundleType
    = UnitType
    | WireType WireType
    | Tensor BundleType BundleType
    | List Index BundleType
    | TypeVariable BundleTypeVariableId
    deriving (Eq, Show)

instance Pretty BundleType where
    pretty UnitType = "Unit"
    pretty (WireType Bit) = "Bit"
    pretty (WireType Qubit) = "Qubit"
    pretty (Tensor b1 b2) = "(" ++ pretty b1 ++ " ⊗ " ++ pretty b2 ++ ")"
    pretty (List i b) = "List[" ++ pretty i ++ "]" ++ pretty b
    pretty (TypeVariable id) = id

instance Indexed BundleType where
    freeVariables :: BundleType -> IndexContext
    freeVariables UnitType = Set.empty
    freeVariables (WireType _) = Set.empty
    freeVariables (Tensor b1 b2) = freeVariables b1 `Set.union` freeVariables b2
    freeVariables (List i b) = freeVariables i `Set.union` freeVariables b
    freeVariables (TypeVariable _) = Set.empty
    wellFormed :: IndexContext -> BundleType -> Bool
    wellFormed _ UnitType = True
    wellFormed _ (WireType _) = True
    wellFormed theta (Tensor b1 b2) = wellFormed theta b1 && wellFormed theta b2
    wellFormed theta (List i b) = wellFormed theta i && wellFormed theta b
    wellFormed _ (TypeVariable _) = True
    isub :: Index -> IndexVariableId -> BundleType -> BundleType
    isub _ _ = id   -- No index variables in bundle types

--- SUBSTITUTION ---------------------------------------------------------------------------------

type BundleTypeSubstitution = Map BundleTypeVariableId BundleType

-- The class of datatypes that may contain bundle type variables
class HasBundleTypeVariables a where
    freeBundleTypeVariables :: a -> Set.Set BundleTypeVariableId
    applyBundleTypeSubstitution :: BundleTypeSubstitution -> a -> a
    mostGeneralBundleTypeUnifier :: a -> a -> Maybe BundleTypeSubstitution
    isBundleTypeClosed :: a -> Bool
    isBundleTypeClosed = Set.null . freeBundleTypeVariables

instance HasBundleTypeVariables BundleType where
    freeBundleTypeVariables UnitType = Set.empty
    freeBundleTypeVariables (WireType _) = Set.empty
    freeBundleTypeVariables (Tensor b1 b2) = freeBundleTypeVariables b1 `Set.union` freeBundleTypeVariables b2
    freeBundleTypeVariables (List i b) = freeBundleTypeVariables b
    freeBundleTypeVariables (TypeVariable id) = Set.singleton id
    applyBundleTypeSubstitution :: BundleTypeSubstitution -> BundleType -> BundleType
    applyBundleTypeSubstitution _ UnitType = UnitType
    applyBundleTypeSubstitution _ (WireType wt) = WireType wt
    applyBundleTypeSubstitution sub (Tensor b1 b2) = Tensor (applyBundleTypeSubstitution sub b1) (applyBundleTypeSubstitution sub b2)
    applyBundleTypeSubstitution sub (List i b) = List i (applyBundleTypeSubstitution sub b)
    applyBundleTypeSubstitution sub bt@(TypeVariable id) = Map.findWithDefault bt id sub
    mostGeneralBundleTypeUnifier :: BundleType -> BundleType -> Maybe BundleTypeSubstitution
    mostGeneralBundleTypeUnifier (TypeVariable id) b = assignVar id b
    mostGeneralBundleTypeUnifier b (TypeVariable id) = assignVar id b
    mostGeneralBundleTypeUnifier UnitType UnitType = return Map.empty
    mostGeneralBundleTypeUnifier (WireType wt1) (WireType wt2) | wt1 == wt2 = return Map.empty
    mostGeneralBundleTypeUnifier (Tensor b1 b2) (Tensor b1' b2') = do
        sub1 <- mostGeneralBundleTypeUnifier b1 b1'
        sub2 <- mostGeneralBundleTypeUnifier (applyBundleTypeSubstitution sub1 b2) (applyBundleTypeSubstitution sub1 b2')
        return $ compose sub2 sub1
    mostGeneralBundleTypeUnifier (List _ b) (List _ b') = mostGeneralBundleTypeUnifier b b'
    mostGeneralBundleTypeUnifier _ _ = Nothing

assignVar :: BundleTypeVariableId -> BundleType -> Maybe BundleTypeSubstitution
assignVar id (TypeVariable id') | id == id' = return Map.empty
assignVar id b | id `Set.member` freeBundleTypeVariables b = Nothing
assignVar id b = return $ Map.singleton id b

compose :: BundleTypeSubstitution -> BundleTypeSubstitution -> BundleTypeSubstitution
compose sub1 sub2 = Map.union (Map.map (applyBundleTypeSubstitution sub1) sub2) sub1


--- WIRE COUNTING ---------------------------------------------------------------------------------

-- The class of datatypes that can contain wires and are thus amenable to wire counting
-- Def. 2 (Wire Count)
class Wide a where
    wireCount :: a -> Index -- #(•) in the paper

instance Wide WireType where
    wireCount Bit = Number 1
    wireCount Qubit = Number 1

instance Wide BundleType where
    wireCount UnitType = Number 0
    wireCount (WireType wtype) = wireCount wtype
    wireCount (Tensor b1 b2) = Plus (wireCount b1) (wireCount b2)
    wireCount (List i b) = Mult i (wireCount b)
    wireCount (TypeVariable _) = error "wireCount: encountered type variable"

--Any traversable structure of elements with wire counts can be wire counted
--Its wire count is the sum of the wire counts of its elements
instance (Traversable t, Wide a) => Wide (t a) where
    wireCount x = let wirecounts = wireCount <$> x in foldr Plus (Number 0) wirecounts


--- SUBTYPING ---------------------------------------------------------------------------------


isBundleSubtype :: BundleType -> BundleType -> Bool
isBundleSubtype UnitType UnitType = True
isBundleSubtype (WireType wtype1) (WireType wtype2) = wtype1 == wtype2
isBundleSubtype (Tensor b1 b2) (Tensor b1' b2') = isBundleSubtype b1' b1 && isBundleSubtype b2' b2
isBundleSubtype (List i b) (List i' b') = checkEq i i' && isBundleSubtype b' b
isBundleSubtype _ _ = False
