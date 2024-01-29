{-# LANGUAGE FlexibleInstances #-}
module AST.Bundle(
    Bundle(..),
    BundleType(..),
    WireType(..),
    LabelId,
    Wide(..),
    isBundleSubtype
) where

import AST.Index

import qualified Data.Set as Set
import PrettyPrinter

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

-- Bundle Type Syntax
-- Fig. 9
data BundleType
    = UnitType
    | WireType WireType
    | Tensor BundleType BundleType
    | List Index BundleType
    deriving (Eq, Show)
instance Pretty BundleType where
    pretty UnitType = "Unit"
    pretty (WireType Bit) = "Bit"
    pretty (WireType Qubit) = "Qubit"
    pretty (Tensor b1 b2) = "(" ++ pretty b1 ++ " ⊗ " ++ pretty b2 ++ ")"
    pretty (List i b) = "List[" ++ pretty i ++ "]" ++ pretty b
instance Indexed BundleType where
    wellFormed _ UnitType = True
    wellFormed _ (WireType _) = True
    wellFormed theta (Tensor b1 b2) = wellFormed theta b1 && wellFormed theta b2
    wellFormed theta (List i b) = wellFormed theta i && wellFormed theta b

    isub _ _ = id   -- No index variables in bundle types

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

--Any traversable structure of elements with wire counts can be wire counted
--Its wire count is the sum of the wire counts of its elements
instance (Traversable t, Wide a) => Wide (t a) where
    wireCount x = let wirecounts = wireCount <$> x in foldr Plus (Number 0) wirecounts


--- SUBTYPING ---------------------------------------------------------------------------------


isBundleSubtype :: BundleType -> BundleType -> Bool
isBundleSubtype UnitType UnitType = True
isBundleSubtype (WireType wtype1) (WireType wtype2) = wtype1 == wtype2
isBundleSubtype (Tensor b1 b2) (Tensor b1' b2') = isBundleSubtype b1' b1 && isBundleSubtype b2' b2
isBundleSubtype (List i b) (List i' b') = checkEq Set.empty i i' && isBundleSubtype b' b
isBundleSubtype _ _ = False
