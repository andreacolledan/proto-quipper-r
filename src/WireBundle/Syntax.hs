{-# LANGUAGE FlexibleInstances #-}
module WireBundle.Syntax where
import Index
import PrettyPrinter

type LabelId = String

data WireType
    = Bit
    | Qubit
    deriving (Eq, Show)

instance Pretty WireType

data Bundle
    = UnitValue
    | Label LabelId
    | Pair Bundle Bundle
    deriving Show

instance Pretty Bundle where
    pretty UnitValue = "*"
    pretty (Label id) = id
    pretty (Pair b1 b2) = "(" ++ pretty b1 ++ ", " ++ pretty b2 ++ ")"

data BundleType
    = UnitType
    | WireType WireType
    | Tensor BundleType BundleType
    deriving (Eq, Show)

instance Pretty BundleType where
    pretty UnitType = "Unit"
    pretty (WireType Bit) = "Bit"
    pretty (WireType Qubit) = "Qubit"
    pretty (Tensor b1 b2) = "(" ++ pretty b1 ++ " ⊗ " ++ pretty b2 ++ ")"

class Wide a where
    wireCount :: a -> Index

--Any traversable structure of wide elements has a width defined as the sum of the width of their elements
instance (Traversable t, Wide a) => Wide (t a) where
    wireCount x = let wirecounts = wireCount <$> x in foldr Plus (Number 0) wirecounts

instance Wide WireType where
    wireCount Bit = Number 1
    wireCount Qubit = Number 1

instance Wide BundleType where
    wireCount UnitType = Number 0
    wireCount (WireType wtype) = wireCount wtype
    wireCount (Tensor b1 b2) = Plus (wireCount b1) (wireCount b2)