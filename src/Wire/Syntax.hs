{-# LANGUAGE FlexibleInstances #-}
module Wire.Syntax where
import Index
import PrettyPrinter

type LabelId = String

data WireType
    = Bit
    | Qubit
    deriving (Eq, Show)

data Bundle
    = UnitValue
    | Label LabelId
    deriving Show

instance Pretty Bundle where
    pretty UnitValue = "*"
    pretty (Label id) = id

data BundleType
    = UnitType
    | WireType WireType
    deriving (Eq, Show)

instance Pretty BundleType where
    pretty UnitType = "Unit"
    pretty (WireType Bit) = "Bit"
    pretty (WireType Qubit) = "Qubit"

class Wide a where
    wireCount :: a -> Index

--Any traversable structure of wide elements has a width defined as the sum of the width of their elements
instance (Traversable t, Wide a) => Wide (t a) where
    wireCount x = let wirecounts = wireCount <$> x in foldr Plus (Number 0) wirecounts

instance Wide BundleType where
    wireCount UnitType = Number 0
    wireCount (WireType _) = Number 1