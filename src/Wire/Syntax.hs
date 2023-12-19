{-# LANGUAGE FlexibleInstances #-}
module Wire.Syntax where
import Index

type LabelId = String

data WireType
    = Bit
    | Qubit
    deriving (Eq, Show)

data Bundle
    = UnitValue
    | Label LabelId
    deriving Show

data BundleType
    = UnitType
    | WireType WireType
    deriving (Eq, Show)

class Wide a where
    wireCount :: a -> Index

--Any traversable structure of wide elements has a width defined as the sum of the width of their elements
instance (Traversable t, Wide a) => Wide (t a) where
    wireCount x = let wirecounts = wireCount <$> x in foldr Plus (Number 0) wirecounts

instance Wide BundleType where
    wireCount UnitType = Number 0
    wireCount (WireType _) = Number 1