module Wire.Syntax where
import Index

type LabelId = String

data WireType
    = Bit
    | Qubit
    deriving Eq

data Bundle
    = UnitValue
    | Label LabelId

data BundleType
    = UnitType
    | WireType WireType
    deriving Eq

class Wide a where
    wireCount :: a -> Index

instance Wide BundleType where
    wireCount UnitType = Number 0
    wireCount (WireType _) = Number 1