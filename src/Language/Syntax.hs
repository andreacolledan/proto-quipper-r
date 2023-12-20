module Language.Syntax where
import Wire.Syntax
import Circuit.Syntax
import Index

type VariableId = String

data Value
    = Bundle Bundle
    | BoxedCircuit Bundle Circuit Bundle
    deriving Show

data Term
    = Apply Value Value
    deriving Show

data Type
    = BundleType BundleType
    | Circ Index BundleType BundleType
    deriving Show

linear :: Type -> Bool
linear (BundleType _) = True
linear (Circ {}) = False

instance Wide Type where
    wireCount (BundleType bt) = wireCount bt
    wireCount (Circ {}) = Number 0