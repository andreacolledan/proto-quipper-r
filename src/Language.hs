module Language where
{-
import Wire
import Index

type VariableId = String

data Value
    = Bundle Bundle
    | BoxedCircuit Value

data Term
    = Apply Bundle Bundle

data Type
    = BundleType BundleType
    | Circ Index Type Type

instance Wide Type where
    wireCount (BundleType bt) = wireCount bt
    wireCount (Circ {}) = Number 0

type TypingContext = [(VariableId,Type)]

linear :: Type -> Bool
linear (BundleType _) = True
linear (Circ {}) = False
-}