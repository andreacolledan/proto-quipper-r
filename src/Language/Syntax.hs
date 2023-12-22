module Language.Syntax where
import WireBundle.Syntax
import Circuit.Syntax
import Index
import PrettyPrinter

type VariableId = String

data Value
    = Bundle Bundle
    | BoxedCircuit Bundle Circuit Bundle
    deriving Show

instance Pretty Value where
    pretty (Bundle b) = pretty b
    pretty (BoxedCircuit _ c _) = pretty c

data Term
    = Apply Value Value
    deriving Show

instance Pretty Term where
    pretty (Apply v w) = "apply(" ++ pretty v ++ ", " ++ pretty w ++ ")"

data Type
    = BundleType BundleType
    | Circ Index BundleType BundleType
    deriving Show

instance Pretty Type where
    pretty (BundleType btype) = pretty btype
    pretty (Circ i inBtype outBtype) = "Circ " ++ pretty i ++ " (" ++ pretty inBtype ++ ", " ++ pretty outBtype ++ ")"

isLinear :: Type -> Bool
isLinear (BundleType _) = True
isLinear (Circ {}) = False

instance Wide Type where
    wireCount (BundleType btype) = wireCount btype
    wireCount (Circ {}) = Number 0