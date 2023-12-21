module Language.Syntax where
import Wire.Syntax
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
    pretty (BoxedCircuit b c b') = pretty c

data Term
    = Apply Value Value
    deriving Show

instance Pretty Term where
    pretty (Apply v w) = "apply(" ++pretty v ++ ", " ++ pretty w ++ ")"

data Type
    = BundleType BundleType
    | Circ Index BundleType BundleType
    deriving Show

instance Pretty Type where
    pretty (BundleType bt) = pretty bt
    pretty (Circ i t u) = "Circ " ++ pretty i ++ " (" ++ pretty t ++ ", " ++ pretty u ++ ")"

linear :: Type -> Bool
linear (BundleType _) = True
linear (Circ {}) = False

instance Wide Type where
    wireCount (BundleType bt) = wireCount bt
    wireCount (Circ {}) = Number 0