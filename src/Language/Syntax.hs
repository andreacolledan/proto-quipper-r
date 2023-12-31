module Language.Syntax where
import WireBundle.Syntax(LabelId, Bundle, BundleType, WireType, Wide(..))
import Circuit.Syntax
import Index
import PrettyPrinter

type VariableId = String

-- Fig. 8
data Value
    = UnitValue
    | Label LabelId
    | Variable VariableId
    | Pair Value Value
    | BoxedCircuit Bundle Circuit Bundle
    deriving Show

instance Pretty Value where
    pretty UnitValue = "*"
    pretty (Label id) = id
    pretty (Variable id) = id
    pretty (Pair v w) = "(" ++ pretty v ++ ", " ++ pretty w ++ ")"
    pretty (BoxedCircuit _ c _) = pretty c

-- Fig. 8
data Term
    = Apply Value Value
    | Dest VariableId VariableId Value Term
    | Return Value
    deriving Show

instance Pretty Term where
    pretty (Apply v w) = "apply(" ++ pretty v ++ ", " ++ pretty w ++ ")"
    pretty (Dest x y v m) = "(let (" ++ x ++ ", " ++ y ++ ") = " ++ pretty v ++ " in " ++ pretty m ++ ")"
    pretty (Return v) = "return " ++ pretty v

-- Fig. 8
data Type
    = UnitType
    | WireType WireType
    | Tensor Type Type
    | Circ Index BundleType BundleType
    deriving (Show, Eq)

instance Pretty Type where
    pretty UnitType = "Unit"
    pretty (WireType wt) = pretty wt
    pretty (Tensor t1 t2) = "(" ++ pretty t1 ++ " ⊗ " ++ pretty t2 ++ ")"
    pretty (Circ i inBtype outBtype) = "Circ " ++ pretty i ++ " (" ++ pretty inBtype ++ ", " ++ pretty outBtype ++ ")"

isLinear :: Type -> Bool
isLinear UnitType = False
isLinear (WireType _) = True
isLinear (Tensor typ1 typ2) = isLinear typ1 && isLinear typ2
isLinear (Circ {}) = False

instance Wide Type where
    wireCount UnitType = Number 0
    wireCount (WireType _) = Number 1
    wireCount (Tensor t1 t2) = Plus (wireCount t1) (wireCount t2)
    wireCount (Circ {}) = Number 0