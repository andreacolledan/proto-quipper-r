module Language.Syntax(
    Value(..),
    Term(..),
    Type(..),
    isLinear,
    VariableId
) where
import Circuit.Syntax
import Index
import PrettyPrinter
import WireBundle.Syntax(LabelId, Bundle, BundleType, WireType, Wide(..))

type VariableId = String

-- Fig. 8
data Value
    = UnitValue
    | Label LabelId
    | Variable VariableId
    | Pair Value Value
    | BoxedCircuit Bundle Circuit Bundle
    | Abs VariableId Type Term
    deriving Show

instance Pretty Value where
    pretty UnitValue = "*"
    pretty (Label id) = id
    pretty (Variable id) = id
    pretty (Pair v w) = "(" ++ pretty v ++ ", " ++ pretty w ++ ")"
    pretty (BoxedCircuit _ c _) = pretty c
    pretty (Abs x t m) = "(λ" ++ x ++ ":" ++ pretty t ++ ". " ++ pretty m ++ ")"

-- Fig. 8
data Term
    = Apply Value Value
    | Dest VariableId VariableId Value Term
    | Return Value
    | App Value Value
    deriving Show

instance Pretty Term where
    pretty (Apply v w) = "apply(" ++ pretty v ++ ", " ++ pretty w ++ ")"
    pretty (Dest x y v m) = "(let (" ++ x ++ ", " ++ y ++ ") = " ++ pretty v ++ " in " ++ pretty m ++ ")"
    pretty (Return v) = "return " ++ pretty v
    pretty (App m n) = "(" ++ pretty m ++ " " ++ pretty n ++ ")"

-- Fig. 8
data Type
    = UnitType
    | WireType WireType
    | Tensor Type Type
    | Circ Index BundleType BundleType
    | Arrow Type Type Index Index
    deriving (Show, Eq)

instance Pretty Type where
    pretty UnitType = "Unit"
    pretty (WireType wt) = pretty wt
    pretty (Tensor t1 t2) = "(" ++ pretty t1 ++ " ⊗ " ++ pretty t2 ++ ")"
    pretty (Circ i inBtype outBtype) = "Circ [" ++ pretty i ++ "] (" ++ pretty inBtype ++ ", " ++ pretty outBtype ++ ")"
    pretty (Arrow typ1 typ2 i j) = "(" ++ pretty typ1 ++ " ⊸ [" ++ pretty i ++ "," ++ pretty j ++ "]" ++ pretty typ2 ++ ")"

isLinear :: Type -> Bool
isLinear UnitType = False
isLinear (WireType _) = True
isLinear (Tensor typ1 typ2) = isLinear typ1 && isLinear typ2
isLinear (Circ {}) = False
isLinear (Arrow {}) = True


instance Wide Type where
    wireCount UnitType = Number 0
    wireCount (WireType _) = Number 1
    wireCount (Tensor t1 t2) = Plus (wireCount t1) (wireCount t2)
    wireCount (Circ {}) = Number 0
    wireCount (Arrow _ _ _ j) = j