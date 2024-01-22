module Language.Syntax(
    Value(..),
    Term(..),
    Type(..),
    isLinear,
    VariableId,
    toBundleType,
) where
import Circuit.Syntax
import Index
import PrettyPrinter
import WireBundle.Syntax(LabelId, Bundle, BundleType, WireType, Wide(..))
import qualified WireBundle.Syntax as Bundle

type VariableId = String

-- Fig. 8
data Value
    = UnitValue
    | Label LabelId                         -- *
    | Variable VariableId                   -- x
    | Pair Value Value                      -- (V, W)
    | BoxedCircuit Bundle Circuit Bundle    -- (l, C, k)
    | Abs VariableId Type Term              -- λx:t.M
    | Lift Term                             -- lift(M)
    deriving (Eq, Show)

instance Pretty Value where
    pretty UnitValue = "*"
    pretty (Label id) = id
    pretty (Variable id) = id
    pretty (Pair v w) = "(" ++ pretty v ++ ", " ++ pretty w ++ ")"
    pretty (BoxedCircuit _ c _) = "[" ++ pretty c ++ "]"
    pretty (Abs x t m) = "(λ" ++ x ++ ":" ++ pretty t ++ ". " ++ pretty m ++ ")"
    pretty (Lift m) = "lift(" ++ pretty m ++ ")"

-- Fig. 8
data Term
    = Apply Value Value                     -- apply(V, W)
    | Box BundleType Value                  -- box:T(V)
    | Dest VariableId VariableId Value Term -- let (x, y) = V in M
    | Return Value                          -- return V
    | Let VariableId Term Term              -- let x = M in N
    | App Value Value                       -- V W
    | Force Value                           -- force(V)
    deriving (Eq, Show)

instance Pretty Term where
    pretty (Apply v w) = "apply(" ++ pretty v ++ ", " ++ pretty w ++ ")"
    pretty (Box t v) = "box:" ++ pretty t ++ "(" ++ pretty v ++ ")"
    pretty (Dest x y v m) = "(let (" ++ x ++ ", " ++ y ++ ") = " ++ pretty v ++ " in " ++ pretty m ++ ")"
    pretty (Return v) = "return " ++ pretty v
    pretty (Let x m n) = "(let " ++ x ++ " = " ++ pretty m ++ " in " ++ pretty n ++ ")"
    pretty (App m n) = "(" ++ pretty m ++ " " ++ pretty n ++ ")"
    pretty (Force v) = "force(" ++ pretty v ++ ")"

-- Fig. 8
data Type
    = UnitType
    | WireType WireType
    | Tensor Type Type
    | Circ Index BundleType BundleType
    | Arrow Type Type Index Index
    | Bang Type
    deriving (Show, Eq)

instance Pretty Type where
    pretty UnitType = "Unit"
    pretty (WireType wt) = pretty wt
    pretty (Tensor t1 t2) = "(" ++ pretty t1 ++ " ⊗ " ++ pretty t2 ++ ")"
    pretty (Circ i inBtype outBtype) = "Circ [" ++ pretty i ++ "] (" ++ pretty inBtype ++ ", " ++ pretty outBtype ++ ")"
    pretty (Arrow typ1 typ2 i j) = "(" ++ pretty typ1 ++ " -o [" ++ pretty i ++ "," ++ pretty j ++ "] " ++ pretty typ2 ++ ")"
    pretty (Bang typ) = "!" ++ pretty typ

isLinear :: Type -> Bool
isLinear UnitType = False
isLinear (WireType _) = True
isLinear (Tensor typ1 typ2) = isLinear typ1 && isLinear typ2
isLinear (Circ {}) = False
isLinear (Arrow {}) = True
isLinear (Bang _) = False


instance Wide Type where
    wireCount UnitType = Number 0
    wireCount (WireType _) = Number 1
    wireCount (Tensor t1 t2) = Plus (wireCount t1) (wireCount t2)
    wireCount (Circ {}) = Number 0
    wireCount (Arrow _ _ _ j) = j
    wireCount (Bang _) = Number 0

toBundleType :: Type -> Maybe BundleType
toBundleType UnitType = Just Bundle.UnitType
toBundleType (WireType wtype) = Just $ Bundle.WireType wtype
toBundleType (Tensor typ1 typ2) = do
    btype1 <- toBundleType typ1
    btype2 <- toBundleType typ2
    return $ Bundle.Tensor btype1 btype2
toBundleType _ = Nothing
