module Language.Syntax(
    Value(..),
    Term(..),
    Type(..),
    isLinear,
    VariableId,
    toBundleType,
    checkSubtype
) where
import Circuit.Syntax
import Index
import PrettyPrinter
import WireBundle.Syntax(LabelId, Bundle, BundleType, WireType, Wide(..))
import qualified WireBundle.Syntax as Bundle

type VariableId = String

-- The datatype of PQR values
-- Fig. 8
data Value
    = UnitValue
    | Label LabelId                         -- *
    | Variable VariableId                   -- x
    | Pair Value Value                      -- (V, W)
    | BoxedCircuit Bundle Circuit Bundle    -- (l, C, k)
    | Abs VariableId Type Term              -- λx:t.M
    | Lift Term                             -- lift(M)
    | Nil                                   -- []
    | Cons Value Value                      -- V:W
    | Fold IndexVariableId Value Value      -- fold[i] V W
    | Anno Value Type                       -- (V : t)
    deriving (Eq, Show)
instance Pretty Value where
    pretty UnitValue = "*"
    pretty (Label id) = id
    pretty (Variable id) = id
    pretty (Pair v w) = "(" ++ pretty v ++ ", " ++ pretty w ++ ")"
    pretty (BoxedCircuit _ c _) = "[" ++ pretty c ++ "]"
    pretty (Abs x t m) = "(λ" ++ x ++ ":" ++ pretty t ++ ". " ++ pretty m ++ ")"
    pretty (Lift m) = "lift(" ++ pretty m ++ ")"
    pretty Nil = "[]"
    pretty (Cons v w) = "(" ++ pretty v ++ ":" ++ pretty w ++ ")"
    pretty (Fold i v w) = "fold[" ++ i ++ "] " ++ pretty v ++ " " ++ pretty w
    pretty (Anno v t) = "(" ++ pretty v ++ " : " ++ pretty t ++ ")"

-- The datatype of PQR terms
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

-- The datatype of PQR types
-- Fig. 8
data Type
    = UnitType                          -- 1
    | WireType WireType                 -- Bit | Qubit
    | Tensor Type Type                  -- A ⊗ B
    | Circ Index BundleType BundleType  -- Circ[I] (T,U)
    | Arrow Type Type Index Index       -- A -o [I,J] B
    | Bang Type                         -- !A
    | List Index Type                   -- List[I] A
    deriving (Show, Eq)
instance Pretty Type where
    pretty UnitType = "Unit"
    pretty (WireType wt) = pretty wt
    pretty (Tensor t1 t2) = "(" ++ pretty t1 ++ " ⊗ " ++ pretty t2 ++ ")"
    pretty (Circ i inBtype outBtype) = "Circ [" ++ pretty i ++ "] (" ++ pretty inBtype ++ ", " ++ pretty outBtype ++ ")"
    pretty (Arrow typ1 typ2 i j) = "(" ++ pretty typ1 ++ " -o [" ++ pretty i ++ "," ++ pretty j ++ "] " ++ pretty typ2 ++ ")"
    pretty (Bang typ) = "!" ++ pretty typ
    pretty (List i typ) = "List[" ++ pretty i ++ "] " ++ pretty typ

-- PQR types are amenable to wire counting
-- Def. 2 (Wire Count)
instance Wide Type where
    wireCount UnitType = Number 0
    wireCount (WireType _) = Number 1
    wireCount (Tensor t1 t2) = Plus (wireCount t1) (wireCount t2)
    wireCount (Circ {}) = Number 0
    wireCount (Arrow _ _ _ j) = j
    wireCount (Bang _) = Number 0
    wireCount (List i t) = Mult i (wireCount t)

-- PQR types are amenable to the notion of well-formedness with respect to an index context
instance Indexed Type where
    wellFormed _ UnitType = True
    wellFormed _ (WireType _) = True
    wellFormed theta (Tensor t1 t2) = wellFormed theta t1 && wellFormed theta t2
    wellFormed theta (Circ i inBtype outBtype) = wellFormed theta i && wellFormed theta inBtype && wellFormed theta outBtype
    wellFormed theta (Arrow typ1 typ2 i j) = wellFormed theta typ1 && wellFormed theta typ2 && wellFormed theta i && wellFormed theta j
    wellFormed theta (Bang typ) = wellFormed theta typ
    wellFormed theta (List i typ) = wellFormed theta i && wellFormed theta typ

    isub _ _ UnitType = UnitType
    isub _ _ (WireType wtype) = WireType wtype
    isub i id (Tensor t1 t2) = Tensor (isub i id t1) (isub i id t2)
    isub i id (Circ j inBtype outBtype) = Circ (isub i id j) inBtype outBtype --Bundle types have no free variables
    isub i id (Arrow typ1 typ2 j k) = Arrow (isub i id typ1) (isub i id typ2) (isub i id j) (isub i id k)
    isub i id (Bang typ) = Bang (isub i id typ)
    isub i id (List j typ) = List (isub i id j) (isub i id typ)

-- Returns True iff the given type is linear
isLinear :: Type -> Bool
isLinear UnitType = False
isLinear (WireType _) = True
isLinear (Tensor typ1 typ2) = isLinear typ1 && isLinear typ2
isLinear (Circ {}) = False
isLinear (Arrow {}) = True
isLinear (Bang _) = False
isLinear (List _ typ) = isLinear typ

-- Turns a suitable PQR type into an identical bundle type
toBundleType :: Type -> Maybe BundleType
toBundleType UnitType = Just Bundle.UnitType
toBundleType (WireType wtype) = Just $ Bundle.WireType wtype
toBundleType (Tensor typ1 typ2) = do
    btype1 <- toBundleType typ1
    btype2 <- toBundleType typ2
    return $ Bundle.Tensor btype1 btype2
toBundleType _ = Nothing

fromBundleType :: BundleType -> Type
fromBundleType Bundle.UnitType = UnitType
fromBundleType (Bundle.WireType wtype) = WireType wtype
fromBundleType (Bundle.Tensor btype1 btype2) = Tensor (fromBundleType btype1) (fromBundleType btype2)
fromBundleType (Bundle.List i btype) = List i (fromBundleType btype)


--- SUBTYPING ---------------------------------------------------------------------------------

checkSubtype :: IndexContext -> Type -> Type -> Bool
checkSubtype _ UnitType UnitType = True
checkSubtype _ (WireType wtype1) (WireType wtype2) = wtype1 == wtype2
checkSubtype theta (Bang t) (Bang t') = checkSubtype theta t t'
checkSubtype theta (Tensor t1 t2) (Tensor t1' t2') =
    checkSubtype theta t1' t1
    && checkSubtype theta t2 t2'
checkSubtype theta (Arrow t1 t2 i j) (Arrow t1' t2' i' j') =
    checkSubtype theta t1' t1
    && checkSubtype theta t2 t2'
    && checkLeq theta i i'
    && checkEq theta j j'
checkSubtype theta (Circ i btype1 btype2) (Circ i' btype1' btype2') =
    checkSubtype theta (fromBundleType btype1) (fromBundleType btype1')
    &&checkSubtype theta (fromBundleType btype1') (fromBundleType btype1)
    && checkSubtype theta (fromBundleType btype2) (fromBundleType btype2')
    && checkSubtype theta (fromBundleType btype2') (fromBundleType btype2)
    && checkLeq theta i i'
checkSubtype theta (List i t) (List i' t') =
    checkSubtype theta t t'
    && checkEq theta i i'
checkSubtype _ _ _ = False

