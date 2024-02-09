{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
module AST.Language(
    Value(..),
    Term(..),
    Type(..),
    isLinear,
    VariableId,
    toBundleType,
    checkSubtype,
    TypeSubstitution,
    applyTypeSub,
    mgtu,
    compose,
    checkTypeEq,
    simplifyType
) where

import AST.Bundle(LabelId, Bundle, BundleType, WireType, Wide(..))
import qualified AST.Bundle as Bundle
import AST.Circuit
import AST.Index
import Semantics.Index

import PrettyPrinter
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Set
import qualified Data.Set as Set

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
    | Anno Value Type                       -- (V :: t)
    deriving (Eq, Show)
instance Pretty Value where
    pretty UnitValue = "()"
    pretty (Label id) = id
    pretty (Variable id) = id
    pretty (Pair v w) = "(" ++ pretty v ++ ", " ++ pretty w ++ ")"
    pretty (BoxedCircuit _ c _) = "[" ++ pretty c ++ "]"
    pretty (Abs x t m) = "(\\" ++ x ++ ":" ++ pretty t ++ " -> " ++ pretty m ++ ")"
    pretty (Lift m) = "(lift " ++ pretty m ++ ")"
    pretty Nil = "[]"
    pretty (Cons v w) = "(" ++ pretty v ++ ":" ++ pretty w ++ ")"
    pretty (Fold i v w) = "(fold[" ++ i ++ "] " ++ pretty v ++ " " ++ pretty w ++ ")"
    pretty (Anno v t) = "(" ++ pretty v ++ " :: " ++ pretty t ++ ")"

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


--- TYPES ---------------------------------------------------------------------------------------

type TypeVariableId = String

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
    | TypeVariable TypeVariableId       -- α
    deriving (Show, Eq)
instance Pretty Type where
    pretty UnitType = "()"
    pretty (WireType wt) = pretty wt
    pretty (Tensor t1 t2) = "(" ++ pretty t1 ++ ", " ++ pretty t2 ++ ")"
    pretty (Circ i inBtype outBtype) = "Circ [" ++ pretty i ++ "] (" ++ pretty inBtype ++ ", " ++ pretty outBtype ++ ")"
    pretty (Arrow typ1 typ2 i j) = "(" ++ pretty typ1 ++ " ->[" ++ pretty i ++ "," ++ pretty j ++ "] " ++ pretty typ2 ++ ")"
    pretty (Bang typ) = "!" ++ pretty typ
    pretty (List i typ) = "List[" ++ pretty i ++ "] " ++ pretty typ
    pretty (TypeVariable id) = id

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
    wireCount (TypeVariable _) = error "Cannot count wires of a type variable"

-- PQR types are amenable to the notion of well-formedness with respect to an index context
instance Indexed Type where
    freeVariables :: Type -> Set IndexVariableId
    freeVariables UnitType = Set.empty
    freeVariables (WireType _) = Set.empty
    freeVariables (Tensor t1 t2) = freeVariables t1 `Set.union` freeVariables t2
    freeVariables (Circ i _ _) = freeVariables i
    freeVariables (Arrow typ1 typ2 i j) = freeVariables typ1 `Set.union` freeVariables typ2 `Set.union` freeVariables i `Set.union` freeVariables j
    freeVariables (Bang typ) = freeVariables typ
    freeVariables (List i typ) = freeVariables i `Set.union` freeVariables typ
    freeVariables (TypeVariable _) = Set.empty
    wellFormed :: IndexContext -> Type -> Bool
    wellFormed _ UnitType = True
    wellFormed _ (WireType _) = True
    wellFormed theta (Tensor t1 t2) = wellFormed theta t1 && wellFormed theta t2
    wellFormed theta (Circ i inBtype outBtype) = wellFormed theta i && wellFormed theta inBtype && wellFormed theta outBtype
    wellFormed theta (Arrow typ1 typ2 i j) = wellFormed theta typ1 && wellFormed theta typ2 && wellFormed theta i && wellFormed theta j
    wellFormed theta (Bang typ) = wellFormed theta typ
    wellFormed theta (List i typ) = wellFormed theta i && wellFormed theta typ
    wellFormed _ (TypeVariable _) = True
    isub :: Index -> IndexVariableId -> Type -> Type
    isub _ _ UnitType = UnitType
    isub _ _ (WireType wtype) = WireType wtype
    isub i id (Tensor t1 t2) = Tensor (isub i id t1) (isub i id t2)
    isub i id (Circ j inBtype outBtype) = Circ (isub i id j) inBtype outBtype --Bundle types have no free variables
    isub i id (Arrow typ1 typ2 j k) = Arrow (isub i id typ1) (isub i id typ2) (isub i id j) (isub i id k)
    isub i id (Bang typ) = Bang (isub i id typ)
    isub i id (List j typ) = List (isub i id j) (isub i id typ)
    isub _ _ tv@(TypeVariable _) = tv

-- Returns True iff the given type is linear
isLinear :: Type -> Bool
isLinear UnitType = False
isLinear (WireType _) = True
isLinear (Tensor typ1 typ2) = isLinear typ1 && isLinear typ2
isLinear (Circ {}) = False
isLinear (Arrow {}) = True
isLinear (Bang _) = False
isLinear (List _ typ) = isLinear typ
isLinear (TypeVariable _) = True

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
fromBundleType (Bundle.TypeVariable _) = error "Cannot convert bundle type variable to PQR type"

--- SUBSTITUTION ---------------------------------------------------------------------------------

type TypeSubstitution = Map TypeVariableId Type

freeTypeVariables :: Type -> Set TypeVariableId
freeTypeVariables UnitType = Set.empty
freeTypeVariables (WireType _) = Set.empty
freeTypeVariables (Tensor t1 t2) = freeTypeVariables t1 `Set.union` freeTypeVariables t2
freeTypeVariables (Circ {}) = Set.empty
freeTypeVariables (Arrow t1 t2 _ _) = freeTypeVariables t1 `Set.union` freeTypeVariables t2
freeTypeVariables (Bang t) = freeTypeVariables t
freeTypeVariables (List _ t) = freeTypeVariables t
freeTypeVariables (TypeVariable id) = Set.singleton id

applyTypeSub :: TypeSubstitution -> Type -> Type
applyTypeSub _ UnitType = UnitType
applyTypeSub _ typ@(WireType _) = typ
applyTypeSub sub (Tensor t1 t2) = Tensor (applyTypeSub sub t1) (applyTypeSub sub t2)
applyTypeSub _ typ@(Circ {}) = typ
applyTypeSub sub (Arrow typ1 typ2 i j) = Arrow (applyTypeSub sub typ1) (applyTypeSub sub typ2) i j
applyTypeSub sub (Bang typ) = Bang (applyTypeSub sub typ)
applyTypeSub sub (List i typ) = List i (applyTypeSub sub typ)
applyTypeSub sub typ@(TypeVariable id) = Map.findWithDefault typ id sub

compose :: TypeSubstitution -> TypeSubstitution -> TypeSubstitution
compose sub1 sub2 = Map.union (Map.map (applyTypeSub sub1) sub2) sub1

--- UNIFICATION ---------------------------------------------------------------------------------

assignTypeVariable :: TypeVariableId -> Type -> Maybe TypeSubstitution
assignTypeVariable id (TypeVariable id') | id == id' = return Map.empty
assignTypeVariable id t | id `Set.member` freeTypeVariables t = Nothing
assignTypeVariable id t = return $ Map.singleton id t

--TODO include checks on equality of indices
mgtu :: Type -> Type -> Maybe TypeSubstitution
mgtu (TypeVariable id) t = assignTypeVariable id t
mgtu t (TypeVariable id) = assignTypeVariable id t
mgtu UnitType UnitType = return Map.empty
mgtu (WireType wt1) (WireType wt2) | wt1 == wt2 = return Map.empty
mgtu (Tensor t1 t2) (Tensor t1' t2') = do
    sub1 <- mgtu t1 t1'
    sub2 <- mgtu (applyTypeSub sub1 t2) (applyTypeSub sub1 t2')
    return $ compose sub2 sub1
mgtu (Circ i inBtype outBtype) (Circ i' inBtype' outBtype') | checkEq i i' && inBtype == inBtype' && outBtype == outBtype' = return Map.empty
mgtu (Arrow typ1 typ2 i j) (Arrow typ1' typ2' i' j') | checkEq i i' && checkEq j j' = do
    sub1 <- mgtu typ1 typ1'
    sub2 <- mgtu (applyTypeSub sub1 typ2) (applyTypeSub sub1 typ2')
    return $ compose sub2 sub1
mgtu (Bang typ) (Bang typ') = mgtu typ typ'
mgtu (List i typ) (List i' typ') | checkEq i i' = mgtu typ typ'
mgtu _ _ = Nothing




--- SUBTYPING ---------------------------------------------------------------------------------

checkSubtype :: Type -> Type -> Bool
checkSubtype UnitType UnitType = True
checkSubtype (WireType wtype1) (WireType wtype2) = wtype1 == wtype2
checkSubtype (Bang t) (Bang t') = checkSubtype t t'
checkSubtype (Tensor t1 t2) (Tensor t1' t2') =
    checkSubtype t1' t1
    && checkSubtype t2 t2'
checkSubtype (Arrow t1 t2 i j) (Arrow t1' t2' i' j') =
    checkSubtype t1' t1
    && checkSubtype t2 t2'
    && checkLeq i i'
    && checkEq j j'
checkSubtype (Circ i btype1 btype2) (Circ i' btype1' btype2') =
    checkSubtype (fromBundleType btype1) (fromBundleType btype1')
    &&checkSubtype (fromBundleType btype1') (fromBundleType btype1)
    && checkSubtype (fromBundleType btype2) (fromBundleType btype2')
    && checkSubtype (fromBundleType btype2') (fromBundleType btype2)
    && checkLeq i i'
checkSubtype (List i t) (List i' t') =
    checkSubtype t t'
    && checkEq i i'
checkSubtype _ _ = False

checkTypeEq :: Type -> Type -> Bool
checkTypeEq UnitType UnitType = True
checkTypeEq (WireType wtype1) (WireType wtype2) = wtype1 == wtype2
checkTypeEq (Bang t) (Bang t') = checkTypeEq t t'
checkTypeEq (Tensor t1 t2) (Tensor t1' t2') =
    checkTypeEq t1' t1
    && checkTypeEq t2 t2'
checkTypeEq (Arrow t1 t2 i j) (Arrow t1' t2' i' j') =
    checkTypeEq t1' t1
    && checkTypeEq t2 t2'
    && checkEq i i'
    && checkEq j j'
checkTypeEq (Circ i btype1 btype2) (Circ i' btype1' btype2') =
    checkTypeEq (fromBundleType btype1) (fromBundleType btype1')
    && checkTypeEq (fromBundleType btype2) (fromBundleType btype2')
    && checkEq i i'
checkTypeEq (List i t) (List i' t') =
    checkTypeEq t t'
    && checkEq i i'
checkTypeEq _ _ = False

simplifyType :: Type -> Type
simplifyType (Tensor t1 t2) = Tensor (simplifyType t1) (simplifyType t2)
simplifyType (Arrow t1 t2 i j) = Arrow (simplifyType t1) (simplifyType t2) (simplify i) (simplify j)
simplifyType (Bang t) = Bang (simplifyType t)
simplifyType (List i t) = List (simplify i) (simplifyType t)
simplifyType (Circ i inBtype outBtype) = Circ (simplify i) inBtype outBtype
simplifyType t = t