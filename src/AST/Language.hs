{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module AST.Language
  ( Value (..),
    Term (..),
    Type (..),
    isLinear,
    VariableId,
    toBundleType,
    TypeSubstitution,
    tsub,
    mgtu,
    compose,
    TypeVariableId
  )
where

import AST.Bundle (Bundle, BundleType, LabelId, Wide (..), WireType)
import qualified AST.Bundle as Bundle
import AST.Circuit
import AST.Index
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set
import qualified Data.Set as Set
import PrettyPrinter
import Semantics.Index

type VariableId = String

-- The datatype of PQR values
-- Fig. 8
data Value
  = UnitValue
  | Label LabelId                       -- l, k, t...
  | Variable VariableId                 -- x, y, z...
  | Pair Value Value                    -- (v, w)
  | BoxedCircuit Bundle Circuit Bundle  -- (b1, c, b2)
  | Abs VariableId Type Term            -- \x :: t . m
  | Lift Term                           -- lift m
  | Nil                                 -- []
  | Cons Value Value                    -- v:w
  | Fold IndexVariableId Value Value    -- fold[i] v w
  | Anno Value Type                     -- v :: typ
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
  = Apply Value Value                       -- apply(v, w)
  | Box BundleType Value                    -- box[bt] v
  | Dest VariableId VariableId Value Term   -- let (x, y) = v in m
  | Return Value                            -- return v
  | Let VariableId Term Term                -- let x = m in n
  | App Value Value                         -- v w
  | Force Value                             -- force v
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
  = UnitType                            -- ()
  | WireType WireType                   -- Bit | Qubit
  | Tensor Type Type                    -- (t1, t2)
  | Circ Index BundleType BundleType    -- Circ[i](bt1, vt2)
  | Arrow Type Type Index Index         -- t1 ->[i,j] t2
  | Bang Type                           -- !t
  | List Index Type                     -- List[I] t
  | TypeVariable TypeVariableId         -- α
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
  isub i id (Circ j inBtype outBtype) = Circ (isub i id j) inBtype outBtype -- Bundle types have no free variables
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

--- SUBSTITUTION ---------------------------------------------------------------------------------

type TypeSubstitution = Map TypeVariableId Type

-- tfv t Returns the free type variables occurring in t
tfv :: Type -> Set TypeVariableId
tfv UnitType = Set.empty
tfv (WireType _) = Set.empty
tfv (Tensor t1 t2) = tfv t1 `Set.union` tfv t2
tfv (Circ {}) = Set.empty
tfv (Arrow t1 t2 _ _) = tfv t1 `Set.union` tfv t2
tfv (Bang t) = tfv t
tfv (List _ t) = tfv t
tfv (TypeVariable id) = Set.singleton id

-- tsub sub t applies the type substitution sub to the type t
tsub :: TypeSubstitution -> Type -> Type
tsub _ UnitType = UnitType
tsub _ typ@(WireType _) = typ
tsub sub (Tensor t1 t2) = Tensor (tsub sub t1) (tsub sub t2)
tsub _ typ@(Circ {}) = typ
tsub sub (Arrow typ1 typ2 i j) = Arrow (tsub sub typ1) (tsub sub typ2) i j
tsub sub (Bang typ) = Bang (tsub sub typ)
tsub sub (List i typ) = List i (tsub sub typ)
tsub sub typ@(TypeVariable id) = Map.findWithDefault typ id sub

-- sub1 `compose` sub2 composes the type substitutions sub1 and sub2
-- according to sub2 ∘ sub1 = sub1 U (sub1 sub2)
compose :: TypeSubstitution -> TypeSubstitution -> TypeSubstitution
compose sub1 sub2 = Map.union (Map.map (tsub sub1) sub2) sub1



--- UNIFICATION ---------------------------------------------------------------------------------

-- assignTypeVariable id t attempts to return the singleton substitution id |-> t
-- if unnecessary (id != t) it returns the empty substitution
-- if impossible (id occurs in t) it returns Nothing
assignTypeVariable :: TypeVariableId -> Type -> Maybe TypeSubstitution
assignTypeVariable id (TypeVariable id') | id == id' = return Map.empty
assignTypeVariable id t | id `Set.member` tfv t = Nothing
assignTypeVariable id t = return $ Map.singleton id t

-- mgtu t1 t2 attempts to find a most general type substitution sub such that sub(t1) = t2
-- If successful, it returns Just sub, otherwise it returns Nothing
-- TODO checks on equality of indices
-- TODO subtyping
mgtu :: Type -> Type -> Maybe TypeSubstitution
mgtu (TypeVariable id) t = assignTypeVariable id t
mgtu t (TypeVariable id) = assignTypeVariable id t
mgtu UnitType UnitType = return Map.empty
mgtu (WireType wt1) (WireType wt2) | wt1 == wt2 = return Map.empty
mgtu (Tensor t1 t2) (Tensor t1' t2') = do
  sub1 <- mgtu t1 t1'
  sub2 <- mgtu (tsub sub1 t2) (tsub sub1 t2')
  return $ compose sub2 sub1
mgtu (Circ i inBtype outBtype) (Circ i' inBtype' outBtype') | checkEq i i' && inBtype == inBtype' && outBtype == outBtype' = return Map.empty
mgtu (Arrow typ1 typ2 i j) (Arrow typ1' typ2' i' j') | checkEq i i' && checkEq j j' = do
  sub1 <- mgtu typ1 typ1'
  sub2 <- mgtu (tsub sub1 typ2) (tsub sub1 typ2')
  return $ compose sub2 sub1
mgtu (Bang typ) (Bang typ') = mgtu typ typ'
mgtu (List i typ) (List i' typ') | checkEq i i' = mgtu typ typ'
mgtu _ _ = Nothing