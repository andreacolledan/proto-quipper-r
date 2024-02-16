{-# LANGUAGE InstanceSigs #-}

module Lang.Type.AST where

import Bundle.AST (BundleType, Wide (..), WireType)
import qualified Bundle.AST as Bundle
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set
import qualified Data.Set as Set
import Index.AST
import Index.Semantics
import PrettyPrinter

--- TYPES ---------------------------------------------------------------------------------------

type TVarId = String

-- The datatype of PQR types
-- Fig. 8
data Type
  = UnitType -- ()
  | WireType WireType -- Bit | Qubit
  | Tensor Type Type -- (t1, t2)
  | Circ Index BundleType BundleType -- Circ[i](bt1, vt2)
  | Arrow Type Type Index Index -- t1 ->[i,j] t2
  | Bang Type -- !t
  | List Index Type -- List[I] t
  | TVar TVarId -- α
  | TForall Index Type -- ∀i . t
  | TNat -- Nat
  deriving (Show, Eq)

instance Pretty Type where
  pretty UnitType = "()"
  pretty (WireType wt) = pretty wt
  pretty (Tensor t1 t2) = "(" ++ pretty t1 ++ ", " ++ pretty t2 ++ ")"
  pretty (Circ i inBtype outBtype) = "Circ [" ++ pretty i ++ "] (" ++ pretty inBtype ++ ", " ++ pretty outBtype ++ ")"
  pretty (Arrow typ1 typ2 i j) = "(" ++ pretty typ1 ++ " ->[" ++ pretty i ++ "," ++ pretty j ++ "] " ++ pretty typ2 ++ ")"
  pretty (Bang typ) = "!" ++ pretty typ
  pretty (List i typ) = "List[" ++ pretty i ++ "] " ++ pretty typ
  pretty (TVar id) = id
  pretty (TForall i typ) = "∀" ++ pretty i ++ " . " ++ pretty typ
  pretty TNat = "Nat"

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
  wireCount (TForall _ t) = wireCount t
  wireCount TNat = Number 0
  wireCount (TVar _) = error "Cannot count wires of a type variable"

-- PQR types are amenable to the notion of well-formedness with respect to an index context
instance HasIndex Type where
  ifv :: Type -> Set IndexVariableId
  ifv UnitType = Set.empty
  ifv (WireType _) = Set.empty
  ifv (Tensor t1 t2) = ifv t1 `Set.union` ifv t2
  ifv (Circ i _ _) = ifv i
  ifv (Arrow typ1 typ2 i j) = ifv typ1 `Set.union` ifv typ2 `Set.union` ifv i `Set.union` ifv j
  ifv (Bang typ) = ifv typ
  ifv (List i typ) = ifv i `Set.union` ifv typ
  ifv TNat = Set.empty
  ifv (TVar _) = error "unimplemented"
  ifv (TForall i typ) = error "unimplemented"
  isub :: Index -> IndexVariableId -> Type -> Type
  isub _ _ UnitType = UnitType
  isub _ _ (WireType wtype) = WireType wtype
  isub i id (Tensor t1 t2) = Tensor (isub i id t1) (isub i id t2)
  isub i id (Circ j inBtype outBtype) = Circ (isub i id j) inBtype outBtype -- Bundle types have no free variables
  isub i id (Arrow typ1 typ2 j k) = Arrow (isub i id typ1) (isub i id typ2) (isub i id j) (isub i id k)
  isub i id (Bang typ) = Bang (isub i id typ)
  isub i id (List j typ) = List (isub i id j) (isub i id typ)
  isub _ _ TNat = TNat
  isub _ _ tv@(TVar _) = error "unimplemented"
  isub i id (TForall j typ) = error "unimplemented"

-- Returns True iff the given type is linear
isLinear :: Type -> Bool
isLinear UnitType = False
isLinear (WireType _) = True
isLinear (Tensor typ1 typ2) = isLinear typ1 && isLinear typ2
isLinear (Circ {}) = False
isLinear (Arrow {}) = True
isLinear (Bang _) = False
isLinear (List _ typ) = isLinear typ
isLinear TNat = False
isLinear (TVar _) = True
isLinear (TForall _ typ) = isLinear typ

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

type TypeSubstitution = Map TVarId Type

-- tfv t Returns the free type variables occurring in t
tfv :: Type -> Set TVarId
tfv UnitType = Set.empty
tfv (WireType _) = Set.empty
tfv (Tensor t1 t2) = tfv t1 `Set.union` tfv t2
tfv (Circ {}) = Set.empty
tfv (Arrow t1 t2 _ _) = tfv t1 `Set.union` tfv t2
tfv (Bang t) = tfv t
tfv (List _ t) = tfv t
tfv TNat = Set.empty
tfv (TVar id) = Set.singleton id
tfv (TForall _ t) = tfv t

-- tsub sub t applies the type substitution sub to the type t
tsub :: TypeSubstitution -> Type -> Type
tsub _ UnitType = UnitType
tsub _ typ@(WireType _) = typ
tsub sub (Tensor t1 t2) = Tensor (tsub sub t1) (tsub sub t2)
tsub _ typ@(Circ {}) = typ
tsub sub (Arrow typ1 typ2 i j) = Arrow (tsub sub typ1) (tsub sub typ2) i j
tsub sub (Bang typ) = Bang (tsub sub typ)
tsub sub (List i typ) = List i (tsub sub typ)
tsub _ TNat = TNat
tsub sub typ@(TVar id) = Map.findWithDefault typ id sub
tsub sub (TForall i typ) = error "unimplemented"

-- sub1 `compose` sub2 composes the type substitutions sub1 and sub2
-- according to sub2 ∘ sub1 = sub1 U (sub1 sub2)
compose :: TypeSubstitution -> TypeSubstitution -> TypeSubstitution
compose sub1 sub2 = Map.union (Map.map (tsub sub1) sub2) sub1

infixr 7 `compose`

--- UNIFICATION ---------------------------------------------------------------------------------

-- assignTVar id t attempts to return the singleton substitution id |-> t
-- if unnecessary (id != t) it returns the empty substitution
-- if impossible (id occurs in t) it returns Nothing
assignTVar :: TVarId -> Type -> Maybe TypeSubstitution
assignTVar id (TVar id') | id == id' = return Map.empty
assignTVar id t | id `Set.member` tfv t = Nothing
assignTVar id t = return $ Map.singleton id t

-- mgtu t1 t2 attempts to find a most general type substitution sub such that sub(t1) = t2
-- If successful, it returns Just sub, otherwise it returns Nothing
-- TODO checks on equality of indices
-- TODO subtyping
mgtu :: Type -> Type -> Maybe TypeSubstitution
mgtu (TVar id) t = assignTVar id t
mgtu t (TVar id) = assignTVar id t
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