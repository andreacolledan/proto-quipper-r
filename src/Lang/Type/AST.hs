{-# LANGUAGE InstanceSigs #-}

module Lang.Type.AST where

import Bundle.AST ( BundleType (..), WireType, Wide(..) )
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
  = TUnit                                     -- ()
  | TWire WireType                            -- Bit | Qubit
  | TPair Type Type                           -- (t1, t2)
  | TCirc Index BundleType BundleType         -- Circ[i](bt1, vt2)
  | TArrow Type Type Index Index              -- t1 -o[i,j] t2
  | TBang Type                                -- !t
  | TList Index Type                          -- TList[I] t
  | TVar TVarId                               -- α
  | TIForall IndexVariableId Type Index Index -- i ->[i,j] t
  deriving (Show, Eq)

instance Pretty Type where
  pretty TUnit = "()"
  pretty (TWire wt) = pretty wt
  pretty (TPair t1 t2) = "(" ++ pretty t1 ++ ", " ++ pretty t2 ++ ")"
  pretty (TCirc i inBtype outBtype) = "Circ [" ++ pretty i ++ "] (" ++ pretty inBtype ++ ", " ++ pretty outBtype ++ ")"
  pretty (TArrow typ1 typ2 i j) = "(" ++ pretty typ1 ++ " -o[" ++ pretty i ++ ", " ++ pretty j ++ "] " ++ pretty typ2 ++ ")"
  pretty (TBang typ) = "!" ++ pretty typ
  pretty (TList i typ) = "List[" ++ pretty i ++ "] " ++ pretty typ
  pretty (TVar id) = id
  pretty (TIForall id typ i j) = "(" ++ id ++ " ->[" ++ pretty i ++ ", " ++ pretty j ++ "] " ++ pretty typ ++ ")"

-- PQR types are amenable to wire counting
-- Def. 2 (Wire Count)
instance Wide Type where
  wireCount TUnit = Number 0
  wireCount (TWire _) = Number 1
  wireCount (TPair t1 t2) = Plus (wireCount t1) (wireCount t2)
  wireCount (TCirc {}) = Number 0
  wireCount (TArrow _ _ _ i) = i
  wireCount (TBang _) = Number 0
  wireCount (TList i t) = Mult i (wireCount t)
  wireCount (TIForall _ _ _ i) = i
  wireCount (TVar _) = error "Cannot count wires of a type variable"

-- PQR types are amenable to the notion of well-formedness with respect to an index context
instance HasIndex Type where
  ifv :: Type -> Set IndexVariableId
  ifv TUnit = Set.empty
  ifv (TWire _) = Set.empty
  ifv (TPair t1 t2) = ifv t1 `Set.union` ifv t2
  ifv (TCirc i _ _) = ifv i
  ifv (TArrow typ1 typ2 i j) = ifv typ1 `Set.union` ifv typ2 `Set.union` ifv i `Set.union` ifv j
  ifv (TBang typ) = ifv typ
  ifv (TList i typ) = ifv i `Set.union` ifv typ
  ifv (TVar _) = error "unimplemented"
  ifv (TIForall id typ i j) = Set.delete id (ifv typ `Set.union` ifv i `Set.union` ifv j)
  isub :: Index -> IndexVariableId -> Type -> Type
  isub _ _ TUnit = TUnit
  isub _ _ (TWire wtype) = TWire wtype
  isub i id (TPair t1 t2) = TPair (isub i id t1) (isub i id t2)
  isub i id (TCirc j inBtype outBtype) = TCirc (isub i id j) inBtype outBtype -- Bundle types have no free variables
  isub i id (TArrow typ1 typ2 j k) = TArrow (isub i id typ1) (isub i id typ2) (isub i id j) (isub i id k)
  isub i id (TBang typ) = TBang (isub i id typ)
  isub i id (TList j typ) = TList (isub i id j) (isub i id typ)
  isub _ _ tv@(TVar _) = error "unimplemented"
  isub i id (TIForall id' typ j e) | id == id' = TIForall id' typ j e
                                   | otherwise = TIForall id' (isub i id typ) (isub i id j) (isub i id e)

-- Returns True iff the given type is linear
isLinear :: Type -> Bool
isLinear TUnit = False
isLinear (TWire _) = True
isLinear (TPair typ1 typ2) = isLinear typ1 && isLinear typ2
isLinear (TCirc {}) = False
isLinear (TArrow {}) = True
isLinear (TBang _) = False
isLinear (TList _ typ) = isLinear typ
isLinear (TVar _) = True
isLinear (TIForall _ typ _ i) = isLinear typ && checkEq i (Number 0) --TODO I really don't like this

-- Turns a suitable PQR type into an identical bundle type
toBundleType :: Type -> Maybe BundleType
toBundleType TUnit = Just BTUnit
toBundleType (TWire wtype) = Just $ BTWire wtype
toBundleType (TPair typ1 typ2) = do
  btype1 <- toBundleType typ1
  btype2 <- toBundleType typ2
  return $ BTPair btype1 btype2
toBundleType _ = Nothing

--- SUBSTITUTION ---------------------------------------------------------------------------------

type TypeSubstitution = Map TVarId Type

-- tfv t Returns the free type variables occurring in t
tfv :: Type -> Set TVarId
tfv TUnit = Set.empty
tfv (TWire _) = Set.empty
tfv (TPair t1 t2) = tfv t1 `Set.union` tfv t2
tfv (TCirc {}) = Set.empty
tfv (TArrow t1 t2 _ _) = tfv t1 `Set.union` tfv t2
tfv (TBang t) = tfv t
tfv (TList _ t) = tfv t
tfv (TVar id) = Set.singleton id
tfv (TIForall _ t _ _) = tfv t

-- tsub sub t applies the type substitution sub to the type t
tsub :: TypeSubstitution -> Type -> Type
tsub _ TUnit = TUnit
tsub _ typ@(TWire _) = typ
tsub sub (TPair t1 t2) = TPair (tsub sub t1) (tsub sub t2)
tsub _ typ@(TCirc {}) = typ
tsub sub (TArrow typ1 typ2 i j) = TArrow (tsub sub typ1) (tsub sub typ2) i j
tsub sub (TBang typ) = TBang (tsub sub typ)
tsub sub (TList i typ) = TList i (tsub sub typ)
tsub sub typ@(TVar id) = Map.findWithDefault typ id sub
tsub sub (TIForall i typ _ _) = error "unimplemented"

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
mgtu TUnit TUnit = return Map.empty
mgtu (TWire wt1) (TWire wt2) | wt1 == wt2 = return Map.empty
mgtu (TPair t1 t2) (TPair t1' t2') = do
  sub1 <- mgtu t1 t1'
  sub2 <- mgtu (tsub sub1 t2) (tsub sub1 t2')
  return $ compose sub2 sub1
mgtu (TCirc i inBtype outBtype) (TCirc i' inBtype' outBtype') | checkEq i i' && inBtype == inBtype' && outBtype == outBtype' = return Map.empty
mgtu (TArrow typ1 typ2 i j) (TArrow typ1' typ2' i' j') | checkLeq i i' && checkEq j j' = do
  sub1 <- mgtu typ1 typ1'
  sub2 <- mgtu (tsub sub1 typ2) (tsub sub1 typ2')
  return $ compose sub2 sub1
mgtu (TBang typ) (TBang typ') = mgtu typ typ'
mgtu (TList i typ) (TList i' typ') | checkEq i i' = mgtu typ typ'
mgtu (TIForall id typ i j) (TIForall id' typ' i' j') | id == id' && checkLeq i i' && checkEq j j' = mgtu typ typ' --TODO alpha conversion
mgtu _ _ = Nothing