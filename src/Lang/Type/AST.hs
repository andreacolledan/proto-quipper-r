{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}

module Lang.Type.AST (
  Type(..),
  TVarId,
  isLinear,
  toBundleType,
  fromBundleType
) where

import Bundle.AST ( BundleType (..), WireType, Wide(..) )
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
  wireCount (TList (Number 0) _) = Number 0
  wireCount (TList i t) = Mult i (wireCount t)
  wireCount (TIForall _ _ _ i) = i
  wireCount (TVar _) = error "Cannot count wires of a type variable"

-- PQR types are amenable to the notion of well-formedness with respect to an index context
instance HasIndex Type where
  iv :: Type -> Set IndexVariableId
  iv TUnit = Set.empty
  iv (TWire _) = Set.empty
  iv (TPair t1 t2) = iv t1 `Set.union` iv t2
  iv (TCirc i _ _) = iv i
  iv (TArrow typ1 typ2 i j) = iv typ1 `Set.union` iv typ2 `Set.union` iv i `Set.union` iv j
  iv (TBang typ) = iv typ
  iv (TList i typ) = iv i `Set.union` iv typ
  iv (TVar _) = Set.empty
  iv (TIForall id typ i j) = Set.insert id (iv typ `Set.union` iv i `Set.union` iv j)
  ifv :: Type -> Set IndexVariableId
  ifv TUnit = Set.empty
  ifv (TWire _) = Set.empty
  ifv (TPair t1 t2) = ifv t1 `Set.union` ifv t2
  ifv (TCirc i _ _) = ifv i
  ifv (TArrow typ1 typ2 i j) = ifv typ1 `Set.union` ifv typ2 `Set.union` ifv i `Set.union` ifv j
  ifv (TBang typ) = ifv typ
  ifv (TList i typ) = ifv i `Set.union` ifv typ
  ifv (TVar _) = Set.empty
  ifv (TIForall id typ i j) = Set.delete id (ifv typ `Set.union` ifv i `Set.union` ifv j)
  isub :: Index -> IndexVariableId -> Type -> Type
  isub _ _ TUnit = TUnit
  isub _ _ (TWire wtype) = TWire wtype
  isub i id (TPair t1 t2) = TPair (isub i id t1) (isub i id t2)
  isub i id (TCirc j inBtype outBtype) = TCirc (isub i id j) inBtype outBtype -- Bundle types have no free variables
  isub i id (TArrow typ1 typ2 j k) = TArrow (isub i id typ1) (isub i id typ2) (isub i id j) (isub i id k)
  isub i id (TBang typ) = TBang (isub i id typ)
  isub i id (TList j typ) = TList (isub i id j) (isub i id typ)
  isub _ _ (TVar a) = TVar a
  isub i id (TIForall id' typ j k) = let
    id'' = fresh id' [IndexVariable id, i, j, k]
    id''' = fresh id'' [typ] --must do this in two steps since typ cannot be put in the same list above
    in TIForall id''' (isub i id . isub (IndexVariable id''') id' $ typ) (isub i id . isub (IndexVariable id''') id' $ j) (isub i id . isub (IndexVariable id''') id' $ k)

-- Returns True iff the given type is linear
isLinear :: Type -> Bool
isLinear TUnit = False
isLinear (TWire _) = True
isLinear (TPair typ1 typ2) = isLinear typ1 && isLinear typ2
isLinear (TCirc {}) = False
isLinear (TArrow {}) = True
isLinear (TBang _) = False
isLinear (TList i typ)  | checkEq i (Number 0) = False  --TODO I really don't like this
                        | otherwise = isLinear typ
isLinear (TVar _) = False --Variables are only used in the pre-processing stage, so we are permissive here
isLinear (TIForall _ typ _ i) = isLinear typ && checkEq i (Number 0) --TODO I really don't like this

-- Turns a suitable PQR type into an identical bundle type
toBundleType :: Type -> Maybe BundleType
toBundleType TUnit = Just BTUnit
toBundleType (TWire wtype) = Just $ BTWire wtype
toBundleType (TPair typ1 typ2) = do
  btype1 <- toBundleType typ1
  btype2 <- toBundleType typ2
  return $ BTPair btype1 btype2
toBundleType (TVar id) = Just $ BTVar id
toBundleType (TList i typ) = do
  btype <- toBundleType typ
  return $ BTList i btype
toBundleType _ = Nothing

-- fromBundleType bt returns the PQR type equivalent to bt
fromBundleType :: BundleType -> Type
fromBundleType BTUnit = TUnit
fromBundleType (BTWire wtype) = TWire wtype
fromBundleType (BTPair b1 b2) = TPair (fromBundleType b1) (fromBundleType b2)
fromBundleType (BTList i b) = TList i (fromBundleType b)
fromBundleType (BTVar id) = TVar id