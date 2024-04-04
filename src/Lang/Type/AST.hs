{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module Lang.Type.AST
  ( Type (..),
    TVarId,
    isLinear,
    toBundleType,
    fromBundleType,
  )
where

import Bundle.AST (BundleType (..), Wide (..), WireType)
import qualified Data.HashSet as Set
import Index.AST
import PrettyPrinter
import Data.List (intercalate)

--- TYPE SYNTAX MODULE ---------------------------------------------------------------------------------------
---
--- This module defines the abstract syntax of PQR types.
--- The syntax is almost identical to the one in the paper, with the exception of the introduction of
--- type variables (used internally) and dependent function types (which internalize the index
--- meta-theoretical results in the paper).
-------------------------------------------------------------------------------------------------------------

type TVarId = String

-- Fig. 8
-- | The datatype of PQR types
data Type
  = TUnit                                     -- Unit type        : ()
  | TWire WireType                            -- Wire type        : Bit | Qubit
  | TTensor [Type]                            -- Tensor type      : (t1, t2, ...)
  | TCirc Index BundleType BundleType         -- Circuit type     : Circ[i](bt1, vt2)
  | TArrow Type Type Index Index              -- Function type    : t1 -o[i,j] t2
  | TBang Type                                -- Bang type        : !t
  | TList Index Type                          -- List type        : TList[i] t
  | TVar TVarId                               -- Type variable    : 
  | TIForall IndexVariableId Type Index Index -- Dep. fun. type   : i ->[i,j] t
  deriving (Show, Eq)

instance Pretty Type where
  pretty TUnit = "()"
  pretty (TWire wt) = pretty wt
  pretty (TTensor ts) = "(" ++ intercalate ", " (map pretty ts) ++ ")"
  pretty (TCirc i inBtype outBtype) = "Circ [" ++ pretty i ++ "] (" ++ pretty inBtype ++ ", " ++ pretty outBtype ++ ")"
  pretty (TArrow typ1 typ2 i j) = "(" ++ pretty typ1 ++ " -o[" ++ pretty i ++ ", " ++ pretty j ++ "] " ++ pretty typ2 ++ ")"
  pretty (TBang typ) = "!" ++ pretty typ
  pretty (TList i typ) = "List[" ++ pretty i ++ "] " ++ pretty typ
  pretty (TVar id) = id
  pretty (TIForall id typ i j) = "(" ++ id ++ " ->[" ++ pretty i ++ ", " ++ pretty j ++ "] " ++ pretty typ ++ ")"

-- Def. 2 (Wire Count)
-- PQR types are amenable to wire counting
instance Wide Type where
  wireCount TUnit = Number 0
  wireCount (TWire _) = Number 1
  wireCount (TTensor ts) = foldl Plus (Number 0) (map wireCount ts)
  wireCount (TCirc {}) = Number 0
  wireCount (TArrow _ _ _ i) = i
  wireCount (TBang _) = Number 0
  wireCount (TList (Number 0) _) = Number 0
  wireCount (TList i t) = Mult i (wireCount t)
  wireCount (TIForall _ _ _ i) = i
  wireCount (TVar _) = error "Cannot count wires of a type variable"

-- PQR types are amenable to the notion of well-formedness with respect to an index context
instance HasIndex Type where
  iv :: Type -> Set.HashSet IndexVariableId
  iv TUnit = Set.empty
  iv (TWire _) = Set.empty
  iv (TTensor ts) = foldr (Set.union . iv) Set.empty ts
  iv (TCirc i _ _) = iv i
  iv (TArrow typ1 typ2 i j) = iv typ1 `Set.union` iv typ2 `Set.union` iv i `Set.union` iv j
  iv (TBang typ) = iv typ
  iv (TList i typ) = iv i `Set.union` iv typ
  iv (TVar _) = Set.empty
  iv (TIForall id typ i j) = Set.insert id (iv typ `Set.union` iv i `Set.union` iv j)
  ifv :: Type -> Set.HashSet IndexVariableId
  ifv TUnit = Set.empty
  ifv (TWire _) = Set.empty
  ifv (TTensor ts) = foldr (Set.union . ifv) Set.empty ts
  ifv (TCirc i _ _) = ifv i
  ifv (TArrow typ1 typ2 i j) = ifv typ1 `Set.union` ifv typ2 `Set.union` ifv i `Set.union` ifv j
  ifv (TBang typ) = ifv typ
  ifv (TList i typ) = ifv i `Set.union` ifv typ
  ifv (TVar _) = Set.empty
  ifv (TIForall id typ i j) = Set.delete id (ifv typ `Set.union` ifv i `Set.union` ifv j)
  isub :: Index -> IndexVariableId -> Type -> Type
  isub _ _ TUnit = TUnit
  isub _ _ (TWire wtype) = TWire wtype
  isub i id (TTensor ts) = TTensor (map (isub i id) ts)
  isub i id (TCirc j inBtype outBtype) = TCirc (isub i id j) inBtype outBtype -- Bundle types have no free variables
  isub i id (TArrow typ1 typ2 j k) = TArrow (isub i id typ1) (isub i id typ2) (isub i id j) (isub i id k)
  isub i id (TBang typ) = TBang (isub i id typ)
  isub i id (TList j typ) = TList (isub i id j) (isub i id typ)
  isub _ _ (TVar a) = TVar a
  isub i id (TIForall id' typ j k) =
    let id'' = fresh id' [IndexVariable id, i, j, k]
        id''' = fresh id'' [typ] -- must do this in two steps since typ cannot be put in the same list above
     in TIForall id''' (isub i id . isub (IndexVariable id''') id' $ typ) (isub i id . isub (IndexVariable id''') id' $ j) (isub i id . isub (IndexVariable id''') id' $ k)

-- | @isLinear t@ returns 'True' @t@ is a linear type, and 'False' otherwise
isLinear :: Type -> Bool
isLinear TUnit = False
isLinear (TWire _) = True
isLinear (TTensor ts) = any isLinear ts
isLinear (TCirc {}) = False
isLinear (TArrow {}) = True
isLinear (TBang _) = False
isLinear (TList (Number 0) _) = False  -- Empty lists can be discarded
isLinear (TList _ typ) = isLinear typ
isLinear (TVar _) = False -- Variables are only used in the pre-processing stage, so we are permissive here
isLinear (TIForall _ typ _ _) = isLinear typ

-- | Turns a suitable PQR 'Type' into an identical 'BundleType'.
-- @toBundleType t@ returns @'Just' bt@ if PQR 'Type' @t@ is also a bundle type, and 'Nothing' otherwise
toBundleType :: Type -> Maybe BundleType
toBundleType TUnit = Just BTUnit
toBundleType (TWire wtype) = Just $ BTWire wtype
toBundleType (TTensor ts) = do
  bts <- mapM toBundleType ts
  return $ BTTensor bts
toBundleType (TVar id) = Just $ BTVar id
toBundleType (TList i typ) = do
  btype <- toBundleType typ
  return $ BTList i btype
toBundleType _ = Nothing

-- | Turns a 'BundleType' into an identical PQR 'Type'. 
-- @fromBundleType bt@ returns the PQR 'Type' corresponding to bundle type @bt@
fromBundleType :: BundleType -> Type
fromBundleType BTUnit = TUnit
fromBundleType (BTWire wtype) = TWire wtype
fromBundleType (BTTensor bs) = TTensor (map fromBundleType bs)
fromBundleType (BTList i b) = TList i (fromBundleType b)
fromBundleType (BTVar id) = TVar id