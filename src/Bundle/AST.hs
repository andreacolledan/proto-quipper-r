{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Bundle.AST
  ( Bundle (..),
    BundleType (..),
    WireType (..),
    LabelId,
    Wide (..),
    isBundleSubtype,
    BundleTypeVariableId,
    BundleTypeSubstitution,
    compose,
    mgbtu,
    btsub,
  )
where

import Index.AST
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import PrettyPrinter
import Index.Semantics
import Control.Exception (assert)

--- LANGUAGE ---------------------------------------------------------------------------------

type LabelId = String

-- Basic wire types
data WireType
  = Bit
  | Qubit
  deriving (Eq, Show)

instance Pretty WireType

-- Wire Bundle Syntax (Fig. 9)
data Bundle
  = UnitValue           -- ()
  | Label LabelId       -- l,k,...
  | Pair Bundle Bundle  -- (b1, b2)
  | Nil                 -- []
  | Cons Bundle Bundle  -- b1:b2
  deriving (Eq, Show)

instance Pretty Bundle where
  pretty UnitValue = "()"
  pretty (Label id) = id
  pretty (Pair b1 b2) = "(" ++ pretty b1 ++ ", " ++ pretty b2 ++ ")"
  pretty Nil = "[]"
  pretty (Cons b1 b2) = "(" ++ pretty b1 ++ ":" ++ pretty b2 ++ ")"



--- BUNDLE TYPES ---------------------------------------------------------------------------------

type BundleTypeVariableId = String

-- Bundle Type Syntax (Fig. 9)
data BundleType
  = UnitType
  | WireType WireType
  | Tensor BundleType BundleType
  | List Index BundleType
  | TypeVariable BundleTypeVariableId
  deriving (Eq, Show)

instance Pretty BundleType where
  pretty UnitType = "Unit"
  pretty (WireType Bit) = "Bit"
  pretty (WireType Qubit) = "Qubit"
  pretty (Tensor b1 b2) = "(" ++ pretty b1 ++ " ⊗ " ++ pretty b2 ++ ")"
  pretty (List i b) = "List[" ++ pretty i ++ "]" ++ pretty b
  pretty (TypeVariable id) = id

-- Bundle types are index-bearing syntactical objects
instance HasIndex BundleType where
  ifv :: BundleType -> IndexContext
  ifv UnitType = Set.empty
  ifv (WireType _) = Set.empty
  ifv (Tensor b1 b2) = ifv b1 `Set.union` ifv b2
  ifv (List i b) = assert (null (ifv i)) $ ifv i `Set.union` ifv b
  ifv (TypeVariable _) = Set.empty
  isub :: Index -> IndexVariableId -> BundleType -> BundleType
  isub _ _ = id -- No index variables in bundle types



--- SUBSTITUTION ---------------------------------------------------------------------------------

type BundleTypeSubstitution = Map BundleTypeVariableId BundleType

-- btfv bt Returns the free bundle type variables occurring in bt
btfv :: BundleType -> Set.Set BundleTypeVariableId
btfv UnitType = Set.empty
btfv (WireType _) = Set.empty
btfv (Tensor b1 b2) = btfv b1 `Set.union` btfv b2
btfv (List _ b) = btfv b
btfv (TypeVariable id) = Set.singleton id

-- btsub sub bt applies the bundle type substitution sub to the bundle type bt
btsub :: BundleTypeSubstitution -> BundleType -> BundleType
btsub _ UnitType = UnitType
btsub _ (WireType wt) = WireType wt
btsub sub (Tensor b1 b2) = Tensor (btsub sub b1) (btsub sub b2)
btsub sub (List i b) = List i (btsub sub b)
btsub sub bt@(TypeVariable id) = Map.findWithDefault bt id sub

-- mgbtu bt1 bt2 attempts to find a most general bundle type substitution sub such that sub(bt1) = bt2
-- If successful, it returns Just sub, otherwise it returns Nothing
mgbtu :: BundleType -> BundleType -> Maybe BundleTypeSubstitution
mgbtu (TypeVariable id) b = assignVar id b
mgbtu b (TypeVariable id) = assignVar id b
mgbtu UnitType UnitType = return Map.empty
mgbtu (WireType wt1) (WireType wt2) | wt1 == wt2 = return Map.empty
mgbtu (Tensor b1 b2) (Tensor b1' b2') = do
    sub1 <- mgbtu b1 b1'
    sub2 <- mgbtu (btsub sub1 b2) (btsub sub1 b2')
    return $ compose sub2 sub1
mgbtu (List _ b) (List _ b') = mgbtu b b'
mgbtu _ _ = Nothing

-- assignVar id bt returns the singleton substitution id |-> bt
-- if unnecessary (id != bt) it returns the empty substitution
-- if impossible (id occurs in bt) it returns Nothing
assignVar :: BundleTypeVariableId -> BundleType -> Maybe BundleTypeSubstitution
assignVar id (TypeVariable id') | id == id' = return Map.empty
assignVar id b | id `Set.member` btfv b = Nothing
assignVar id b = return $ Map.singleton id b

-- compose sub1 sub2 returns the composition of the two substitutions
-- according to sub2 ∘ sub1 = sub1 U (sub1 sub2)
compose :: BundleTypeSubstitution -> BundleTypeSubstitution -> BundleTypeSubstitution
compose sub1 sub2 = Map.union sub1 (Map.map (btsub sub1) sub2)



--- WIRE COUNTING ---------------------------------------------------------------------------------

-- The class of datatypes that can contain wires and are thus amenable to wire counting
-- Def. 2 (Wire Count)
class Wide a where
  wireCount :: a -> Index -- #(•) in the paper

instance Wide WireType where
  wireCount Bit = Number 1
  wireCount Qubit = Number 1

instance Wide BundleType where
  wireCount UnitType = Number 0
  wireCount (WireType wtype) = wireCount wtype
  wireCount (Tensor b1 b2) = Plus (wireCount b1) (wireCount b2)
  wireCount (List i b) = Mult i (wireCount b)
  wireCount (TypeVariable _) = error "wireCount: encountered type variable"

-- Any traversable structure of elements with wire counts can be wire counted
-- Its wire count is the sum of the wire counts of its elements
instance (Traversable t, Wide a) => Wide (t a) where
  wireCount x = let wirecounts = wireCount <$> x in foldr Plus (Number 0) wirecounts



--- SUBTYPING ---------------------------------------------------------------------------------

-- Θ ⊢ t1 <: t2 (Figure 15, restricted to bundle types)
-- Note that due to their nature, subtyping on bundle types collapses to type equality
isBundleSubtype :: BundleType -> BundleType -> Bool
isBundleSubtype UnitType UnitType = True
isBundleSubtype (WireType wtype1) (WireType wtype2) = wtype1 == wtype2
isBundleSubtype (Tensor b1 b2) (Tensor b1' b2') = isBundleSubtype b1' b1 && isBundleSubtype b2' b2
isBundleSubtype (List i b) (List i' b') = checkEq i i' && isBundleSubtype b' b
isBundleSubtype _ _ = False
