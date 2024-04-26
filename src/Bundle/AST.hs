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
    BTVarId,
    BundleTypeSubstitution,
    compose,
    mgbtu,
    btsub,
    btfv
  )
where

import Index.AST
import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set
import PrettyPrinter
import Index.Semantics
import Control.Exception (assert)
import Data.List (intercalate)
import Control.Monad
import Data.Foldable

--- LANGUAGE ---------------------------------------------------------------------------------

type LabelId = String

-- Basic wire types
data WireType
  = Bit
  | Qubit
  deriving (Eq, Show)

instance Pretty WireType where
  pretty Bit = "Bit"
  pretty Qubit = "Qubit"

-- Wire Bundle Syntax (Fig. 9)
data Bundle
  = UnitValue                   -- Unit value       : ()
  | Label LabelId               -- Label            : l, k, t, ...
  | Tuple [Bundle]              -- Tuple             : (b1, b2, ...)
  | Nil                         -- Empty list       : []
  | Cons Bundle Bundle          -- Cons             : b1:b2
  deriving (Eq, Show)

instance Pretty Bundle where
  pretty UnitValue = "()"
  pretty (Label id) = id
  pretty (Tuple bs) = "(" ++ intercalate ", " (map pretty bs) ++ ")"
  pretty Nil = "[]"
  pretty (Cons b1 b2) = "(" ++ pretty b1 ++ ":" ++ pretty b2 ++ ")"



--- BUNDLE TYPES ---------------------------------------------------------------------------------

type BTVarId = String

-- Bundle Type Syntax (Fig. 9)
data BundleType
  = BTUnit
  | BTWire WireType
  | BTTensor [BundleType]
  | BTList Index BundleType
  | BTVar BTVarId
  deriving (Eq, Show)

instance Pretty BundleType where
  pretty BTUnit = "()"
  pretty (BTWire Bit) = "Bit"
  pretty (BTWire Qubit) = "Qubit"
  pretty (BTTensor bs) = "(" ++ intercalate ", " (map pretty bs) ++ ")"
  pretty (BTList i b) = "List[" ++ pretty i ++ "] " ++ pretty b
  pretty (BTVar id) = id

-- Bundle types are index-bearing syntactical objects
instance HasIndex BundleType where
  iv :: BundleType -> Set.HashSet IndexVariableId
  iv BTUnit = Set.empty
  iv (BTWire _) = Set.empty
  iv (BTTensor bs) = foldr (Set.union . iv) Set.empty bs
  iv (BTList i b) = assert (null (iv i)) $ iv i `Set.union` iv b
  iv (BTVar _) = Set.empty
  ifv :: BundleType -> Set.HashSet IndexVariableId
  ifv BTUnit = Set.empty
  ifv (BTWire _) = Set.empty
  ifv (BTTensor bs) = foldr (Set.union . ifv) Set.empty bs
  ifv (BTList i b) = assert (null (ifv i)) $ ifv i `Set.union` ifv b
  ifv (BTVar _) = Set.empty
  isub :: Index -> IndexVariableId -> BundleType -> BundleType
  isub i id (BTList j b) = BTList (isub i id j) (isub i id b)
  isub i id (BTTensor bs) = BTTensor (map (isub i id) bs)
  isub _ _ b = b



--- SUBSTITUTION ---------------------------------------------------------------------------------

type BundleTypeSubstitution = Map.HashMap BTVarId BundleType

-- btfv bt Returns the free bundle type variables occurring in bt
btfv :: BundleType -> Set.HashSet BTVarId
btfv BTUnit = Set.empty
btfv (BTWire _) = Set.empty
btfv (BTTensor bs) = foldr (Set.union . btfv) Set.empty bs
btfv (BTList _ b) = btfv b
btfv (BTVar id) = Set.singleton id

-- btsub sub bt applies the bundle type substitution sub to the bundle type bt
btsub :: BundleTypeSubstitution -> BundleType -> BundleType
btsub _ BTUnit = BTUnit
btsub _ (BTWire wt) = BTWire wt
btsub sub (BTTensor bs) = BTTensor (map (btsub sub) bs)
btsub sub (BTList i b) = BTList i (btsub sub b)
btsub sub bt@(BTVar id) = Map.findWithDefault bt id sub

-- mgbtu bt1 bt2 attempts to find a most general bundle type substitution sub such that sub(bt1) = bt2
-- If successful, it returns Just sub, otherwise it returns Nothing
mgbtu :: BundleType -> BundleType -> Maybe BundleTypeSubstitution
mgbtu (BTVar id) b = assignVar id b
mgbtu b (BTVar id) = assignVar id b
mgbtu BTUnit BTUnit = return Map.empty
mgbtu (BTWire wt1) (BTWire wt2) | wt1 == wt2 = return Map.empty
mgbtu (BTTensor bts) (BTTensor bts')
  | length bts == length bts' = do
    when (length bts < 2) $ error "Internal error: Tensors must have at least two elements"
    subs <- zipWithM mgbtu bts bts'
    return $ fold subs
  | otherwise = Nothing
mgbtu (BTList _ b) (BTList _ b') = mgbtu b b'
mgbtu _ _ = Nothing

-- assignVar id bt returns the singleton substitution id |-> bt
-- if unnecessary (id != bt) it returns the empty substitution
-- if impossible (id occurs in bt) it returns Nothing
assignVar :: BTVarId -> BundleType -> Maybe BundleTypeSubstitution
assignVar id (BTVar id') | id == id' = return Map.empty
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
  wireCount BTUnit = Number 0
  wireCount (BTWire wtype) = wireCount wtype
  wireCount (BTTensor bs) = foldl Plus (Number 0) (wireCount <$> bs)
  wireCount (BTList i b) = Mult i (wireCount b)
  wireCount (BTVar _) = error "wireCount: encountered type variable"

-- Any traversable structure of elements with wire counts can be wire counted
-- Its wire count is the sum of the wire counts of its elements
instance (Traversable t, Wide a) => Wide (t a) where
  wireCount x = let wirecounts = wireCount <$> x in foldr Plus (Number 0) wirecounts



--- SUBTYPING ---------------------------------------------------------------------------------

-- Θ ⊢ t1 <: t2 (Figure 15, restricted to bundle types)
-- Note that due to their nature, subtyping on bundle types collapses to type equality
isBundleSubtype :: BundleType -> BundleType -> Bool
isBundleSubtype BTUnit BTUnit = True
isBundleSubtype (BTWire wtype1) (BTWire wtype2) = wtype1 == wtype2
isBundleSubtype (BTTensor bs) (BTTensor bs')
  | length bs == length bs' = and $ zipWith isBundleSubtype bs bs'
  | otherwise = False
isBundleSubtype (BTList i b) (BTList i' b') = checkClosedEq i i' && isBundleSubtype b' b
isBundleSubtype _ _ = False
