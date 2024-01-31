{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module AST.Bundle(
    Bundle(..),
    BundleType(..),
    WireType(..),
    LabelId,
    Wide(..),
    isBundleSubtype,
    BTVarId
) where

import AST.Index
import qualified Data.Set as Set
import PrettyPrinter
import Inference.Unification (WithFreeVars (..), Substitutable (..), Unifiable (..), singSub, emptySub, compose)
import qualified Data.Map as Map

--- LANGUAGE ---------------------------------------------------------------------------------

type LabelId = String

data WireType
    = Bit
    | Qubit
    deriving (Eq, Show)
instance Pretty WireType

-- Wire Bundle Syntax
-- Fig. 9
data Bundle
    = UnitValue             -- *
    | Label LabelId         -- ℓ,k
    | Pair Bundle Bundle    -- (˜l,˜k)
    | Nil                   -- []
    | Cons Bundle Bundle    -- ˜l:˜k
    deriving (Eq, Show)
instance Pretty Bundle where
    pretty UnitValue = "*"
    pretty (Label id) = id
    pretty (Pair b1 b2) = "(" ++ pretty b1 ++ ", " ++ pretty b2 ++ ")"
    pretty Nil = "[]"
    pretty (Cons b1 b2) = "(" ++ pretty b1 ++ ":" ++ pretty b2 ++ ")"


--- BUNDLE TYPES ---------------------------------------------------------------------------------


type BTVarId = String

-- Bundle Type Syntax
-- Fig. 9
data BundleType
    = UnitType
    | WireType WireType
    | Tensor BundleType BundleType
    | List Index BundleType
    | TypeVariable BTVarId
    deriving (Eq, Show)

instance Pretty BundleType where
    pretty UnitType = "Unit"
    pretty (WireType Bit) = "Bit"
    pretty (WireType Qubit) = "Qubit"
    pretty (Tensor b1 b2) = "(" ++ pretty b1 ++ " ⊗ " ++ pretty b2 ++ ")"
    pretty (List i b) = "List[" ++ pretty i ++ "]" ++ pretty b
    pretty (TypeVariable id) = id

instance Indexed BundleType where
    freeVariables :: BundleType -> IndexContext
    freeVariables UnitType = Set.empty
    freeVariables (WireType _) = Set.empty
    freeVariables (Tensor b1 b2) = freeVariables b1 `Set.union` freeVariables b2
    freeVariables (List i b) = freeVariables i `Set.union` freeVariables b
    freeVariables (TypeVariable _) = Set.empty
    wellFormed :: IndexContext -> BundleType -> Bool
    wellFormed _ UnitType = True
    wellFormed _ (WireType _) = True
    wellFormed theta (Tensor b1 b2) = wellFormed theta b1 && wellFormed theta b2
    wellFormed theta (List i b) = wellFormed theta i && wellFormed theta b
    wellFormed _ (TypeVariable _) = True
    isub :: Index -> IndexVariableId -> BundleType -> BundleType
    isub _ _ = id   -- No index variables in bundle types

instance WithFreeVars BTVarId BundleType where
    freeVars UnitType = Set.empty
    freeVars (WireType _) = Set.empty
    freeVars (Tensor b1 b2) = freeVars b1 `Set.union` freeVars b2
    freeVars (List _ b) = freeVars b
    freeVars (TypeVariable id) = Set.singleton id

instance Substitutable BTVarId BundleType BundleType where
    apply _ UnitType = UnitType
    apply _ (WireType wtype) = WireType wtype
    apply sub (Tensor b1 b2) = Tensor (apply sub b1) (apply sub b2)
    apply sub (List i b) = List i (apply sub b)
    apply sub (TypeVariable id) = Map.findWithDefault (TypeVariable id) id sub

instance Unifiable BTVarId BundleType BundleType where
    mgu (TypeVariable id) t = return $ singSub id t
    mgu t (TypeVariable id) = return $ singSub id t
    mgu UnitType UnitType = return emptySub
    mgu (WireType w1) (WireType w2) | w1 == w2 = return emptySub
    mgu (Tensor b1 b2) (Tensor b3 b4) = do
        sub1 <- mgu b1 b3
        sub2 <- mgu (apply sub1 b2) (apply sub1 b4)
        return $ sub2 `compose` sub1
    mgu (List _ b1) (List _ b2) = mgu b1 b2
    mgu _ _ = Nothing


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

--Any traversable structure of elements with wire counts can be wire counted
--Its wire count is the sum of the wire counts of its elements
instance (Traversable t, Wide a) => Wide (t a) where
    wireCount x = let wirecounts = wireCount <$> x in foldr Plus (Number 0) wirecounts


--- SUBTYPING ---------------------------------------------------------------------------------


isBundleSubtype :: BundleType -> BundleType -> Bool
isBundleSubtype UnitType UnitType = True
isBundleSubtype (WireType wtype1) (WireType wtype2) = wtype1 == wtype2
isBundleSubtype (Tensor b1 b2) (Tensor b1' b2') = isBundleSubtype b1' b1 && isBundleSubtype b2' b2
isBundleSubtype (List i b) (List i' b') = checkEq Set.empty i i' && isBundleSubtype b' b
isBundleSubtype _ _ = False
