{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module AST.Index(
    Index(..),
    IndexVariableId,
    IndexContext,
    Indexed(..),
    Constraint(..)
) where

import Data.Set (Set)
import qualified Data.Set as Set
import PrettyPrinter


type IndexVariableId = String

-- Syntax of indices: arithmetic expressions over natural numbers and index variables
-- (fig. 8)
data Index
    = IndexVariable IndexVariableId         -- id
    | Number Int                            -- n
    | Plus Index Index                      -- i + j
    | Max Index Index                       -- max(i, j)
    | Mult Index Index                      -- i * j
    | Minus Index Index                     -- i - j
    | Maximum IndexVariableId Index Index   -- max[id < i] j
    deriving (Show, Eq)

instance Pretty Index where
    pretty (IndexVariable id) = id
    pretty (Number n) = show n
    pretty (Plus i j) = "(" ++ pretty i ++ " + " ++ pretty j ++ ")"
    pretty (Max i j) = "max(" ++ pretty i ++ ", " ++ pretty j ++ ")"
    pretty (Mult i j) = "(" ++ pretty i ++ " * " ++ pretty j ++ ")"
    pretty (Minus i j) = "(" ++ pretty i ++ " - " ++ pretty j ++ ")"
    pretty (Maximum id i j) = "max[" ++ id ++ " < " ++ pretty i ++ "] " ++ pretty j


-- Corresponds to Θ in the paper
type IndexContext = Set IndexVariableId

-- The class of datatypes that bear indices. They can
--  - be checked for well-formedness with respect to an index context
--  - have an index variable within them replaced by an index
class Indexed a where
    freeVariables :: a -> Set IndexVariableId
    wellFormed :: IndexContext -> a -> Bool
    isub :: Index -> IndexVariableId -> a -> a

instance Indexed Index where
    freeVariables :: Index -> Set IndexVariableId
    freeVariables (IndexVariable id) = Set.singleton id
    freeVariables (Number _) = Set.empty
    freeVariables (Plus i j) = freeVariables i `Set.union` freeVariables j
    freeVariables (Max i j) = freeVariables i `Set.union` freeVariables j
    freeVariables (Mult i j) = freeVariables i `Set.union` freeVariables j
    freeVariables (Minus i j) = freeVariables i `Set.union` freeVariables j
    freeVariables (Maximum id i j) = Set.delete id (freeVariables i `Set.union` freeVariables j)
    wellFormed :: IndexContext -> Index -> Bool
    wellFormed context (IndexVariable id) = id `elem` context
    wellFormed _ (Number _) = True
    wellFormed context (Plus i j) = wellFormed context i && wellFormed context j
    wellFormed context (Max i j) = wellFormed context i && wellFormed context j
    wellFormed context (Mult i j) = wellFormed context i && wellFormed context j
    wellFormed context (Minus i j) = wellFormed context i && wellFormed context j
    wellFormed context (Maximum id i j) =
        notElem id context
        && wellFormed context i
        && wellFormed (Set.insert id context) j
    isub :: Index -> IndexVariableId -> Index -> Index
    isub _ _ (Number n) = Number n
    isub i id j@(IndexVariable id') = if id == id' then i else j
    isub i id (Plus j k) = Plus (isub i id j) (isub i id k)
    isub i id (Max j k) = Max (isub i id j) (isub i id k)
    isub i id (Mult j k) = Mult (isub i id j) (isub i id k)
    isub i id (Minus j k) = Minus (isub i id j) (isub i id k)
    isub i id (Maximum id' j k) = let j' = isub i id j in if id == id' then Maximum id' j' k else Maximum id' j' (isub i id k)

-- Natural lifting of well-formedness to traversable data structures
instance (Traversable t, Indexed a) => Indexed (t a) where
    freeVariables :: t a -> Set IndexVariableId
    freeVariables x = let freeVariableSets = freeVariables <$> x in foldr Set.union Set.empty freeVariableSets
    wellFormed :: IndexContext -> t a -> Bool
    wellFormed context x = let wellFormednesses = wellFormed context <$> x in and wellFormednesses
    isub :: Index -> IndexVariableId -> t a -> t a
    isub i id x = isub i id <$> x

-- Allowed relations between indices
data Constraint
    = Eq Index Index
    | Leq Index Index
    deriving Show

instance Pretty Constraint where
    pretty (Eq i j) = pretty i ++ " = " ++ pretty j
    pretty (Leq i j) = pretty i ++ " ≤ " ++ pretty j
