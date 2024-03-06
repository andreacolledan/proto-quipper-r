{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Index.AST(
    Index(..),
    IndexVariableId,
    IndexContext,
    HasIndex(..),
    Constraint(..),
    IRel(..),
    emptyictx,
    fresh
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

emptyictx :: IndexContext
emptyictx = Set.empty

-- The class of datatypes that bear indices. They can
--  - be checked for well-formedness with respect to an index context
--  - have an index variable within them replaced by an index
class HasIndex a where
    iv :: a -> Set IndexVariableId
    ifv :: a -> Set IndexVariableId
    isub :: Index -> IndexVariableId -> a -> a

wellFormed :: HasIndex a => IndexContext -> a -> Bool
wellFormed theta x = ifv x `Set.isSubsetOf` theta

instance HasIndex Index where
    iv :: Index -> Set IndexVariableId
    iv (IndexVariable id) = Set.singleton id
    iv (Number _) = Set.empty
    iv (Plus i j) = iv i `Set.union` iv j
    iv (Max i j) = iv i `Set.union` iv j
    iv (Mult i j) = iv i `Set.union` iv j
    iv (Minus i j) = iv i `Set.union` iv j
    iv (Maximum id i j) = Set.insert id (iv i `Set.union` iv j)
    ifv :: Index -> Set IndexVariableId
    ifv (IndexVariable id) = Set.singleton id
    ifv (Number _) = Set.empty
    ifv (Plus i j) = ifv i `Set.union` ifv j
    ifv (Max i j) = ifv i `Set.union` ifv j
    ifv (Mult i j) = ifv i `Set.union` ifv j
    ifv (Minus i j) = ifv i `Set.union` ifv j
    ifv (Maximum id i j) = Set.delete id (ifv i `Set.union` ifv j)
    isub :: Index -> IndexVariableId -> Index -> Index
    isub _ _ (Number n) = Number n
    isub i id j@(IndexVariable id') = if id == id' then i else j
    isub i id (Plus j k) = Plus (isub i id j) (isub i id k)
    isub i id (Max j k) = Max (isub i id j) (isub i id k)
    isub i id (Mult j k) = Mult (isub i id j) (isub i id k)
    isub i id (Minus j k) = Minus (isub i id j) (isub i id k)
    isub i id (Maximum id' j k) = let id'' = fresh id' [IndexVariable id, i, k] in
      Maximum id'' (isub i id j) (isub i id . isub (IndexVariable id'') id' $ k)

-- fresh id ids checks if id occurs (free or bound) in the list of indexed terms xs
-- If it does not, id is returned, otherwise, a fresh variable name is returned.
fresh :: (HasIndex a) => IndexVariableId -> [a] -> IndexVariableId
fresh id xs = 
  let toavoid = Set.unions $ iv <$> xs in
  head $ filter (`Set.notMember` toavoid) $ id : [id ++ show n | n <- [0..]]

-- Natural lifting of well-formedness to traversable data structures
instance (Traversable t, HasIndex a) => HasIndex (t a) where
    iv :: t a -> Set IndexVariableId
    iv x = let ivets = iv <$> x in foldr Set.union Set.empty ivets
    ifv :: t a -> Set IndexVariableId
    ifv x = let ifvets = ifv <$> x in foldr Set.union Set.empty ifvets
    isub :: Index -> IndexVariableId -> t a -> t a
    isub i id x = isub i id <$> x

-- Allowed relations between indices

data IRel = Eq | Leq
    deriving (Show, Eq)

instance Pretty IRel where
    pretty Eq = "="
    pretty Leq = "≤"

data Constraint = Constraint IRel Index Index
    deriving (Show, Eq)

instance Pretty Constraint where
    pretty (Constraint rel i j) = pretty i ++ " " ++ pretty rel ++ " " ++ pretty j
