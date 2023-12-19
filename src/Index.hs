{-# LANGUAGE FlexibleInstances #-}
module Index where
import Data.Set (Set)

type IndexVariableId = String

data Index
    = IndexVariable IndexVariableId
    | Number Int
    | Plus Index Index
    deriving Show

-- Corresponds to Θ in the paper
type IndexContext = Set IndexVariableId

class Indexed a where
    wellFormed :: IndexContext -> a -> Bool

instance (Traversable t, Indexed a) => Indexed (t a) where
    wellFormed context x = let wellFormednesses = wellFormed context <$> x in and wellFormednesses

instance Indexed Index where
    wellFormed context (IndexVariable id) = id `elem` context
    wellFormed _ (Number _) = True
    wellFormed context (Plus i j) = wellFormed context i && wellFormed context j

-- We only compare number indices for now
instance Eq Index where
    (Number n) == (Number m) = n == m
    _ == _ = False

instance Ord Index where
    (Number n) <= (Number m) = n <= m
    _ <= _ = False