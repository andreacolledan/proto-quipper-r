{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Inference.Unification where
import Data.Map
import Data.Set (Set)


--- GENERIC OPENNESS -----------------------------------------------------------------------------

-- The class of datatypes that may contain variable names of type k
class (Eq k, Ord k) => WithFreeVars k a where
    freeVars :: a -> Set k

-- Every traversable collection of WithFreeVars elements is itself WithFreeVars
instance (Traversable t, WithFreeVars k a) => WithFreeVars k (t a) where
    freeVars = foldMap freeVars


--- GENERIC SUBSTITUTION --------------------------------------------------------------------------

-- Define substitutions of a as maps from string identifiers to a
type Substitution k a = Map k a

emptySub :: Substitution k a
emptySub = empty

singSub :: k -> a -> Substitution k a
singSub = singleton

-- The class of datatypes that are amenable to substitution of values of type a for placeholders of type k
-- Substitutable k a b means that b may contain placeholders of type k that stand for values of type a
-- and that we can substitute values of type a for those placeholders
class WithFreeVars k b => Substitutable k a b  where
    apply :: Substitution k a -> b -> b

instance (Traversable t, Substitutable k a b) => Substitutable k a (t b) where
    apply sub = fmap (apply sub)

-- substitution composition under the logic sub1(sub2(x)) = (sub 1(sub 2))(x)
compose :: Substitutable k a a => Substitution k a -> Substitution k a -> Substitution k a
compose sub1 sub2 = fmap (apply sub1) sub2 `union` sub1


--- GENERIC UNIFICATION ------------------------------------------------------------------------------

-- The class of datatypes that are amenable to unification
-- mgu computes the most general unifier of two values, if it exists
class (Substitutable k a b) => Unifiable k a b where
    mgu :: b -> b -> Maybe (Substitution k a)