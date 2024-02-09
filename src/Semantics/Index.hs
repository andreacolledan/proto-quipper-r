module Semantics.Index where

import qualified Data.Set as Set
import AST.Index
import Solving.CVC5

-- Θ ⊨ i = j (figs. 10,15)
checkEq :: Index -> Index -> Bool
checkEq i j = case (simplify i,simplify j) of
    (i',j') | i' == j' -> True                                          -- identical indices are equal
    (Number n, Number m) -> n == m                                      -- number indices are equal iff their values are equal
    (IndexVariable id, IndexVariable id') -> id == id'                  -- variables are equal if they are the same name
    (i',j') -> let theta = freeVariables i' `Set.union` freeVariables j'-- in all other cases, query the SMT solver
        in querySMTWithContext theta $ Eq i' j'

-- Θ ⊨ i ≤ j (figs. 12,15)
checkLeq :: Index -> Index -> Bool
checkLeq i j = case (simplify i,simplify j) of
    (i',j') | i' == j' -> True                                          -- identical indices are equal
    (Number n, Number m) -> n <= m                                      -- number indices are lesser-or-equal iff their values are lesser-or-equal
    (i',j') -> let theta = freeVariables i' `Set.union` freeVariables j'-- in all other cases, query the SMT solver
        in querySMTWithContext theta $ Leq i' j'



nonDecreasingIn :: Index -> IndexVariableId -> Bool
nonDecreasingIn (IndexVariable _) _ = True
nonDecreasingIn (Number _) _ = True
nonDecreasingIn (Plus i j) id = i `nonDecreasingIn` id && j `nonDecreasingIn` id
nonDecreasingIn (Max i j) id = i `nonDecreasingIn` id && j `nonDecreasingIn` id
nonDecreasingIn (Mult i j) id = i `nonDecreasingIn` id && j `nonDecreasingIn` id
nonDecreasingIn (Minus i j) id = i `nonDecreasingIn` id && j `nonIncreasingIn` id
nonDecreasingIn (Maximum id' i j) id | id /= id' =
    i `nonDecreasingIn` id && j `nonDecreasingIn` id
    || i `nonDecreasingIn` id && j `nonDecreasingIn` id'
nonDecreasingIn _ _ = False

nonIncreasingIn :: Index -> IndexVariableId -> Bool
nonIncreasingIn (IndexVariable id') id = id /= id'
nonIncreasingIn (Number _) _ = True
nonIncreasingIn (Plus i j) id = i `nonIncreasingIn` id && j `nonIncreasingIn` id
nonIncreasingIn (Max i j) id = i `nonIncreasingIn` id && j `nonIncreasingIn` id
nonIncreasingIn (Mult i j) id = i `nonIncreasingIn` id && j `nonIncreasingIn` id
nonIncreasingIn (Minus i j) id = i `nonIncreasingIn` id && j `nonDecreasingIn` id
nonIncreasingIn (Maximum id' i j) id | id /= id' =
    i `nonIncreasingIn` id && j `nonIncreasingIn` id
    || i `nonIncreasingIn` id && j `nonDecreasingIn` id'
nonIncreasingIn _ _ = False

stableIn :: Index -> IndexVariableId -> Bool
stableIn i id = i `nonDecreasingIn` id && i `nonIncreasingIn` id


-- Simplifies an index expression
simplify :: Index -> Index
simplify (Number n) = Number n
simplify (Plus i j) = case (simplify i, simplify j) of
    (Number n, Number m) -> Number (n + m)
    (i',Number 0) -> i'
    (Number 0, j') -> j'
    (i', Minus j' i'') | checkEq i' i'' -> j' --happens very often
    (i',j') -> Plus i' j'
simplify (Max i j) = case (simplify i, simplify j) of
    (Number n, Number m) -> Number (max n m)
    (i',j') | checkEq i' j' -> i'
    (i',Number 0) -> i'
    (Number 0, j') -> j'
    (i',j') -> Max i' j'
simplify (Mult i j) = case (simplify i, simplify j) of
    (Number n, Number m) -> Number (n * m)
    (_,Number 0) -> Number 0
    (Number 0, _) -> Number 0
    (i',Number 1) -> i'
    (Number 1, j') -> j'
    (i',j') -> Mult i' j'
simplify (Minus i j) = case (simplify i, simplify j) of
    (Number n, Number m) -> Number (n - m)
    (i',j') | i' == j' -> Number 0
    (i',Number 0) -> i'
    (Number 0, _) -> Number 0
    (i',j') -> Minus i' j'
simplify (IndexVariable id) = IndexVariable id
simplify (Maximum id i j) = case simplify i of
    -- if upper bound is 0, the range is empty and the maximum defaults to 0
    Number 0 -> Number 0
    -- if the upper bound is known, unroll the maximum into a sequence of binary maxima
    Number n -> let unrolling = foldr1 Max [isub (Number step) id j | step <- [0..n-1]] in simplify unrolling
    -- if the upper bound is unknown, simplify the body of the maximum and...
    i' -> let j' = simplify j in
        -- if the body of does not mention id, then just return the body
        if id `notElem` freeVariables j' then j'
        -- if the body does not increase in i, then return the body at id=0
        else if j' `nonIncreasingIn` id then simplify $ isub (Number 0) id j'
        -- if the body of the maximum does not decrease in i, then return the body at id=i-1
        else if j' `nonDecreasingIn` id then simplify $ isub (Minus i' (Number 1)) id j'
        --otherwise return the simplified term and pray that an SMT solver will figure it out (it won't)
        else Maximum id i' j'

