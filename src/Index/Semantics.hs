module Index.Semantics
  ( simplifyIndex,
    checkEq,
    checkLeq,
  )
where

import Index.AST
import qualified Data.Set as Set
import Solving.CVC5

-- Index semantics in terms of a reduction function
-- simplifyIndex i reduces i as much as possible and returns the result
-- If i is closed, then the result is in the form (Number n) for some n
-- If i is not closed, then some tactics are employed to simplify the expression,
-- but the result may still contain free variables
simplifyIndex :: Index -> Index
simplifyIndex (Number n) = Number n
simplifyIndex (IndexVariable id) = IndexVariable id
simplifyIndex (Plus i j) = case (simplifyIndex i, simplifyIndex j) of
  (Number n, Number m) -> Number (n + m)
  (i', Number 0) -> i' -- zero is right identity
  (Number 0, j') -> j' -- zero is left identity
  --(i', Minus j' i'') | checkEq i' i'' -> j' -- (a + (b - a)) = b     --TODO this is true iff b >= a
  (i', j') -> Plus i' j' -- do not reduce further
simplifyIndex (Max i j) = case (simplifyIndex i, simplifyIndex j) of
  (Number n, Number m) -> Number (max n m)
  (i', j') | checkEq i' j' -> i' -- max is idempotent
  (i', Number 0) -> i' -- zero is right identity
  (Number 0, j') -> j' -- zero is left identity
  (i', j') -> Max i' j' -- do not reduce further
simplifyIndex (Mult i j) = case (simplifyIndex i, simplifyIndex j) of
  (Number n, Number m) -> Number (n * m)
  (_, Number 0) -> Number 0 -- zero is right absorbing
  (Number 0, _) -> Number 0 -- zero is left absorbing
  (i', Number 1) -> i' -- one is right identity
  (Number 1, j') -> j' -- one is left identity
  (i', j') -> Mult i' j' -- do not reduce further
simplifyIndex (Minus i j) = case (simplifyIndex i, simplifyIndex j) of
  (Number n, Number m) -> Number (n - m)
  (i', j') | i' == j' -> Number 0 -- a - a = 0
  (i', Number 0) -> i' -- zero is right identity
  (Number 0, _) -> Number 0 -- zero is left absorbing
  (i', j') -> Minus i' j' -- do not reduce further
simplifyIndex (Maximum id i j) = case simplifyIndex i of
  -- if upper bound is 0, the range is empty and the maximum defaults to 0
  Number 0 -> Number 0
  -- if the upper bound is known, unroll the maximum into a sequence of binary maxima
  Number n ->
    let unrolling = foldr1 Max [isub (Number step) id j | step <- [0 .. n - 1]]
     in simplifyIndex unrolling
  -- if the upper bound is unknown, simplify the body of the maximum and...
  i' ->
    let j' = simplifyIndex j
     in -- if the body of does not mention id, then just return the body
        if id `notElem` ifv j'
          then j'
          --else -- if the body does not increase in i, then return the body at id=0

            --if j' `nonIncreasingIn` id
              --then simplifyIndex $ isub (Number 0) id j'
              --else -- if the body of the maximum does not decrease in i, then return the body at id=i-1

                --if j' `nonDecreasingIn` id
                  --then simplifyIndex $ isub (Minus i' (Number 1)) id j'
                  else -- otherwise return the simplified term and pray that an SMT solver will figure it out (it won't)
                    Maximum id i' j'
    where
      -- If i `nonDecreasingIn` id returns True, then j >= id implies i{j/id} >= i
      -- Note, this is an approximation, the converse does not hold
      nonDecreasingIn :: Index -> IndexVariableId -> Bool
      nonDecreasingIn (IndexVariable _) _ = True
      nonDecreasingIn (Number _) _ = True
      nonDecreasingIn (Plus i j) id = i `nonDecreasingIn` id && j `nonDecreasingIn` id
      nonDecreasingIn (Max i j) id = i `nonDecreasingIn` id && j `nonDecreasingIn` id
      nonDecreasingIn (Mult i j) id = i `nonDecreasingIn` id && j `nonDecreasingIn` id
      nonDecreasingIn (Minus i j) id = i `nonDecreasingIn` id && j `nonIncreasingIn` id
      nonDecreasingIn (Maximum id' i j) id
        | id /= id' =
            i `nonDecreasingIn` id && j `nonDecreasingIn` id
              || i `nonDecreasingIn` id && j `nonDecreasingIn` id'
      nonDecreasingIn _ _ = False
      -- If i `nonIncreasingIn` id returns True, then j >= id implies i{j/id} <= i (incomplete)
      -- Note, this is an approximation, the converse does not hold
      nonIncreasingIn :: Index -> IndexVariableId -> Bool
      nonIncreasingIn (IndexVariable id') id = id /= id'
      nonIncreasingIn (Number _) _ = True
      nonIncreasingIn (Plus i j) id = i `nonIncreasingIn` id && j `nonIncreasingIn` id
      nonIncreasingIn (Max i j) id = i `nonIncreasingIn` id && j `nonIncreasingIn` id
      nonIncreasingIn (Mult i j) id = i `nonIncreasingIn` id && j `nonIncreasingIn` id
      nonIncreasingIn (Minus i j) id = i `nonIncreasingIn` id && j `nonDecreasingIn` id
      nonIncreasingIn (Maximum id' i j) id
        | id /= id' =
            i `nonIncreasingIn` id && j `nonIncreasingIn` id
              || i `nonIncreasingIn` id && j `nonDecreasingIn` id'
      nonIncreasingIn _ _ = False

-- Θ ⊨ i = j (figs. 10,15)
-- in this implementation, Θ implicitly contains all the free variables in i and j
checkEq :: Index -> Index -> Bool
checkEq i j = case (simplifyIndex i, simplifyIndex j) of
  (i', j') | i' == j' -> True -- identical indices are equal
  (Number n, Number m) -> n == m -- number indices are equal iff their values are equal
  (IndexVariable id, IndexVariable id') -> id == id' -- variables are equal if they are the same name
  (i', j') ->
    let theta = ifv i' `Set.union` ifv j' -- in all other cases, query the SMT solver
     in querySMTWithContext theta $ Constraint Eq i' j'

-- Θ ⊨ i ≤ j (figs. 12,15)
-- in this implementation, Θ implicitly contains all the free variables in i and j
checkLeq :: Index -> Index -> Bool
checkLeq i j = case (simplifyIndex i, simplifyIndex j) of
  (i', j') | i' == j' -> True -- identical indices are equal
  (Number n, Number m) -> n <= m -- number indices are lesser-or-equal iff their values are lesser-or-equal
  (i', j') ->
    let theta = ifv i' `Set.union` ifv j' -- in all other cases, query the SMT solver
     in querySMTWithContext theta $ Constraint Leq i' j'
