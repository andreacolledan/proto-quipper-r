module Index.Semantics
  ( simplifyIndex,
    checkEq,
    checkLeq,
  )
where

import Index.AST
import Solving.CVC5
import System.IO.Extra (Handle)

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
  (i', j') -> Plus i' j' -- do not reduce further
simplifyIndex (Max i j) = case (simplifyIndex i, simplifyIndex j) of
  (Number n, Number m) -> Number (max n m)
  (i', Number 0) -> i' -- zero is right identity
  (Number 0, j') -> j' -- zero is left identity
  (i', j') | i' == j' -> i' -- idempotent
  (i', j') -> Max i' j' -- do not reduce further
simplifyIndex (Mult i j) = case (simplifyIndex i, simplifyIndex j) of
  (Number n, Number m) -> Number (n * m)
  (_, Number 0) -> Number 0 -- zero is right absorbing
  (Number 0, _) -> Number 0 -- zero is left absorbing
  (i', Number 1) -> i' -- one is right identity
  (Number 1, j') -> j' -- one is left identity
  (i', j') -> Mult i' j' -- do not reduce further
simplifyIndex (Minus i j) = case (simplifyIndex i, simplifyIndex j) of
  (Number n, Number m) -> Number (max 0 (n - m))
  (i', j') | i' == j' -> Number 0 -- a - a = 0
  (i', Number 0) -> i' -- zero is right identity
  (Number 0, _) -> Number 0 -- zero is left absorbing
  (i', j') -> Minus i' j' -- do not reduce further
simplifyIndex (Maximum id i j) = case simplifyIndex i of
  -- if upper bound is 0, the range is empty and the maximum defaults to 0
  Number 0 -> Number 0
  -- if the upper bound is known, unroll the maximum into a sequence of binary maxima
  Number n ->
    let unrolling = foldr1 Max [isub (Number step) id (simplifyIndex j) | step <- [0 .. n - 1]]
     in simplifyIndex unrolling
  -- if the upper bound is not known, do not reduce further
  i' -> Maximum id i' (simplifyIndex j)
  

-- Θ ⊨ i = j (figs. 10,15)
-- in this implementation, Θ implicitly contains all the free variables in i and j
checkEq :: Handle -> Index -> Index -> Bool
checkEq qfh i j = case (simplifyIndex i, simplifyIndex j) of
  (i', j') | i' == j' -> True -- identical indices are equal
  (Number n, Number m) -> n == m -- number indices are equal iff their values are equal
  (IndexVariable id, IndexVariable id') -> id == id' -- variables are equal if they are the same name
  (i', j') -> querySMTWithContext qfh $ Constraint Eq i' j' -- in all other cases, query the solver

-- Θ ⊨ i ≤ j (figs. 12,15)
-- in this implementation, Θ implicitly contains all the free variables in i and j
checkLeq :: Handle -> Index -> Index -> Bool
checkLeq qfh i j = case (simplifyIndex i, simplifyIndex j) of
  (i', j') | i' == j' -> True -- identical indices are equal
  (Number n, Number m) -> n <= m -- number indices are lesser-or-equal iff their values are lesser-or-equal
  (i', j') -> querySMTWithContext qfh $ Constraint Leq i' j' -- in all other cases, query the solver
