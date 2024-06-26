module Index.Semantics
  ( simplifyIndex,
    simplifyIndexStrong,
    checkEq,
    checkLeq,
    checkClosedEq
  )
where

import Index.AST
import Solving.CVC5
import qualified Data.HashSet as Set

-- | @simplifyIndex qfh i@ returns index expression @i@ in a normal form.
-- Note that this might not be a natural number (e.g. if @i@ contains free variables).
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
  (i', Number 0) -> i' -- zero is right identity
  (Number 0, _) -> Number 0 -- zero is left absorbing
  (i', j') -> Minus i' j' -- do not reduce further
simplifyIndex (Maximum id i j) = case simplifyIndex i of
  -- if upper bound is 0, the range is empty and the maximum defaults to 0
  Number 0 -> Number 0
  -- if the upper bound is known, unroll the maximum into a sequence of binary maxima
  Number n ->
    let unrolling = foldr1 Max [simplifyIndex (isub (Number step) id j) | step <- [0 .. n - 1]]
     in simplifyIndex unrolling
  -- if the upper bound is not known, do not reduce further
  i' -> Maximum id i' (simplifyIndex j)

-- | Like 'simplifyIndex', but the reduction strategy can access the SMT solver.
-- 'SolverHandle' @qfh@ is used to interact with the SMT solver.
-- Used only to display inferred types.
simplifyIndexStrong :: SolverHandle -> Index -> IO Index
simplifyIndexStrong _ (Number n) = return $ Number n
simplifyIndexStrong _ (IndexVariable id) = return $ IndexVariable id
simplifyIndexStrong qfh (Plus i j) = do
  i' <- simplifyIndexStrong qfh i
  j' <- simplifyIndexStrong qfh j
  return $ case (i',j') of
    (Number n, Number m) -> Number (n + m)
    (i', Number 0) -> i'    -- zero is right identity
    (Number 0, j') -> j'    -- zero is left identity
    (i', j') -> Plus i' j'  -- do not reduce further
simplifyIndexStrong qfh (Max i j) = do
  i' <- simplifyIndexStrong qfh i
  j' <- simplifyIndexStrong qfh j
  case (i',j') of
    (Number n, Number m) -> return $ Number (max n m)
    (i', Number 0) -> return i' -- zero is right identity
    (Number 0, j') -> return j' -- zero is left identity
    (i', j') -> do
      c <- checkEq qfh i' j'
      return $ if c
        then i'          -- idemptotent
        else Max i' j'   -- do not reduce further
simplifyIndexStrong qfh (Mult i j) = do
  i' <- simplifyIndexStrong qfh i
  j' <- simplifyIndexStrong qfh j
  return $ case (i', j') of
    (Number n, Number m) -> Number (n * m)
    (_, Number 0) -> Number 0 -- zero is right absorbing
    (Number 0, _) -> Number 0 -- zero is left absorbing
    (i', Number 1) -> i'      -- one is right identity
    (Number 1, j') -> j'      -- one is left identity
    (i', j') -> Mult i' j'    -- do not reduce further
simplifyIndexStrong qfh (Minus i j) = do
  i' <- simplifyIndexStrong qfh i
  j' <- simplifyIndexStrong qfh j
  case (i',j') of
    (Number n, Number m) -> return $ Number (max 0 (n - m))
    (i', Number 0) -> return i' -- zero is right identity
    (Number 0, _) -> return $ Number 0 -- zero is left absorbing
    (i',j') -> do
      c <- checkEq qfh i' j'
      return $ if c
        then Number 0      -- equal terms cancel each other out
        else Minus i' j'   -- do not reduce further
simplifyIndexStrong qfh (Maximum id i j) = do
  i' <- simplifyIndexStrong qfh i
  case i' of 
    -- if upper bound is 0, the range is empty and the maximum defaults to 0
    Number 0 -> return $ Number 0
    -- if the upper bound is known, unroll the maximum into a sequence of binary maxima
    Number n -> do
      elems <- sequence [simplifyIndexStrong qfh (isub (Number step) id j) | step <- [0 .. n - 1]]
      let unrolling = foldr1 Max elems
      simplifyIndexStrong qfh unrolling
    -- if the upper bound is not known, do not reduce further
    i' -> do
      j' <- simplifyIndexStrong qfh j
      return $ Maximum id i' j'


  

-- Θ ⊨ i = j (figs. 10,15)
-- | @checkEq qfh i j@ checks if index expressions @i@ and @j@ are equal
-- for all assignments of their free index variables.
-- SolverHandle @qfh@ is used to interact with the SMT solver.
checkEq :: SolverHandle -> Index -> Index -> IO Bool
checkEq qfh i j = case (simplifyIndex i, simplifyIndex j) of
  (i', j') | i' == j' -> return True -- identical indices are equal
  (i', j') | Set.null (ifv i') && Set.null (ifv j') -> return False -- if both indices are closed and not equal, they are not equal
  (i', j') -> querySMTWithContext qfh $ Constraint Eq i' j' -- in all other cases, query the solver

-- Θ ⊨ i ≤ j (figs. 12,15)
-- | @checkLeq qfh i j@ checks if index expression @i@ is lesser-or-equal than index expression @j@
-- for all assignments of their free index variables.
-- SolverHandle @qfh@ is used to interact with the SMT solver.
checkLeq :: SolverHandle -> Index -> Index -> IO Bool
checkLeq qfh i j = case (simplifyIndex i, simplifyIndex j) of
  (i', j') | i' == j' -> return True -- identical indices are lesser-or-equal
  (Number n, Number m) -> return $ n <= m -- number indices are lesser-or-equal iff their values are lesser-or-equal
  (i', j') -> querySMTWithContext qfh $ Constraint Leq i' j' -- in all other cases, query the solver

checkClosedEq :: Index -> Index -> Bool
checkClosedEq i j = case (simplifyIndex i, simplifyIndex j) of
  (i', j') | i' == j' -> True
  _ -> False
