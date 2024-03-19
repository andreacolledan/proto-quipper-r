module Lang.Type.Semantics where

import Index.AST
import Index.Semantics
import Lang.Type.AST
import Solving.CVC5 (SolverHandle)


-- | @simplifyType t@ returns type @t@ in which all index annotations have been simplified
-- to a normal form according to 'simplifyIndex'.
-- SolverHandle @qfh@ is used to interact with the SMT solver.
simplifyType :: SolverHandle -> Type -> Type
simplifyType qfh (TPair t1 t2) = TPair (simplifyType qfh t1) (simplifyType qfh t2)
simplifyType qfh (TArrow t1 t2 i j) = TArrow (simplifyType qfh t1) (simplifyType qfh t2) (simplifyIndex qfh i) (simplifyIndex qfh j)
simplifyType qfh (TBang t) = TBang (simplifyType qfh t)
simplifyType qfh (TList i t) = TList (simplifyIndex qfh i) (simplifyType qfh t)
simplifyType qfh (TCirc i inBtype outBtype) = TCirc (simplifyIndex qfh i) inBtype outBtype
simplifyType qfh (TIForall id t i j) = TIForall id (simplifyType qfh t) (simplifyIndex qfh i) (simplifyIndex qfh j)
simplifyType _ t = t

-- Θ ⊢ t1 <: t2 (Figure 15)
-- | @checkSubtype qfh t1 t2@ checks if type @t1@ is a subtype of type @t2@.
-- SolverHandle @qfh@ is used to interact with the SMT solver.
checkSubtype :: SolverHandle -> Type -> Type -> IO Bool
checkSubtype _ TUnit TUnit = return True
checkSubtype _ (TWire wtype1) (TWire wtype2) = return $ wtype1 == wtype2
checkSubtype qfh (TBang t) (TBang t') = checkSubtype qfh t t'
checkSubtype qfh (TPair t1 t2) (TPair t1' t2') = do
  c1 <- checkSubtype qfh t1 t1'
  c2 <- checkSubtype qfh t2 t2'
  return $ c1 && c2
checkSubtype qfh (TArrow t1 t2 i j) (TArrow t1' t2' i' j') = do
  c1 <- checkSubtype qfh t1' t1
  c2 <- checkSubtype qfh t2 t2'
  c3 <- checkLeq qfh i i'
  c4 <- checkEq qfh j j'
  return $ c1 && c2 && c3 && c4
checkSubtype qfh (TCirc i btype1 btype2) (TCirc i' btype1' btype2') = do
  c1 <- checkSubtype qfh (fromBundleType btype1') (fromBundleType btype1)
  c2 <- checkSubtype qfh (fromBundleType btype2) (fromBundleType btype2')
  c3 <- checkLeq qfh i i'
  return $ c1 && c2 && c3
checkSubtype qfh (TList i t) (TList i' t') = do
  c1 <- checkEq qfh i i'
  c2 <- checkSubtype qfh t t'
  return $ c1 && c2
checkSubtype qfh (TIForall id t i j) (TIForall id' t' i' j') =
  let fid = fresh id [i, j, IndexVariable id', i', j']
      fid' = fresh fid [t, t'] -- must do this in two steps since t and t' cannot be put in the same list above
   in do
    c1 <- checkSubtype qfh (isub (IndexVariable fid') id t) (isub (IndexVariable fid') id' t')
    c2 <- checkLeq qfh (isub (IndexVariable fid') id i) (isub (IndexVariable fid') id' i')
    c3 <- checkEq qfh (isub (IndexVariable fid') id j) (isub (IndexVariable fid') id' j')
    return $ c1 && c2 && c3
checkSubtype _ _ _ = return False
