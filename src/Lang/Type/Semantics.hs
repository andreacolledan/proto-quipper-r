module Lang.Type.Semantics where
import Lang.Type.AST
import Index.AST
import Index.Semantics
import System.IO.Extra (Handle)

-- Type semantics in the form of a reduction function
-- Note that types simplify only in the presence of indices
simplifyType :: Handle -> Type -> Type
simplifyType qfh (TPair t1 t2) = TPair (simplifyType qfh t1) (simplifyType qfh t2)
simplifyType qfh (TArrow t1 t2 i j) = TArrow (simplifyType qfh t1) (simplifyType qfh t2) (simplifyIndex qfh i) (simplifyIndex qfh j)
simplifyType qfh (TBang t) = TBang (simplifyType qfh t)
simplifyType qfh (TList i t) = TList (simplifyIndex qfh i) (simplifyType qfh t)
simplifyType qfh (TCirc i inBtype outBtype) = TCirc (simplifyIndex qfh i) inBtype outBtype
simplifyType qfh (TIForall id t i j) = TIForall id (simplifyType qfh t) (simplifyIndex qfh i) (simplifyIndex qfh j)
simplifyType _ t = t

-- Θ ⊢ t1 <: t2 (Figure 15)
-- Note that in this implementation Θ is assumed to contain all the free index variables of t1 and t2
checkSubtype :: Handle -> Type -> Type -> Bool
checkSubtype _ TUnit TUnit = True
checkSubtype _ (TWire wtype1) (TWire wtype2) = wtype1 == wtype2
checkSubtype qfh (TBang t) (TBang t') = checkSubtype qfh t t'
checkSubtype qfh (TPair t1 t2) (TPair t1' t2') =
  checkSubtype qfh t1 t1'
    && checkSubtype qfh t2 t2'
checkSubtype qfh (TArrow t1 t2 i j) (TArrow t1' t2' i' j') =
  checkSubtype qfh t1' t1
    && checkSubtype qfh t2 t2'
    && checkLeq qfh i i'
    && checkEq qfh j j'
checkSubtype qfh (TCirc i btype1 btype2) (TCirc i' btype1' btype2') =
  checkTypeEq qfh (fromBundleType btype1) (fromBundleType btype1')
    && checkTypeEq qfh (fromBundleType btype2) (fromBundleType btype2')
    && checkLeq qfh i i'
checkSubtype qfh (TList i t) (TList i' t') = checkEq qfh i i' && checkSubtype qfh t t'
checkSubtype qfh (TIForall id t i j) (TIForall id' t' i' j') = let
  fid = fresh id [i, j, IndexVariable id', i', j']
  fid' = fresh fid [t, t'] -- must do this in two steps since t and t' cannot be put in the same list above
  in checkSubtype qfh (isub (IndexVariable fid') id t) (isub (IndexVariable fid') id' t')
    && checkLeq qfh (isub (IndexVariable fid') id i) (isub (IndexVariable fid') id' i')
    && checkEq qfh (isub (IndexVariable fid') id j) (isub (IndexVariable fid') id' j')
checkSubtype _ _ _ = False

-- Θ ⊢ t1 <:> t2 (Figure 15)
-- Note that in this implementation Θ is assumed to contain all the free index variables of t1 and t2
checkTypeEq :: Handle -> Type -> Type -> Bool
checkTypeEq _ TUnit TUnit = True
checkTypeEq _ (TWire wtype1) (TWire wtype2) = wtype1 == wtype2
checkTypeEq qfh (TBang t) (TBang t') = checkTypeEq qfh t t'
checkTypeEq qfh (TPair t1 t2) (TPair t1' t2') =
  checkTypeEq qfh t1' t1
    && checkTypeEq qfh t2 t2'
checkTypeEq qfh (TArrow t1 t2 i j) (TArrow t1' t2' i' j') =
  checkTypeEq qfh t1' t1
    && checkTypeEq qfh t2 t2'
    && checkEq qfh i i'
    && checkEq qfh j j'
checkTypeEq qfh (TCirc i btype1 btype2) (TCirc i' btype1' btype2') =
  checkTypeEq qfh (fromBundleType btype1) (fromBundleType btype1')
    && checkTypeEq qfh (fromBundleType btype2) (fromBundleType btype2')
    && checkEq qfh i i'
checkTypeEq qfh (TList i t) (TList i' t') = checkTypeEq qfh t t' && checkEq qfh i i'
checkTypeEq qfh (TIForall id t i j) (TIForall id' t' i' j') = let
  fid = fresh id [i, j, IndexVariable id', i', j']
  fid' = fresh fid [t, t'] -- must do this in two steps since t and t' cannot be put in the same list above
  in checkTypeEq qfh (isub (IndexVariable fid') id t) (isub (IndexVariable fid') id' t')
    && checkEq qfh (isub (IndexVariable fid') id i) (isub (IndexVariable fid') id' i')
    && checkEq qfh (isub (IndexVariable fid') id j) (isub (IndexVariable fid') id' j')
checkTypeEq _ _ _ = False
