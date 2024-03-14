module Lang.Type.Semantics where
import Lang.Type.AST
import Index.AST
import Index.Semantics

-- Type semantics in the form of a reduction function
-- Note that types simplify only in the presence of indices
simplifyType :: Type -> Type
simplifyType (TPair t1 t2) = TPair (simplifyType t1) (simplifyType t2)
simplifyType (TArrow t1 t2 i j) = TArrow (simplifyType t1) (simplifyType t2) (simplifyIndex i) (simplifyIndex j)
simplifyType (TBang t) = TBang (simplifyType t)
simplifyType (TList i t) = TList (simplifyIndex i) (simplifyType t)
simplifyType (TCirc i inBtype outBtype) = TCirc (simplifyIndex i) inBtype outBtype
simplifyType (TIForall id t i j) = TIForall id (simplifyType t) (simplifyIndex i) (simplifyIndex j)
simplifyType t = t

-- Θ ⊢ t1 <: t2 (Figure 15)
-- Note that in this implementation Θ is assumed to contain all the free index variables of t1 and t2
checkSubtype :: Type -> Type -> Bool
checkSubtype TUnit TUnit = True
checkSubtype (TWire wtype1) (TWire wtype2) = wtype1 == wtype2
checkSubtype (TBang t) (TBang t') = checkSubtype t t'
checkSubtype (TPair t1 t2) (TPair t1' t2') =
  checkSubtype t1 t1'
    && checkSubtype t2 t2'
checkSubtype (TArrow t1 t2 i j) (TArrow t1' t2' i' j') =
  checkSubtype t1' t1
    && checkSubtype t2 t2'
    && checkLeq i i'
    && checkEq j j'
checkSubtype (TCirc i btype1 btype2) (TCirc i' btype1' btype2') =
  checkTypeEq (fromBundleType btype1) (fromBundleType btype1')
    && checkTypeEq (fromBundleType btype2) (fromBundleType btype2')
    && checkLeq i i'
checkSubtype (TList i t) (TList i' t') = checkEq i i' && (checkEq i (Number 0) || checkSubtype t t') --TODO remove zero check
checkSubtype (TIForall id t i j) (TIForall id' t' i' j') = let
  fid = fresh id [i, j, IndexVariable id', i', j']
  fid' = fresh fid [t, t'] -- must do this in two steps since t and t' cannot be put in the same list above
  in checkSubtype (isub (IndexVariable fid') id t) (isub (IndexVariable fid') id' t')
    && checkLeq (isub (IndexVariable fid') id i) (isub (IndexVariable fid') id' i')
    && checkEq (isub (IndexVariable fid') id j) (isub (IndexVariable fid') id' j')
checkSubtype _ _ = False

-- Θ ⊢ t1 <:> t2 (Figure 15)
-- Note that in this implementation Θ is assumed to contain all the free index variables of t1 and t2
checkTypeEq :: Type -> Type -> Bool
checkTypeEq TUnit TUnit = True
checkTypeEq (TWire wtype1) (TWire wtype2) = wtype1 == wtype2
checkTypeEq (TBang t) (TBang t') = checkTypeEq t t'
checkTypeEq (TPair t1 t2) (TPair t1' t2') =
  checkTypeEq t1' t1
    && checkTypeEq t2 t2'
checkTypeEq (TArrow t1 t2 i j) (TArrow t1' t2' i' j') =
  checkTypeEq t1' t1
    && checkTypeEq t2 t2'
    && checkEq i i'
    && checkEq j j'
checkTypeEq (TCirc i btype1 btype2) (TCirc i' btype1' btype2') =
  checkTypeEq (fromBundleType btype1) (fromBundleType btype1')
    && checkTypeEq (fromBundleType btype2) (fromBundleType btype2')
    && checkEq i i'
checkTypeEq (TList i t) (TList i' t') = checkTypeEq t t' && checkEq i i'
checkTypeEq (TIForall id t i j) (TIForall id' t' i' j') = let
  fid = fresh id [i, j, IndexVariable id', i', j']
  fid' = fresh fid [t, t'] -- must do this in two steps since t and t' cannot be put in the same list above
  in checkTypeEq (isub (IndexVariable fid') id t) (isub (IndexVariable fid') id' t')
    && checkEq (isub (IndexVariable fid') id i) (isub (IndexVariable fid') id' i')
    && checkEq (isub (IndexVariable fid') id j) (isub (IndexVariable fid') id' j')
checkTypeEq _ _ = False
