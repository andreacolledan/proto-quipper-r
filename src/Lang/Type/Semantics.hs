module Lang.Type.Semantics where

import Bundle.AST
import Lang.Type.AST
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
  checkSubtype t1' t1
    && checkSubtype t2 t2'
checkSubtype (TArrow t1 t2 i j) (TArrow t1' t2' i' j') =
  checkSubtype t1' t1
    && checkSubtype t2 t2'
    && checkLeq i i'
    && checkEq j j'
checkSubtype (TCirc i btype1 btype2) (TCirc i' btype1' btype2') =
  checkSubtype (fromBundleType btype1) (fromBundleType btype1')
    && checkSubtype (fromBundleType btype1') (fromBundleType btype1)
    && checkSubtype (fromBundleType btype2) (fromBundleType btype2')
    && checkSubtype (fromBundleType btype2') (fromBundleType btype2)
    && checkLeq i i'
checkSubtype (TList i t) (TList i' t') =
  checkSubtype t t'
    && checkEq i i'
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
checkTypeEq (TList i t) (TList i' t') =
  checkTypeEq t t'
    && checkEq i i'
checkTypeEq _ _ = False

-- Coerce a bundle type to a PQR type
-- Raises an error if the input is a type variable (should never happen)
fromBundleType :: BundleType -> Type
fromBundleType BTUnit = TUnit
fromBundleType (BTWire wtype) = TWire wtype
fromBundleType (BTPair btype1 btype2) = TPair (fromBundleType btype1) (fromBundleType btype2)
fromBundleType (BTList i btype) = TList i (fromBundleType btype)
fromBundleType (BTVar _) = error "Cannot convert bundle type variable to PQR type"
