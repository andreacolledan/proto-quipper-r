module Semantics.Type where

import AST.Bundle (BundleType)
import qualified AST.Bundle as Bundle
import AST.Language
import Semantics.Index

-- Type semantics in the form of a reduction function
-- Note that types simplify only in the presence of indices
simplifyType :: Type -> Type
simplifyType (Tensor t1 t2) = Tensor (simplifyType t1) (simplifyType t2)
simplifyType (Arrow t1 t2 i j) = Arrow (simplifyType t1) (simplifyType t2) (simplifyIndex i) (simplifyIndex j)
simplifyType (Bang t) = Bang (simplifyType t)
simplifyType (List i t) = List (simplifyIndex i) (simplifyType t)
simplifyType (Circ i inBtype outBtype) = Circ (simplifyIndex i) inBtype outBtype
simplifyType t = t

-- Θ ⊢ t1 <: t2 (Figure 15)
-- Note that in this implementation Θ is assumed to contain all the free index variables of t1 and t2
checkSubtype :: Type -> Type -> Bool
checkSubtype UnitType UnitType = True
checkSubtype (WireType wtype1) (WireType wtype2) = wtype1 == wtype2
checkSubtype (Bang t) (Bang t') = checkSubtype t t'
checkSubtype (Tensor t1 t2) (Tensor t1' t2') =
  checkSubtype t1' t1
    && checkSubtype t2 t2'
checkSubtype (Arrow t1 t2 i j) (Arrow t1' t2' i' j') =
  checkSubtype t1' t1
    && checkSubtype t2 t2'
    && checkLeq i i'
    && checkEq j j'
checkSubtype (Circ i btype1 btype2) (Circ i' btype1' btype2') =
  checkSubtype (fromBundleType btype1) (fromBundleType btype1')
    && checkSubtype (fromBundleType btype1') (fromBundleType btype1)
    && checkSubtype (fromBundleType btype2) (fromBundleType btype2')
    && checkSubtype (fromBundleType btype2') (fromBundleType btype2)
    && checkLeq i i'
checkSubtype (List i t) (List i' t') =
  checkSubtype t t'
    && checkEq i i'
checkSubtype _ _ = False

-- Θ ⊢ t1 <:> t2 (Figure 15)
-- Note that in this implementation Θ is assumed to contain all the free index variables of t1 and t2
checkTypeEq :: Type -> Type -> Bool
checkTypeEq UnitType UnitType = True
checkTypeEq (WireType wtype1) (WireType wtype2) = wtype1 == wtype2
checkTypeEq (Bang t) (Bang t') = checkTypeEq t t'
checkTypeEq (Tensor t1 t2) (Tensor t1' t2') =
  checkTypeEq t1' t1
    && checkTypeEq t2 t2'
checkTypeEq (Arrow t1 t2 i j) (Arrow t1' t2' i' j') =
  checkTypeEq t1' t1
    && checkTypeEq t2 t2'
    && checkEq i i'
    && checkEq j j'
checkTypeEq (Circ i btype1 btype2) (Circ i' btype1' btype2') =
  checkTypeEq (fromBundleType btype1) (fromBundleType btype1')
    && checkTypeEq (fromBundleType btype2) (fromBundleType btype2')
    && checkEq i i'
checkTypeEq (List i t) (List i' t') =
  checkTypeEq t t'
    && checkEq i i'
checkTypeEq _ _ = False

-- Coerce a bundle type to a PQR type
-- Raises an error if the input is a type variable (should never happen)
fromBundleType :: BundleType -> Type
fromBundleType Bundle.UnitType = UnitType
fromBundleType (Bundle.WireType wtype) = WireType wtype
fromBundleType (Bundle.Tensor btype1 btype2) = Tensor (fromBundleType btype1) (fromBundleType btype2)
fromBundleType (Bundle.List i btype) = List i (fromBundleType btype)
fromBundleType (Bundle.TypeVariable _) = error "Cannot convert bundle type variable to PQR type"
