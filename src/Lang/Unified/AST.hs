{-# LANGUAGE InstanceSigs #-}
module Lang.Unified.AST (
  Expr(..),
  VariableId
) where

import Bundle.AST
import Index.AST
import Lang.Type.AST
import Circuit ( Circuit )
import PrettyPrinter (Pretty(..))
import Lang.Unified.Constant
import Lang.Type.Unify (HasType (..), TypeSubstitution, toBundleTypeSubstitution)
import qualified Data.Set as Set

--- PQR SYNTAX MODULE ---------------------------------------------------------------------------------------
---
--- This module defines the abstract syntax of PQR expressions. This syntax is based on the one in the paper,
--- but it exhibits significant differences and additional constructs which make it more usable.
-------------------------------------------------------------------------------------------------------------

type VariableId = String

-- | The datatype of PQR expressions
data Expr =
  EUnit                                       -- Unit value               : ()
  | ELabel LabelId                            -- Label (internal)         :
  | EVar VariableId                           -- Variable                 : x, y, z, ...          
  | EPair Expr Expr                           -- Pair                     : (e1, e2)
  | EAbs VariableId Type Expr                 -- Abstraction              : \x :: t . e
  | ELift Expr                                -- Lift                     : lift e
  | ENil (Maybe Type)                         -- Nil                      : []
  | ECons Expr Expr                           -- Cons                     : e : es
  | EFold Expr Expr Expr                      -- Fold                     : fold (e1, e2, e3)
  | ECirc Bundle Circuit Bundle               -- Boxed Circuit (internal) :  
  | EApp Expr Expr                            -- Application              : e1 e2
  | EApply Expr Expr                          -- Apply                    : apply(e1, e2)
  | EBox BundleType Expr                      -- Box                      : box :: bt e
  | EForce Expr                               -- Force                    : force e
  | ELet VariableId Expr Expr                 -- Let                      : let x = e1 in e2
  | EDest VariableId VariableId Expr Expr     -- Dest                     : let (x, y) = e1 in e2
  | EAnno Expr Type                           -- Annotation               : e :: t
  | EIAbs IndexVariableId Expr                -- Index Abstraction        : @i . e
  | EIApp Expr Index                          -- Index Application        : e @ i
  | EConst Constant                           -- Constant                 : QInit0, Hadamard, ...
  | ELetCons VariableId VariableId Expr Expr  -- Let Cons                 : let x:xs = e1 in e2
  deriving (Eq, Show)

instance Pretty Expr where
  pretty EUnit = "()"
  pretty (ELabel id) = id
  pretty (EVar id) = id
  pretty (EPair e1 e2) = "(" ++ pretty e1 ++ ", " ++ pretty e2 ++ ")"
  pretty (ECirc {}) = "[Boxed Circuit]"
  pretty (EAbs x t e) = "(\\" ++ x ++ " :: " ++ pretty t ++ " . " ++ pretty e ++ ")" 
  pretty (EApp e1 e2) = "(" ++ pretty e1 ++ " " ++ pretty e2 ++ ")"
  pretty (ELift e) = "(lift " ++ pretty e ++ ")"
  pretty (EForce e) = "(force " ++ pretty e ++ ")"
  pretty (ENil _) = "[]"
  pretty (ECons e1 e2) = "(" ++ pretty e1 ++ ":" ++ pretty e2 ++ ")"
  pretty (EFold e1 e2 e3) = "fold (" ++ pretty e1 ++ ", " ++ pretty e2 ++ ", " ++ pretty e3 ++ ")"
  pretty (EAnno e t) = "(" ++ pretty e ++ " :: " ++ pretty t ++ ")"
  pretty (EApply e1 e2) = "apply(" ++ pretty e1 ++ ", " ++ pretty e2 ++ ")"
  pretty (EBox bt e) = "(box ::" ++ pretty bt ++ " " ++ pretty e ++ ")"
  pretty (ELet x e1 e2) = "(let " ++ x ++ " = " ++ pretty e1 ++ " in " ++ pretty e2 ++ ")"
  pretty (EDest x y e1 e2) = "(let (" ++ x ++ ", " ++ y ++ ") = " ++ pretty e1 ++ " in " ++ pretty e2 ++ ")"
  pretty (EIAbs id e) = "(@" ++ id ++ " . " ++ pretty e ++ ")"
  pretty (EIApp e i) = "(" ++ pretty e ++ " @ " ++ pretty i ++ ")"
  pretty (EConst c) = pretty c
  pretty (ELetCons x y e1 e2) = "(let " ++ x ++ ":" ++ y ++ " = " ++ pretty e1 ++ " in " ++ pretty e2 ++ ")"

instance HasType Expr where
  tfv :: Expr -> Set.Set TVarId
  tfv EUnit = Set.empty
  tfv (ELabel _) = Set.empty
  tfv (EVar _) = Set.empty
  tfv (EPair e1 e2) = tfv e1 `Set.union` tfv e2
  tfv (ECirc {}) = Set.empty
  tfv (EAbs _ t e) = tfv t `Set.union` tfv e
  tfv (EApp e1 e2) = tfv e1 `Set.union` tfv e2
  tfv (ELift e) = tfv e
  tfv (EForce e) = tfv e
  tfv (ENil anno) = maybe Set.empty tfv anno
  tfv (ECons e1 e2) = tfv e1 `Set.union` tfv e2
  tfv (EFold e1 e2 e3) = tfv e1 `Set.union` tfv e2 `Set.union` tfv e3
  tfv (EAnno e t) = tfv e `Set.union` tfv t
  tfv (EApply e1 e2) = tfv e1 `Set.union` tfv e2
  tfv (EBox bt e) = btfv bt `Set.union` tfv e
  tfv (ELet _ e1 e2) = tfv e1 `Set.union` tfv e2
  tfv (EDest _ _ e1 e2) = tfv e1 `Set.union` tfv e2
  tfv (EIAbs _ e) = tfv e
  tfv (EIApp e _) = tfv e
  tfv (EConst _) = Set.empty
  tfv (ELetCons _ _ e1 e2) = tfv e1 `Set.union` tfv e2
  tsub :: TypeSubstitution -> Expr -> Expr
  tsub _ EUnit = EUnit
  tsub _ (ELabel id) = ELabel id
  tsub _ (EVar id) = EVar id
  tsub sub (EPair e1 e2) = EPair (tsub sub e1) (tsub sub e2)
  tsub _ e@(ECirc {}) = e -- bundle types do not contain type variables
  tsub sub (EAbs id t e) = EAbs id (tsub sub t) (tsub sub e)
  tsub sub (EApp e1 e2) = EApp (tsub sub e1) (tsub sub e2)
  tsub sub (ELift e) = ELift (tsub sub e)
  tsub sub (EForce e) = EForce (tsub sub e)
  tsub sub (ENil anno) = ENil (tsub sub <$> anno)
  tsub sub (ECons e1 e2) = ECons (tsub sub e1) (tsub sub e2)
  tsub sub (EFold e1 e2 e3) = EFold (tsub sub e1) (tsub sub e2) (tsub sub e3)
  tsub sub (EAnno e t) = EAnno (tsub sub e) (tsub sub t)
  tsub sub (EApply e1 e2) = EApply (tsub sub e1) (tsub sub e2)
  tsub sub (EBox bt e) = let sub' = toBundleTypeSubstitution sub in EBox (btsub sub' bt) (tsub sub e)
  tsub sub (ELet id e1 e2) = ELet id (tsub sub e1) (tsub sub e2)
  tsub sub (EDest id1 id2 e1 e2) = EDest id1 id2 (tsub sub e1) (tsub sub e2)
  tsub sub (EIAbs id e) = EIAbs id (tsub sub e)
  tsub sub (EIApp e i) = EIApp (tsub sub e) i
  tsub _ e@(EConst _) = e
  tsub sub (ELetCons id1 id2 e1 e2) = ELetCons id1 id2 (tsub sub e1) (tsub sub e2)
  


  