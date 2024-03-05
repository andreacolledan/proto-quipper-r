module Lang.Unified.AST (
  Expr(..),
  Constant(..),
  VariableId
) where

import Bundle.AST
import Index.AST
import Lang.Type.AST
import Circuit ( Circuit )
import PrettyPrinter (Pretty(..))

type VariableId = String

-- Enum of constants
data Constant
  -- Qubit metaoperations
  = QInit0
  | QInit1
  | QDiscard
  | Meas
  -- Single qubit gates
  | Hadamard
  | PauliX
  | PauliY
  | PauliZ
  -- Two qubit gates
  | CNot
  -- Three qubit gates
  | Toffoli
  -- Functions
  | MakeCRGate
  deriving (Eq, Show)

instance Pretty Constant where
  pretty QInit0 = "QInit0"
  pretty QInit1 = "QInit1"
  pretty QDiscard = "QDiscard"
  pretty Meas = "Meas"
  pretty Hadamard = "Hadamard"
  pretty PauliX = "PauliX"
  pretty PauliY = "PauliY"
  pretty PauliZ = "PauliZ"
  pretty CNot = "CNot"
  pretty Toffoli = "Toffoli"
  pretty MakeCRGate = "MakeCRGate"

-- The datatype of PQR expressions
data Expr =
  EUnit                                       -- Unit value               : ()
  | ELabel LabelId                            -- Label (internal)         :
  | EVar VariableId                           -- Variable                 : x, y, z, ...          
  | EPair Expr Expr                           -- Pair                     : (e1, e2)
  | EAbs VariableId Type Expr                 -- Abstraction              : \x :: t . e
  | ELift Expr                                -- Lift                     : lift e
  | ENil                                     -- Nil                      : []
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
  | EConst Constant                           -- Constant                 :
  | ELetCons VariableId VariableId Expr Expr  -- Let Cons                 : let (x : y) = e1 in e2
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
  pretty ENil = "[]"
  pretty (ECons e1 e2) = "(" ++ pretty e1 ++ ":" ++ pretty e2 ++ ")"
  pretty (EFold e1 e2 e3) = "fold (" ++ pretty e1 ++ ", " ++ pretty e2 ++ ", " ++ pretty e3 ++ ")"
  pretty (EAnno e t) = "(" ++ pretty e ++ " :: " ++ pretty t ++ ")"
  pretty (EApply e1 e2) = "apply(" ++ pretty e1 ++ ", " ++ pretty e2 ++ ")"
  pretty (EBox bt e) = "(box ::" ++ pretty bt ++ " " ++ pretty e ++ ")"
  pretty (ELet x e1 e2) = "(let " ++ x ++ " = " ++ pretty e1 ++ " in " ++ pretty e2 ++ ")"
  pretty (EDest x y e1 e2) = "(let (" ++ x ++ ", " ++ y ++ ") = " ++ pretty e1 ++ " in " ++ pretty e2 ++ ")"
  pretty (EIAbs id e) = "(forall " ++ id ++ " . " ++ pretty e ++ ")"
  pretty (EIApp e i) = "(" ++ pretty e ++ " @ " ++ pretty i ++ ")"
  pretty (EConst c) = pretty c
  pretty (ELetCons x y e1 e2) = "(let (" ++ x ++ ":" ++ y ++ ") = " ++ pretty e1 ++ " in " ++ pretty e2 ++ ")"

