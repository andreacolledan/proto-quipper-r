module Lang.Unified.AST where

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
  | MakeRGate
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
  pretty MakeRGate = "MakeRGate"

-- The datatype of PQR expressions
data Expr =
  EUnit
  | ELabel LabelId
  | EVar VariableId
  | EPair Expr Expr
  | EAbs VariableId Type Expr
  | ELift Expr
  | ENil
  | ECons Expr Expr
  | EFold Expr Expr
  | ECirc Bundle Circuit Bundle
  | EApp Expr Expr
  | EApply Expr Expr
  | EBox BundleType Expr
  | EForce Expr
  | ELet VariableId Expr Expr
  | EDest VariableId VariableId Expr Expr
  | EAnno Expr Type
  | EIAbs IndexVariableId Expr
  | EIApp Expr Index
  | EConst Constant
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
  pretty (EFold e1 e2) = "fold (" ++ pretty e1 ++ ", " ++ pretty e2 ++ ")"
  pretty (EAnno e t) = "(" ++ pretty e ++ " :: " ++ pretty t ++ ")"
  pretty (EApply e1 e2) = "apply(" ++ pretty e1 ++ ", " ++ pretty e2 ++ ")"
  pretty (EBox bt e) = "(box ::" ++ pretty bt ++ " " ++ pretty e ++ ")"
  pretty (ELet x e1 e2) = "(let " ++ x ++ " = " ++ pretty e1 ++ " in " ++ pretty e2 ++ ")"
  pretty (EDest x y e1 e2) = "(let (" ++ x ++ ", " ++ y ++ ") = " ++ pretty e1 ++ " in " ++ pretty e2 ++ ")"
  pretty (EIAbs id e) = "(forall " ++ id ++ " . " ++ pretty e ++ ")"
  pretty (EIApp e i) = "(" ++ pretty e ++ " @ " ++ pretty i ++ ")"
  pretty (EConst c) = pretty c

