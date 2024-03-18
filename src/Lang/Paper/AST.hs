{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Lang.Paper.AST
  ( Value (..),
    Term (..),
    Type (..),
    isLinear,
    VariableId,
    toBundleType,
    TVarId,
    hadamard,
    pauliX,
    qinit,
    qdiscard,
    cnot,
  )
where

import Bundle.AST (Bundle, BundleType, LabelId)
import qualified Bundle.AST as Bundle
import Circuit (Circuit)
import qualified Circuit
import Index.AST
import Lang.Type.AST
import PrettyPrinter

--- PAPER LANGUAGE MODULE (UNUSED)--------------------------------------------------------------------------
---
--- This module defines the abstract syntax of the language almost exactly as presented in the paper.
--- This is currently not used in the application, it is no longer tested and is only kept for reference.
--- For the actual implementation of the language, see Lang.Unified.AST.
------------------------------------------------------------------------------------------------------------

type VariableId = String

-- The datatype of PQR values
-- Fig. 8
data Value
  = UnitValue
  | Label LabelId                       -- l, k, t...
  | Variable VariableId                 -- x, y, z...
  | Pair Value Value                    -- (v, w)
  | BoxedCircuit Bundle Circuit Bundle  -- (b1, c, b2)
  | Abs VariableId Type Term            -- \x :: t . m
  | Lift Term                           -- lift m
  | Nil                                 -- []
  | Cons Value Value                    -- v:w
  | Fold IndexVariableId Value Value    -- fold[i] v w
  | Anno Value Type                     -- v :: typ
  deriving (Eq, Show)

instance Pretty Value where
  pretty UnitValue = "()"
  pretty (Label id) = id
  pretty (Variable id) = id
  pretty (Pair v w) = "(" ++ pretty v ++ ", " ++ pretty w ++ ")"
  pretty (BoxedCircuit _ c _) = "[" ++ pretty c ++ "]"
  pretty (Abs x t m) = "(\\" ++ x ++ ":" ++ pretty t ++ " -> " ++ pretty m ++ ")"
  pretty (Lift m) = "(lift " ++ pretty m ++ ")"
  pretty Nil = "[]"
  pretty (Cons v w) = "(" ++ pretty v ++ ":" ++ pretty w ++ ")"
  pretty (Fold i v w) = "(fold[" ++ i ++ "] " ++ pretty v ++ " " ++ pretty w ++ ")"
  pretty (Anno v t) = "(" ++ pretty v ++ " :: " ++ pretty t ++ ")"

-- The datatype of PQR terms
-- Fig. 8
data Term
  = Apply Value Value                       -- apply(v, w)
  | Box BundleType Value                    -- box[bt] v
  | Dest VariableId VariableId Value Term   -- let (x, y) = v in m
  | Return Value                            -- return v
  | Let VariableId Term Term                -- let x = m in n
  | App Value Value                         -- v w
  | Force Value                             -- force v
  deriving (Eq, Show)

instance Pretty Term where
  pretty (Apply v w) = "apply(" ++ pretty v ++ ", " ++ pretty w ++ ")"
  pretty (Box t v) = "box:" ++ pretty t ++ "(" ++ pretty v ++ ")"
  pretty (Dest x y v m) = "(let (" ++ x ++ ", " ++ y ++ ") = " ++ pretty v ++ " in " ++ pretty m ++ ")"
  pretty (Return v) = "return " ++ pretty v
  pretty (Let x m n) = "(let " ++ x ++ " = " ++ pretty m ++ " in " ++ pretty n ++ ")"
  pretty (App m n) = "(" ++ pretty m ++ " " ++ pretty n ++ ")"
  pretty (Force v) = "force(" ++ pretty v ++ ")"

--- PRIMITIVE BOXED CIRCUITS ---------------------------------------------------------------------------------

-- Hadamard gate, maps a single qubit to a superposition of 0 and 1
hadamard :: Value
hadamard = BoxedCircuit (Bundle.Label "a") Circuit.hadamard (Bundle.Label "b")

-- Pauli X gate, flips the state of a single qubit
pauliX :: Value
pauliX = BoxedCircuit (Bundle.Label "a") Circuit.pauliX (Bundle.Label "b")

-- Initializes a single qubit to the 0 state
qinit :: Value
qinit = BoxedCircuit Bundle.UnitValue Circuit.qinit0 (Bundle.Label "a")

-- Discards a single qubit
qdiscard :: Value
qdiscard = BoxedCircuit (Bundle.Label "a") Circuit.qdiscard Bundle.UnitValue

-- Controlled not gate, two-qubit gate, flips the second qubit if the first qubit is 1
cnot :: Value
cnot =
  BoxedCircuit (Bundle.Pair (Bundle.Label "a") (Bundle.Label "b")) Circuit.cnot (Bundle.Pair (Bundle.Label "c") (Bundle.Label "d"))
