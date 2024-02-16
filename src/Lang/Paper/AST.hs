{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Lang.Paper.AST
  ( Value (..),
    Term (..),
    Type (..),
    isLinear,
    VariableId,
    toBundleType,
    TypeSubstitution,
    tsub,
    mgtu,
    compose,
    TVarId
  )
where

import Bundle.AST (Bundle, BundleType, LabelId)
import Circuit
import Index.AST
import PrettyPrinter
import Lang.Type.AST

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



