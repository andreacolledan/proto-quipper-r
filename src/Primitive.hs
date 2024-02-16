module Primitive
  ( hadamard,
    pauliX,
    qinit,
    qdiscard,
    cnot,
  )
where

import Bundle.AST (WireType (..))
import qualified Bundle.AST as Bundle
import Circuit
import qualified Data.Map as Map
import Lang.Paper.AST (Value (..))

-- Hadamard gate, maps a single qubit to a superposition of 0 and 1
hadamard :: Value
hadamard = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a", Qubit)])) Hadamard (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")

-- Pauli X gate, flips the state of a single qubit
pauliX :: Value
pauliX = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a", Qubit)])) PauliX (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")

-- Initializes a single qubit
qinit :: Value
qinit = BoxedCircuit Bundle.UnitValue (Seq (Id Map.empty) Init Bundle.UnitValue (Bundle.Label "a")) (Bundle.Label "a")

-- Discards a single qubit
qdiscard :: Value
qdiscard = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a", Qubit)])) Discard (Bundle.Label "a") Bundle.UnitValue) Bundle.UnitValue

-- Controlled not gate, two-qubit gate, flips the second qubit if the first qubit is 1
cnot :: Value
cnot =
  BoxedCircuit
    (Bundle.Pair (Bundle.Label "a1") (Bundle.Label "a2"))
    (Seq (Id (Map.fromList [("a1", Qubit), ("a2", Qubit)])) CNot (Bundle.Pair (Bundle.Label "a1") (Bundle.Label "a2")) (Bundle.Pair (Bundle.Label "b1") (Bundle.Label "b2")))
    (Bundle.Pair (Bundle.Label "b1") (Bundle.Label "b2"))