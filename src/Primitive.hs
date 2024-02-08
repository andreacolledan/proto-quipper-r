module Primitive (
    hadamard,
    pauliX,
    qinit,
    qdiscard,
    cnot
) where

import qualified AST.Bundle as Bundle
import AST.Circuit
import AST.Language (Value(..))

import qualified Data.Map as Map
import AST.Bundle (WireType(..))

hadamard :: Value
hadamard = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a",Qubit)])) Hadamard (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
pauliX :: Value
pauliX = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a",Qubit)])) PauliX (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
qinit :: Value
qinit = BoxedCircuit Bundle.UnitValue (Seq (Id Map.empty) Init Bundle.UnitValue (Bundle.Label "a")) (Bundle.Label "a")
qdiscard :: Value
qdiscard = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a",Qubit)])) Discard (Bundle.Label "a") Bundle.UnitValue) Bundle.UnitValue
cnot :: Value
cnot = BoxedCircuit (Bundle.Pair (Bundle.Label "a1") (Bundle.Label "a2"))
    (Seq (Id (Map.fromList [("a1",Qubit),("a2",Qubit)])) CNot (Bundle.Pair (Bundle.Label "a1") (Bundle.Label "a2")) (Bundle.Pair (Bundle.Label "b1") (Bundle.Label "b2")))
    (Bundle.Pair (Bundle.Label "b1") (Bundle.Label "b2"))