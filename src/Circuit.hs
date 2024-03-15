module Circuit
  ( QuantumOperation (..),
    sig,
    net,
    Circuit (..),
    width,
    inferCircuitSignature,
    qinit0,
    qinit1,
    qdiscard,
    measure,
    cnot,
    toffoli,
    hadamard,
    pauliX,
    pauliY,
    pauliZ,
  )
where

import Bundle.AST
import Bundle.Infer
  ( LabelContext,
    WireTypingError,
    runBundleTypeCheckingWithRemaining,
    synthesizeLabelContext,
  )
import qualified Data.HashMap.Strict as Map
import PrettyPrinter (Pretty (..))

--- QUANTUM OPERATIONS ---------------------------------------------------------------------------------

-- The datatype of elementary quantum operations
data QuantumOperation
  = QInit Bool
  | Discard
  | Measure
  | Hadamard
  | PauliX
  | PauliY
  | PauliZ
  | Phase
  | Toffoli
  | R Int
  | CNot
  deriving (Eq, Show)

instance Pretty QuantumOperation where
  pretty (QInit b) = "QInit" ++ if b then "1" else "0"
  pretty Discard = "QDiscard"
  pretty Hadamard = "H"
  pretty PauliX = "X"
  pretty PauliY = "Y"
  pretty PauliZ = "Z"
  pretty Measure = "Meas"
  pretty Phase = "S"
  pretty Toffoli = "Toffoli"
  pretty (R n) = "R(π/" ++ show n ++ ")"
  pretty CNot = "CNot"

-- Returns the signature (input/output types) of a quantum operation
sig :: QuantumOperation -> (BundleType, BundleType)
sig (QInit _) = (BTUnit, BTWire Qubit)
sig Discard = (BTWire Qubit, BTUnit)
sig Measure = (BTWire Qubit, BTWire Bit)
sig Hadamard = (BTWire Qubit, BTWire Qubit)
sig PauliX = (BTWire Qubit, BTWire Qubit)
sig PauliY = (BTWire Qubit, BTWire Qubit)
sig PauliZ = (BTWire Qubit, BTWire Qubit)
sig Phase = (BTWire Qubit, BTWire Qubit)
sig Toffoli = (BTPair (BTPair (BTWire Qubit) (BTWire Qubit)) (BTWire Qubit), BTPair (BTPair (BTWire Qubit) (BTWire Qubit)) (BTWire Qubit))
sig (R _) = (BTWire Qubit, BTWire Qubit)
sig CNot = (BTPair (BTWire Qubit) (BTWire Qubit), BTPair (BTWire Qubit) (BTWire Qubit))

-- Returns the net change in the number of qubits after applying a quantum operation
-- E.g. if a quantum operation consumes 2 qubits and produces 1 qubit, then the net change is -1
-- E.g. if a quantum operation consumes 0 qubits and produces 1 qubit, then the net change is 1
net :: QuantumOperation -> Int
net (QInit _) = 1
net Discard = -1
net _ = 0

--- CIRCUITS ---------------------------------------------------------------------------------

-- The datatype of quantum circuits (Fig. 9)
-- A circuit is either the identity circuit on some labels,
-- or a circuit, followed by a quantum operation consuming some wires and outputting some wires
data Circuit
  = Id LabelContext -- ID_Q
  | Seq Circuit QuantumOperation Bundle Bundle -- C; g(b1) -> b2
  deriving (Eq, Show)

instance Pretty Circuit where
  pretty (Id q) = "Inputs:" ++ pretty q
  pretty (Seq circ op bin bout) = pretty circ ++ "; " ++ pretty op ++ "(" ++ pretty bin ++ ") -> " ++ pretty bout

-- Returns the width of a circuit
-- Def. 1 (Circuit Width)
width :: Circuit -> Int
width (Id q) = Map.size q -- if the circuit is the identity circuit on q, then the width is the wire count of q
width (Seq circ op _ _) = width circ + max 0 (net op - discarded circ) -- we reuse as many previously discarded wires as possible
  where
    discarded :: Circuit -> Int
    discarded (Id _) = 0
    discarded (Seq circ op _ _) = max 0 (discarded circ - net op)

-- C => Q -> L (Fig. 10)
-- inferCircuitSignature c infers the circuit signature of c
-- If succesful, it returns a pair of the input and output labels of c, respectively
-- Otherwise, it returns a WireTypingError
inferCircuitSignature :: Circuit -> Either WireTypingError (LabelContext, LabelContext)
inferCircuitSignature (Id q) = Right (q, q)
inferCircuitSignature (Seq circ op bin bout) = do
  (qin, qmid) <- inferCircuitSignature circ
  let (btype1, btype2) = sig op
  qout1 <- runBundleTypeCheckingWithRemaining qmid bin btype1
  qout2 <- synthesizeLabelContext bout btype2
  return (qin, Map.union qout1 qout2)

--- PRIMITIVE CIRCUITS ---------------------------------------------------------------------------------

qinit0 :: Circuit
qinit0 = Seq (Id Map.empty) (QInit False) UnitValue (Label "a")

qinit1 :: Circuit
qinit1 = Seq (Id Map.empty) (QInit True) UnitValue (Label "a")

qdiscard :: Circuit
qdiscard = Seq (Id (Map.fromList [("a", Qubit)])) Discard (Label "a") UnitValue

measure :: Circuit
measure = Seq (Id (Map.fromList [("a", Qubit)])) Measure (Label "a") (Label "b")

cnot :: Circuit
cnot = Seq (Id (Map.fromList [("a", Qubit), ("b", Qubit)])) CNot (Pair (Label "a") (Label "b")) (Pair (Label "c") (Label "d"))

toffoli :: Circuit
toffoli = Seq (Id (Map.fromList [("a", Qubit), ("b", Qubit), ("c", Qubit)])) Toffoli (Pair (Pair (Label "a") (Label "b")) (Label "c")) (Pair (Pair (Label "d") (Label "e")) (Label "f"))

hadamard :: Circuit
hadamard = Seq (Id (Map.fromList [("a", Qubit)])) Hadamard (Label "a") (Label "b")

pauliX :: Circuit
pauliX = Seq (Id (Map.fromList [("a", Qubit)])) PauliX (Label "a") (Label "b")

pauliY :: Circuit
pauliY = Seq (Id (Map.fromList [("a", Qubit)])) PauliY (Label "a") (Label "b")

pauliZ :: Circuit
pauliZ = Seq (Id (Map.fromList [("a", Qubit)])) PauliZ (Label "a") (Label "b")