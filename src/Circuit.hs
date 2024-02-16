module Circuit
  ( QuantumOperation (..),
    sig,
    net,
    Circuit (..),
    width,
    inferCircuitSignature,
  )
where

import Bundle.AST
  ( Bundle,
    BundleType (Tensor, UnitType, WireType),
    WireType (Qubit),
  )
import Bundle.Infer
  ( LabelContext,
    WireTypingError,
    runBundleTypeCheckingWithRemaining,
    synthesizeLabelContext,
  )
import qualified Data.Map as Map
import PrettyPrinter (Pretty (..))

--- QUANTUM OPERATIONS ---------------------------------------------------------------------------------

-- The datatype of elementary quantum operations
data QuantumOperation
  = Init
  | Discard
  | Hadamard
  | PauliX
  | CNot
  deriving (Eq, Show)

instance Pretty QuantumOperation where
  pretty Init = "Init"
  pretty Discard = "Discard"
  pretty Hadamard = "H"
  pretty PauliX = "X"
  pretty CNot = "CNot"

-- Returns the signature (input/output types) of a quantum operation
sig :: QuantumOperation -> (BundleType, BundleType)
sig Init = (UnitType, WireType Qubit)
sig Discard = (WireType Qubit, UnitType)
sig Hadamard = (WireType Qubit, WireType Qubit)
sig PauliX = (WireType Qubit, WireType Qubit)
sig CNot = (Tensor (WireType Qubit) (WireType Qubit), Tensor (WireType Qubit) (WireType Qubit))

-- Returns the net change in the number of qubits after applying a quantum operation
-- E.g. if a quantum operation consumes 2 qubits and produces 1 qubit, then the net change is -1
-- E.g. if a quantum operation consumes 0 qubits and produces 1 qubit, then the net change is 1
net :: QuantumOperation -> Int
net Init = 1
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