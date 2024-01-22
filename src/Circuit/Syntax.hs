module Circuit.Syntax(
    QuantumOperation(..),
    sig,
    net,
    Circuit(..),
    width
) where
import PrettyPrinter
import WireBundle.Checking (LabelContext)
import WireBundle.Syntax
import qualified Data.Map as Map
data QuantumOperation
    = Init 
    | Discard 
    | Hadamard
    | PauliX 
    | CNot
    deriving (Eq,Show)

instance Pretty QuantumOperation where
    pretty Init = "Init"
    pretty Discard = "Discard"
    pretty Hadamard = "H"
    pretty PauliX = "X"
    pretty CNot = "CNot"

sig :: QuantumOperation -> (BundleType, BundleType)
sig Init     = (UnitType, WireType Qubit)
sig Discard  = (WireType Qubit, UnitType)
sig Hadamard = (WireType Qubit, WireType Qubit)
sig PauliX   = (WireType Qubit, WireType Qubit)
sig CNot     = (Tensor (WireType Qubit) (WireType Qubit), Tensor (WireType Qubit) (WireType Qubit))

net :: QuantumOperation -> Int
net Init    = 1
net Discard = -1
net _       = 0

data Circuit
    = Id LabelContext
    | Seq Circuit QuantumOperation Bundle Bundle
    deriving (Eq,Show)

instance Pretty Circuit where
    pretty (Id q) = "Inputs:" ++ pretty q
    pretty (Seq circ op bin bout) = pretty circ ++ "; " ++ pretty op ++ "(" ++ pretty bin ++ ") -> " ++ pretty bout


width :: Circuit -> Int
width (Id q) = Map.size q
width (Seq circ op _ _) = width circ + max 0 (net op - discarded circ)
    where discarded (Id _) = 0
          discarded (Seq circ op _ _) = max 0 (discarded circ - net op)




    