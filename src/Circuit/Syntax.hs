module Circuit.Syntax where
import WireBundle.Syntax
import PrettyPrinter

data QuantumOperation
    = Init 
    | Discard 
    | Hadamard
    | PauliX 
    | CNot
    deriving Show

instance Pretty QuantumOperation where
    pretty Init = "Init"
    pretty Discard = "Discard"
    pretty Hadamard = "H"
    pretty PauliX = "X"
    pretty CNot = "CNot"

-- For now, only primitive circuits corresponding to gates
data Circuit
    = Op QuantumOperation Bundle Bundle
    deriving Show

instance Pretty Circuit where
    pretty (Op op _ _) = pretty op

-- For now, all circuits have width 1
width :: Circuit -> Int
width _ = 1




    