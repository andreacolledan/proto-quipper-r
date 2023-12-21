module Circuit.Syntax where
import Wire.Syntax
import PrettyPrinter

data QuantumOperation
    = Init 
    | Discard 
    | Hadamard
    | PauliX 
    deriving Show

instance Pretty QuantumOperation where
    pretty Init = "Init"
    pretty Discard = "Discard"
    pretty Hadamard = "H"
    pretty PauliX = "X"

-- For now, only primitive circuits corresponding to gates
data Circuit
    = Op QuantumOperation Bundle Bundle
    deriving Show

instance Pretty Circuit where
    pretty (Op op b1 b2) = pretty op ++ "(" ++ pretty b1 ++ ") -> " ++ pretty b2

-- For now, all circuits have width 1
width :: Circuit -> Int
width _ = 1




    