module Circuit.Syntax where
import Wire.Syntax

data QuantumOperation
    = Init 
    | Discard 
    | Hadamard
    | PauliX 
    deriving Show

-- For now, only primitive circuits corresponding to gates
data Circuit
    = Op QuantumOperation Bundle Bundle
    deriving Show

-- For now, all circuits have width 1
width :: Circuit -> Int
width _ = 1




    