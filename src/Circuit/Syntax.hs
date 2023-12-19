module Circuit.Syntax where
import Wire.Syntax

data QuantumOperation
    = Init 
    | Discard 
    | Hadamard
    | PauliX 

-- For now, only primitive circuits corresponding to gates
data Circuit = Op QuantumOperation Bundle Bundle




    