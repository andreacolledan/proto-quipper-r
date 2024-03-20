module Lang.Unified.Constant (
  Constant(..),
  typeOf
) where
import PrettyPrinter
import Lang.Type.AST
import Index.AST
import Bundle.AST (BundleType(..), WireType (..))

--- CONSTANTS -----------------------------------------------------------------------------------------------
---
--- This module defines the constants of the PQR language.
-------------------------------------------------------------------------------------------------------------

-- Enum of constants
data Constant
  -- Qubit metaoperations
  = QInit0
  | QInit1
  | QDiscard
  | Meas
  -- Bit metaoperations
  | CInit0
  | CInit1
  | CDiscard
  -- Single qubit gates
  | Hadamard
  | PauliX
  | PauliY
  | PauliZ
  -- Two qubit gates
  | CNot
  -- Three qubit gates
  | Toffoli
  -- Functions
  | MakeCRGate
  deriving (Eq, Show)

instance Pretty Constant where
  pretty QInit0 = "QInit0"
  pretty QInit1 = "QInit1"
  pretty QDiscard = "QDiscard"
  pretty CInit0 = "CInit0"
  pretty CInit1 = "CInit1"
  pretty CDiscard = "CDiscard"
  pretty Meas = "Meas"
  pretty Hadamard = "Hadamard"
  pretty PauliX = "PauliX"
  pretty PauliY = "PauliY"
  pretty PauliZ = "PauliZ"
  pretty CNot = "CNot"
  pretty Toffoli = "Toffoli"
  pretty MakeCRGate = "MakeCRGate"

-- | @typeOf c@ returns the type of constant @c@
typeOf :: Constant -> Type
typeOf QInit0 = TCirc (Number 1) BTUnit (BTWire Qubit)
typeOf QInit1 = TCirc (Number 1) BTUnit (BTWire Qubit)
typeOf QDiscard = TCirc (Number 1) (BTWire Qubit) BTUnit
typeOf Meas = TCirc (Number 1) (BTWire Qubit) (BTWire Bit)
typeOf CInit0 = TCirc (Number 1) BTUnit (BTWire Bit)
typeOf CInit1 = TCirc (Number 1) BTUnit (BTWire Bit)
typeOf CDiscard = TCirc (Number 1) (BTWire Bit) BTUnit
typeOf Hadamard = TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)
typeOf PauliX = TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)
typeOf PauliY = TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)
typeOf PauliZ = TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)
typeOf CNot = TCirc (Number 2) (BTPair (BTWire Qubit) (BTWire Qubit)) (BTPair (BTWire Qubit) (BTWire Qubit))
typeOf Toffoli = TCirc (Number 3) (BTPair (BTPair (BTWire Qubit) (BTWire Qubit)) (BTWire Qubit)) (BTPair (BTPair (BTWire Qubit) (BTWire Qubit)) (BTWire Qubit))
typeOf MakeCRGate = TIForall "i" (TCirc (Number 2) (BTPair (BTWire Qubit) (BTWire Qubit)) (BTPair (BTWire Qubit) (BTWire Qubit))) (Number 0) (Number 0)
