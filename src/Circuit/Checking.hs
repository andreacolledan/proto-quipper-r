module Circuit.Checking where
import Circuit.Syntax
import Wire.Checking
import Wire.Syntax
import Data.Either.Extra

sig :: QuantumOperation -> (BundleType,BundleType)
sig Init = (UnitType, WireType Qubit)
sig Discard = (WireType Qubit, UnitType)
sig Hadamard = (WireType Qubit, WireType Qubit)
sig PauliX = (WireType Qubit, WireType Qubit)

--Will change dramatically
inferCircuitSignature :: Circuit -> Either String (LabelContext,LabelContext)
inferCircuitSignature (Op g l k) = do
    let (t,u) = sig g
    q1 <- inferLabelContext l t
    q2 <- inferLabelContext k u
    return (q1,q2)

