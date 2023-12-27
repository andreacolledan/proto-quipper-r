module Circuit.Checking where
import Circuit.Syntax
import WireBundle.Checking
import WireBundle.Syntax

sig :: QuantumOperation -> (BundleType, BundleType)
sig Init     = (UnitType, WireType Qubit)
sig Discard  = (WireType Qubit, UnitType)
sig Hadamard = (WireType Qubit, WireType Qubit)
sig PauliX   = (WireType Qubit, WireType Qubit)
sig CNot     = (Tensor (WireType Qubit) (WireType Qubit), Tensor (WireType Qubit) (WireType Qubit))

-- Will change dramatically
inferCircuitSignature :: Circuit -> Either String (LabelContext, LabelContext)
inferCircuitSignature (Op op inB outB) = do
    let (inBtype, outBtype) = sig op
    inq <- synthesizeLabelContext inB inBtype
    outq <- synthesizeLabelContext outB outBtype
    return (inq, outq)

