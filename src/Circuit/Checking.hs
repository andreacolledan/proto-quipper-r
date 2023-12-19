module Circuit.Checking where
import Circuit.Syntax
import Wire.Checking
import Wire.Syntax
import Data.Either.Extra

data CircuitTypeError 
    = BundleTypeError BundleTypeError
    | OtherCircuitTyperError String

sig :: QuantumOperation -> (BundleType,BundleType)
sig Init = (UnitType, WireType Qubit)
sig Discard = (WireType Qubit, UnitType)
sig Hadamard = (WireType Qubit, WireType Qubit)
sig PauliX = (WireType Qubit, WireType Qubit)

--Will change dramatically
circuitInfer :: Circuit -> Either CircuitTypeError (LabelContext,LabelContext)
circuitInfer (Op g l k) = do
    let (t,u) = sig g
    q1 <- mapLeft BundleTypeError (inferLabelContext l t)
    q2 <- mapLeft BundleTypeError (inferLabelContext k u)
    return (q1,q2)

circuitCheck :: Circuit -> LabelContext -> LabelContext -> Bool
circuitCheck c q1 q2 = case circuitInfer c of
    Left _ -> False
    Right (q1',q2') -> q1' == q1 && q2' == q2

