module Main (main) where
import Wire.Syntax
import qualified Data.Map as Map
import Control.Monad.State (StateT(runStateT))
import Language.Checking (checkValueType)
import Language.Syntax
import Circuit.Syntax
import Index
import qualified Data.Set as Set

main :: IO ()
main = do
        let term = BoxedCircuit (Label "a") (Op Hadamard (Label "a") (Label "b")) (Label "b")
        let check = runStateT (checkValueType term (Circ (Number 1) (WireType Qubit) (WireType Qubit))) (Set.empty, Map.empty, Map.empty)
        print check
        