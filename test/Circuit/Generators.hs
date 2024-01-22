module Circuit.Generators where

import Test.QuickCheck
import Circuit.Syntax

import WireBundle.Generators

generateCircuit :: Int -> Gen Circuit
generateCircuit 0 = Id <$> arbitrary
generateCircuit n = Seq <$> generateCircuit (n-1) <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary Circuit where
    arbitrary = sized generateCircuit

instance Arbitrary QuantumOperation where
    arbitrary = oneof [
        return Init,
        return Circuit.Syntax.Discard,
        return Hadamard,
        return PauliX,
        return CNot
        ]