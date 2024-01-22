module Language.Generators where

import Test.QuickCheck
import Language.Syntax

import WireBundle.Generators
import Index.Generators
import Circuit.Generators

generateValue :: Int -> Gen Value
generateValue 0 = oneof [
    return UnitValue,
    Label <$> arbitrary,
    Variable <$> arbitrary
    ]
generateValue n = do
    n1 <- choose (0, n-1)
    n2 <- choose (0, n-1)
    oneof [
        Pair <$> generateValue n1 <*> generateValue n2,
        BoxedCircuit <$> arbitrary <*> arbitrary <*> arbitrary,
        Abs <$> arbitrary <*> arbitrary <*> generateTerm n1,
        Lift <$> generateTerm n1
        ]

generateTerm :: Int -> Gen Term
generateTerm 0 = oneof [
    Apply <$> generateValue 0 <*> generateValue 0,
    Box <$> arbitrary <*> generateValue 0,
    Return <$> generateValue 0
    ]
generateTerm n = do
    n1 <- choose (0, n-1)
    n2 <- choose (0, n-1)
    oneof [
        Apply <$> generateValue n1 <*> generateValue n2,
        Box <$> arbitrary <*> generateValue n1,
        Dest <$> arbitrary <*> arbitrary <*> generateValue n1 <*> generateTerm n2,
        Return <$> generateValue n1,
        Let <$> arbitrary <*> generateTerm n1 <*> generateTerm n2,
        App <$> generateValue n1 <*> generateValue n2,
        Force <$> generateValue n1
        ]

generateType :: Int -> Gen Type
generateType 0 = oneof [
    return UnitType,
    WireType <$> arbitrary
    ]
generateType n = do
    n1 <- choose (0, n-1)
    n2 <- choose (0, n-1)
    oneof [
        Bang <$> generateType n1,
        Tensor <$> generateType n1 <*> generateType n2,
        Arrow <$> generateType n1 <*> generateType n2 <*> arbitrary <*> arbitrary,
        Circ <$> arbitrary <*> arbitrary <*> arbitrary
        ]

instance Arbitrary Value where
    arbitrary = sized generateValue

instance Arbitrary Term where
    arbitrary = sized generateTerm

instance Arbitrary Type where
    arbitrary = sized generateType

