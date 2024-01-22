module WireBundle.Generators where

import Test.QuickCheck
import WireBundle.Syntax

generateBundle :: Int -> Gen Bundle
generateBundle 0 = oneof [
    return UnitValue,
    Label <$> arbitrary
    ]
generateBundle n = do
    n1 <- choose (0, n-1)
    n2 <- choose (0, n-1)
    Pair <$> generateBundle n1 <*> generateBundle n2


generateBundleType :: Int -> Gen BundleType
generateBundleType 0 = oneof [
    return UnitType,
    WireType <$> arbitrary
    ]
generateBundleType n = do
    n1 <- choose (0, n-1)
    n2 <- choose (0, n-1)
    Tensor <$> generateBundleType n1 <*> generateBundleType n2

instance Arbitrary Bundle where
    arbitrary = sized generateBundle

instance Arbitrary WireType where
    arbitrary = oneof [return Qubit, return Bit]

instance Arbitrary BundleType where
    arbitrary = sized generateBundleType