module Index.Generators where

import Test.QuickCheck
import Index

generateIndex :: Int -> Gen Index
generateIndex 0 = oneof [
    Number <$> arbitrary,
    IndexVariable <$> arbitrary
    ]
generateIndex n = do
    n1 <- choose (0, n-1)
    n2 <- choose (0, n-1)
    oneof [
        Plus <$> generateIndex n1 <*> generateIndex n2,
        Max <$> generateIndex n1 <*> generateIndex n2
        ]

instance Arbitrary Index where
    arbitrary = sized generateIndex