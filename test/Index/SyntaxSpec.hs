module Index.SyntaxSpec where

import Test.Hspec
import Test.Hspec.QuickCheck (prop, modifyMaxSize)

import Index
import Index.Generators
import PrettyPrinter

-- TRIVIAL (for coverage) --

showSpec :: Spec
showSpec = do
    describe "showing an index" $ do
        modifyMaxSize (const 5) $ prop "outputs a string" $ do
            \x -> pretty (x :: Index) `shouldBe` pretty x

-- SPECIFICATION --

spec :: Spec
spec = showSpec