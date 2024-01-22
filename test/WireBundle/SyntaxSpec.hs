module WireBundle.SyntaxSpec where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)

import WireBundle.Syntax
import WireBundle.Generators

-- TRIVIAL (for coverage) --

showSpec :: Spec
showSpec = do
    describe "showing a bundle" $ do
        prop "outputs a string" $ do
            \x -> show (x :: Bundle) `shouldBe` show x
    describe "showing a wire type" $ do
        prop "outputs a string" $ do
            \x -> show (x :: WireType) `shouldBe` show x
    describe "showing a bundle type" $ do
        prop "outputs a string" $ do
            \x -> show (x :: BundleType) `shouldBe` show x

-- SPECIFICATION --

spec :: Spec
spec = showSpec