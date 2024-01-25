module Language.SyntaxSpec (
    spec
) where

import Test.Hspec

import Language.Syntax as Lang
import WireBundle.Syntax as Wire
import Index 
import qualified Data.Set as Set


-- SPECIFICATION --

syntaxSpec :: Spec
syntaxSpec = do 
    describe "toBundleType" $ do
        it "turns the language's unit type into the wire unit type" $ do
            toBundleType Lang.UnitType `shouldBe` Just Wire.UnitType
        it "turns the language's Bit and Qubit types into the wire Qubit and Bit types" $ do
            toBundleType (Lang.WireType Bit)  `shouldBe` Just (Wire.WireType Bit)
            toBundleType (Lang.WireType Qubit) `shouldBe` Just (Wire.WireType Qubit)
        it "turns a complex type comprised of pairs of Unit, Qubit and Bit into an identical bundle type" $ do
            -- ((Unit, Qubit), Bit)
            toBundleType (Lang.Tensor (Lang.Tensor Lang.UnitType (Lang.WireType Qubit)) (Lang.WireType Bit))
                `shouldBe` Just (Wire.Tensor (Wire.Tensor Wire.UnitType (Wire.WireType Qubit)) (Wire.WireType Bit))
            -- (Bit, (Bit, (Qubit, Qubit)))
            toBundleType (Lang.Tensor (Lang.WireType Bit) (Lang.Tensor (Lang.WireType Bit) (Lang.Tensor (Lang.WireType Qubit) (Lang.WireType Qubit))))
                `shouldBe` Just (Wire.Tensor (Wire.WireType Bit) (Wire.Tensor (Wire.WireType Bit) (Wire.Tensor (Wire.WireType Qubit) (Wire.WireType Qubit))))
        it "returns nothing on a type that cannot be interpreted as a bundle type" $ do
            -- (Bit, Bang Unit) FAILS
            toBundleType (Lang.Tensor (Lang.WireType Bit) (Lang.Bang Lang.UnitType)) `shouldBe` Nothing
            -- Circ 1 Qubit Qubit FAILS
            toBundleType (Lang.Circ (Index.Number 1) (Wire.WireType Qubit) (Wire.WireType Qubit)) `shouldBe` Nothing

    describe "wireCount" $ do
        it "returns 0 on parameter types" $ do
            wireCount Lang.UnitType `shouldBe` Number 0
            wireCount (Lang.Circ (Index.Number 1) (Wire.WireType Qubit) (Wire.WireType Qubit)) `shouldBe` Number 0
            wireCount (Bang Lang.UnitType) `shouldBe` Number 0
        it "returns 1 on wire types" $ do
            wireCount (Lang.WireType Bit) `shouldBe` Number 1
            wireCount (Lang.WireType Qubit) `shouldBe` Number 1
        it "returns the sum of the wire counts of the components of a tensor type" $ do
            wireCount (Lang.Tensor (Lang.WireType Bit) (Lang.WireType Qubit)) `shouldSatisfy` checkEq Set.empty (Number 2)
            wireCount (Lang.Tensor (Lang.Tensor (Lang.WireType Bit) (Lang.WireType Qubit)) (Lang.WireType Qubit)) `shouldSatisfy` checkEq Set.empty (Number 3)
        it "returns the arrows second annotation" $ do
            wireCount (Lang.Arrow (Lang.WireType Bit) (Lang.WireType Qubit) (Number 2) (Number 2)) `shouldBe` Number 2 

spec :: Spec
spec = do
    syntaxSpec