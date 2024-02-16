module Lang.Paper.ASTSpec (spec) where

import Bundle.AST
import Index.AST
import Index.Semantics
import Lang.Paper.AST
import Test.Hspec

-- SPECIFICATION --

syntaxSpec :: Spec
syntaxSpec = do
  describe "toBundleType" $ do
    it "turns the language's unit type into the wire unit type" $ do
      toBundleType TUnit `shouldBe` Just BTUnit
    it "turns the language's Bit and Qubit types into the wire Qubit and Bit types" $ do
      toBundleType (TWire Bit) `shouldBe` Just (BTWire Bit)
      toBundleType (TWire Qubit) `shouldBe` Just (BTWire Qubit)
    it "turns a complex type comprised of pairs of Unit, Qubit and Bit into an identical bundle type" $ do
      -- ((Unit, Qubit), Bit)
      toBundleType (TPair (TPair TUnit (TWire Qubit)) (TWire Bit))
        `shouldBe` Just (BTPair (BTPair BTUnit (BTWire Qubit)) (BTWire Bit))
      -- (Bit, (Bit, (Qubit, Qubit)))
      toBundleType (TPair (TWire Bit) (TPair (TWire Bit) (TPair (TWire Qubit) (TWire Qubit))))
        `shouldBe` Just (BTPair (BTWire Bit) (BTPair (BTWire Bit) (BTPair (BTWire Qubit) (BTWire Qubit))))
    it "returns nothing on a type that cannot be interpreted as a bundle type" $ do
      -- (Bit, TBang Unit) FAILS
      toBundleType (TPair (TWire Bit) (TBang TUnit)) `shouldBe` Nothing
      -- Circ 1 Qubit Qubit FAILS
      toBundleType (TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)) `shouldBe` Nothing

  describe "wireCount" $ do
    it "returns 0 on parameter types" $ do
      wireCount TUnit `shouldBe` Number 0
      wireCount (TCirc (Number 1) (BTWire Qubit) (BTWire Qubit)) `shouldBe` Number 0
      wireCount (TBang TUnit) `shouldBe` Number 0
    it "returns 1 on wire types" $ do
      wireCount (TWire Bit) `shouldBe` Number 1
      wireCount (TWire Qubit) `shouldBe` Number 1
    it "returns the sum of the wire counts of the components of a tensor type" $ do
      wireCount (TPair (TWire Bit) (TWire Qubit)) `shouldSatisfy` checkEq (Number 2)
      wireCount (TPair (TPair (TWire Bit) (TWire Qubit)) (TWire Qubit)) `shouldSatisfy` checkEq (Number 3)
    it "returns the arrows second annotation" $ do
      wireCount (TArrow (TWire Bit) (TWire Qubit) (Number 2) (Number 2)) `shouldBe` Number 2

spec :: Spec
spec = do
  syntaxSpec
