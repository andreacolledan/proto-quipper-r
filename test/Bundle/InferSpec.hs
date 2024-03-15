module Bundle.InferSpec (spec) where

import Bundle.AST
import Bundle.Infer
  ( runBundleTypeChecking,
    runBundleTypeInference,
    synthesizeLabelContext,
  )
import Data.Either (isLeft, isRight)
import qualified Data.HashMap.Strict as Map
import Index.AST
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)

-- SPECIFICATION --

spec :: Spec
spec = do
  describe "bundle type inference" $ do
    it "infers the correct type for the unit value" $ do
      -- ∅ ⊢ * => Unit
      runBundleTypeInference Map.empty UnitValue `shouldBe` Right BTUnit
    it "infers the correct type for a label" $ do
      -- a:Qubit ⊢ a => Qubit
      runBundleTypeInference (Map.fromList [("a", Qubit)]) (Label "a") `shouldBe` Right (BTWire Qubit)
      -- a:Bit ⊢ a => Bit
      runBundleTypeInference (Map.fromList [("a", Bit)]) (Label "a") `shouldBe` Right (BTWire Bit)
  -- TODO
  describe "bundle type checking" $ do
    it "succeeds on the empty list" $ do
      -- ∅ ⊢ [] <== List[0] Qubit
      runBundleTypeChecking Map.empty Nil (BTList (Number 0) (BTWire Qubit)) `shouldSatisfy` isRight
      -- ∅ ⊢ [] <== List[0] Bit
      runBundleTypeChecking Map.empty Nil (BTList (Number 0) (BTWire Bit)) `shouldSatisfy` isRight
    it "succeeds on a list of the correct length" $ do
      -- a:Qubit,b:Qubit ⊢ [a,b] <== List[2] Qubit
      runBundleTypeChecking (Map.fromList [("a", Qubit), ("b", Qubit)]) (Cons (Label "a") (Cons (Label "b") Nil)) (BTList (Number 2) (BTWire Qubit)) `shouldSatisfy` isRight
    it "fails on a list of the incorrect length" $ do
      -- a:Qubit,b:Qubit ⊢ [a,b] <=/= List[1] Qubit
      runBundleTypeChecking (Map.fromList [("a", Qubit), ("b", Qubit)]) (Cons (Label "a") (Cons (Label "b") Nil)) (BTList (Number 1) (BTWire Qubit)) `shouldSatisfy` isLeft
    it "fails when there are unused labels in the context" $ do
      -- a:Qubit ⊢ * <=/= Unit
      runBundleTypeChecking (Map.fromList [("a", Qubit)]) UnitValue BTUnit `shouldSatisfy` isLeft
      -- a:Qubit,b:Qubit ⊢ a <=/= Qubit
      runBundleTypeChecking (Map.fromList [("a", Qubit), ("b", Qubit)]) (Label "a") (BTWire Qubit) `shouldSatisfy` isLeft
    it "fails when the checking against the incorrect type" $ do
      -- a:Qubit ⊢ a <=/= Bit
      runBundleTypeChecking (Map.fromList [("a", Qubit)]) (Label "a") (BTWire Bit) `shouldSatisfy` isLeft
      -- a:Qubit,b:Bit ⊢ (a,b) <=/= Qubit ⊗ Qubit
      runBundleTypeChecking (Map.fromList [("a", Qubit), ("b", Bit)]) (Pair (Label "a") (Label "b")) (BTPair (BTWire Qubit) (BTWire Qubit)) `shouldSatisfy` isLeft
  describe "context synthesis" $ do
    it "succeeds when a wire bundle and a wire type have the same shape" $ do
      -- ∅ <== * : Unit
      synthesizeLabelContext UnitValue BTUnit `shouldBe` Right Map.empty
      -- a:Qubit <== a : Qubit
      synthesizeLabelContext (Label "a") (BTWire Qubit) `shouldBe` Right (Map.fromList [("a", Qubit)])
      -- a:Qubit,b:Bit <== (a,b) : Qubit ⊗ Bit
      synthesizeLabelContext (Pair (Label "a") (Label "b")) (BTPair (BTWire Qubit) (BTWire Bit))
        `shouldBe` Right (Map.fromList [("a", Qubit), ("b", Bit)])
      -- a:Qubit,b:Bit,c:Qubit <== ((*,a),(b,c)) : (Unit ⊗ Qubit) ⊗ (Bit ⊗ Qubit)
      synthesizeLabelContext
        (Pair (Pair UnitValue (Label "a")) (Pair (Label "b") (Label "c")))
        (BTPair (BTPair BTUnit (BTWire Qubit)) (BTPair (BTWire Bit) (BTWire Qubit)))
        `shouldBe` Right (Map.fromList [("a", Qubit), ("b", Bit), ("c", Qubit)])
    it "fails when a bundle and a bundle type do not have the same shape" $ do
      -- <=/= * : Qubit
      synthesizeLabelContext UnitValue (BTWire Qubit) `shouldSatisfy` isLeft
      -- <=/= a : Qubit ⊗ Bit
      synthesizeLabelContext (Label "a") (BTPair (BTWire Qubit) (BTWire Bit)) `shouldSatisfy` isLeft
      -- <=/= (a,b) : Qubit
      synthesizeLabelContext (Pair (Label "a") (Label "b")) (BTWire Qubit) `shouldSatisfy` isLeft
      -- <=/= ((*,a),(b,c)) : (Unit ⊗ Qubit) ⊗ Bit
      synthesizeLabelContext
        (Pair (Pair UnitValue (Label "a")) (Pair (Label "b") (Label "c")))
        (BTPair (BTPair BTUnit (BTWire Qubit)) (BTWire Bit))
        `shouldSatisfy` isLeft
    it "fails when a type variable occurs in the bundle type" $ do
      -- <=/= a : ⍺
      synthesizeLabelContext (Label "a") (BTVar "⍺") `shouldSatisfy` isLeft
