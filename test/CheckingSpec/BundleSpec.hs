module CheckingSpec.BundleSpec (spec) where

import AST.Bundle
import AST.Index
import Checking.Bundle (synthesizeBundleType, LabelContext, checkBundleType, WireTypingError(..), synthesizeLabelContext)

import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.State.Lazy (execStateT, evalStateT)
import Data.Either (isLeft, isRight)
import qualified Data.Map as Map
import Test.Hspec


-- SPECIFICATION --


bundleSynthesisTest :: Bundle -> LabelContext -> Either WireTypingError BundleType
bundleSynthesisTest b = evalStateT (synthesizeBundleType b)

bundleCheckingTest :: Bundle -> LabelContext -> BundleType -> Either WireTypingError ()
bundleCheckingTest b q btype = case execStateT (checkBundleType b btype) q of
    Left err -> throwError err
    Right q' -> do
        unless (Map.null q') $ throwError $ UnusedLabels q'

bundleSynthesisSpec :: Spec
bundleSynthesisSpec = do
    describe "wire bundle type synthesis" $ do
        it "synthesizes the unit type for the unit value" $ do
            -- ∅ ⊢ * => Unit
            bundleSynthesisTest UnitValue Map.empty `shouldBe` Right UnitType
        it "synthesizes the correct type of a single label in the context" $ do
            -- a:Qubit ⊢ a => Qubit
            bundleSynthesisTest (Label "a") (Map.fromList [("a",Qubit)]) `shouldBe` Right (WireType Qubit)
            -- a:Bit ⊢ a => Bit
            bundleSynthesisTest (Label "a") (Map.fromList [("a",Bit)]) `shouldBe` Right (WireType Bit)
        it "synthesizes the correct tensor type for a pair of labels" $ do
            -- a:Qubit,b:Bit ⊢ (a,b) => Qubit ⊗ Bit
            bundleSynthesisTest (Pair (Label "a") (Label "b")) (Map.fromList [("a",Qubit),("b",Bit)])
                `shouldBe` Right (Tensor (WireType Qubit) (WireType Bit))
        it "synthesizes the correct tensor type for complex bundles" $ do
            -- a:Qubit,b:Bit,c:Qubit ⊢ ((*,a),(b,c)) => (Unit ⊗ Qubit) ⊗ (Bit ⊗ Qubit)
            bundleSynthesisTest (Pair (Pair UnitValue (Label "a")) (Pair (Label "b") (Label "c")))
                (Map.fromList [("a",Qubit),("b",Bit),("c",Qubit)])
                `shouldBe` Right (Tensor (Tensor UnitType (WireType Qubit)) (Tensor (WireType Bit) (WireType Qubit)))
        it "fails when a label is unbound in the context" $ do
            -- ∅ ⊢ a =/=>
            bundleSynthesisTest (Label "a") Map.empty `shouldSatisfy` isLeft
            -- a:Qubit ⊢ (a,b) =/=>
            bundleSynthesisTest (Pair (Label "a") (Label "b")) (Map.fromList [("a",Qubit)]) `shouldSatisfy` isLeft
        it "fails when a label is used more than once" $ do
            -- a:Qubit ⊢ (a,a) =/=>
            bundleSynthesisTest (Pair (Label "a") (Label "a")) (Map.fromList [("a",Qubit)]) `shouldSatisfy` isLeft

contextSynthesisSpec :: Spec
contextSynthesisSpec = do
    describe "context synthesis" $ do
        it "succeeds when a wire bundle and a wire type have the same shape" $ do
            -- ∅ <== * : Unit
            synthesizeLabelContext UnitValue UnitType `shouldBe` Right Map.empty
            -- a:Qubit <== a : Qubit
            synthesizeLabelContext (Label "a") (WireType Qubit) `shouldBe` Right (Map.fromList [("a",Qubit)])
            -- a:Qubit,b:Bit <== (a,b) : Qubit ⊗ Bit
            synthesizeLabelContext (Pair (Label "a") (Label "b")) (Tensor (WireType Qubit) (WireType Bit))
                `shouldBe` Right (Map.fromList [("a",Qubit),("b",Bit)])
            -- a:Qubit,b:Bit,c:Qubit <== ((*,a),(b,c)) : (Unit ⊗ Qubit) ⊗ (Bit ⊗ Qubit)
            synthesizeLabelContext (Pair (Pair UnitValue (Label "a")) (Pair (Label "b") (Label "c")))
                (Tensor (Tensor UnitType (WireType Qubit)) (Tensor (WireType Bit) (WireType Qubit)))
                `shouldBe` Right (Map.fromList [("a",Qubit),("b",Bit),("c",Qubit)])
        it "fails when a wire bundle and a wire type do not have the same shape" $ do
            -- <=/= * : Qubit
            synthesizeLabelContext UnitValue (WireType Qubit) `shouldSatisfy` isLeft
            -- <=/= a : Qubit ⊗ Bit
            synthesizeLabelContext (Label "a") (Tensor (WireType Qubit) (WireType Bit)) `shouldSatisfy` isLeft
            -- <=/= (a,b) : Qubit
            synthesizeLabelContext (Pair (Label "a") (Label "b")) (WireType Qubit) `shouldSatisfy` isLeft
            -- <=/= ((*,a),(b,c)) : (Unit ⊗ Qubit) ⊗ Bit
            synthesizeLabelContext (Pair (Pair UnitValue (Label "a")) (Pair (Label "b") (Label "c")))
                (Tensor (Tensor UnitType (WireType Qubit)) (WireType Bit))
                `shouldSatisfy` isLeft


bundleCheckingSpec :: Spec
bundleCheckingSpec = do
    describe "wire bundle type checking" $ do
        it "succeeds on the empty list" $ do
            -- ∅ ⊢ [] <== List[0] Qubit
            bundleCheckingTest Nil Map.empty (List (Number 0) (WireType Qubit)) `shouldSatisfy` isRight
            -- ∅ ⊢ [] <== List[0] Bit
            bundleCheckingTest Nil Map.empty (List (Number 0) (WireType Bit)) `shouldSatisfy` isRight
        it "succeeds on a list of the correct length" $ do
            -- a:Qubit,b:Qubit ⊢ [a,b] <== List[2] Qubit
            bundleCheckingTest (Cons (Label "a") (Cons (Label "b") Nil)) (Map.fromList [("a",Qubit),("b",Qubit)]) (List (Number 2) (WireType Qubit)) `shouldSatisfy` isRight
        it "fails on a list of the incorrect length" $ do
            -- a:Qubit,b:Qubit ⊢ [a,b] <=/= List[1] Qubit
            bundleCheckingTest (Cons (Label "a") (Cons (Label "b") Nil)) (Map.fromList [("a",Qubit),("b",Qubit)]) (List (Number 1) (WireType Qubit)) `shouldSatisfy` isLeft
        it "fails when there are unused labels in the context" $ do
            -- a:Qubit ⊢ * <=/= Unit
            bundleCheckingTest UnitValue (Map.fromList [("a",Qubit)]) UnitType `shouldSatisfy` isLeft
            -- a:Qubit,b:Qubit ⊢ a <=/= Qubit
            bundleCheckingTest (Label "a") (Map.fromList [("a",Qubit),("b",Qubit)]) (WireType Qubit) `shouldSatisfy` isLeft
        it "fails when the synthesised type and the checked type do not match" $ do
            -- a:Qubit ⊢ a <=/= Bit
            bundleCheckingTest (Label "a") (Map.fromList [("a",Qubit)]) (WireType Bit) `shouldSatisfy` isLeft
            -- a:Qubit,b:Bit ⊢ (a,b) <=/= Qubit ⊗ Qubit
            bundleCheckingTest (Pair (Label "a") (Label "b")) (Map.fromList [("a",Qubit),("b",Bit)]) (Tensor (WireType Qubit) (WireType Qubit)) `shouldSatisfy` isLeft

spec :: Spec
spec = do
    bundleSynthesisSpec
    contextSynthesisSpec
    bundleCheckingSpec