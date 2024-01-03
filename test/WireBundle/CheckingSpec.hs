module WireBundle.CheckingSpec(spec) where
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.State.Lazy (execStateT, evalStateT)
import qualified Data.Map as Map
import Data.Either (isLeft)
import Test.Hspec ( Spec, describe, it, shouldBe, shouldSatisfy )
import WireBundle.Checking (synthesizeBundleType, LabelContext, checkBundleType, WireTypingError(..))
import WireBundle.Syntax

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

bundleCheckingSpec :: Spec
bundleCheckingSpec = do
    describe "wire bundle type checking" $ do
        it "fails when there are unused labels in the context" $ do
            -- a:Qubit ⊢ * <=/= Unit
            bundleCheckingTest UnitValue (Map.fromList [("a",Qubit)]) UnitType `shouldSatisfy` isLeft
            -- a:Qubit,b:Qubit ⊢ a <=/= Qubit
            bundleCheckingTest (Label "a") (Map.fromList [("a",Qubit),("b",Qubit)]) (WireType Qubit) `shouldSatisfy` isLeft

spec :: Spec
spec = do
    bundleSynthesisSpec
    bundleCheckingSpec