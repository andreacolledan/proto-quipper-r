module Main (main) where
import qualified Data.Map as Map
import Index
import qualified Data.Set as Set
import Language.Syntax (Value(..), Term(..), Type(..))
import WireBundle.Syntax (WireType(..))
import Test.Hspec
import Language.CheckingSpec
import WireBundle.CheckingSpec
import Data.Either (isRight, isLeft)

assortedSpec :: Spec
assortedSpec = do
        describe "term checking" $ do
                it "succeeds when the term is well-typed" $ do
                        -- ∅;∅;l:Qubit ⊢ Apply (Hadamard,l) <= Qubit ; 1
                        let term = Apply hadamard $ Label "l"
                        let (theta,gamma,q) = (Set.empty, Map.empty, Map.fromList [("l",Qubit)])
                        let (typ, index) = (WireType Qubit, Number 1)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
                        -- ∅;∅;∅ ⊢ Apply (Init,*) <= Qubit ; 1
                        let term = Apply qinit UnitValue
                        let (typ, index) = (WireType Qubit, Number 1)
                        let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
                        -- ∅;∅;∅ ⊢ Apply (Init,*) <= Qubit ; 2
                        let term = Apply qinit UnitValue
                        let (typ, index) = (WireType Qubit, Number 2)
                        let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
                it "fails when there are unused linear resources" $ do
                        -- ∅;∅;l:Qubit,k:Qubit ⊢ Apply (Hadamard,l) <=/= Qubit ; 1
                        let term = Apply hadamard $ Label "l"
                        let (theta,gamma,q) = (Set.empty, Map.empty, Map.fromList [("l",Qubit),("k",Qubit)])
                        let (typ, index) = (WireType Qubit, Number 1)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
                it "fails when the circuit produced by the term has width greater than the index" $ do
                        -- ∅;∅;∅ ⊢ Apply (Init,*) <=/= Qubit ; 0
                        let term = Apply qinit UnitValue
                        let (typ, index) = (WireType Qubit, Number 0)
                        let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft

main :: IO ()
main = hspec $ do
        bundleSynthesisSpec
        bundleCheckingSpec
        primitiveGatesSpec
        returnSpec
        destSpec
        assortedSpec
