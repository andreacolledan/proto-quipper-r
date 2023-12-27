module Main (main) where
import qualified Data.Map as Map
import Index
import qualified Data.Set as Set
import Language.Syntax (Value(..), Term(..), Type(..))
import WireBundle.Syntax (WireType(..))
import Test.Hspec
import TestUtils

-- ∅;∅;l:Qubit ⊢ Apply (Hadamard,l) : Qubit ; 1 (SUCCEEDS)
test1 :: (Bool, String)
test1 = let
        term = Apply hadamard $ Label "l"
        (theta,gamma,q) = (Set.empty, Map.empty, Map.fromList [("l",Qubit)])
        (typ, index) = (WireType Qubit, Number 1)
        in termCheckingTest term theta q gamma typ index

-- ∅;∅;l:Qubit,k:Qubit ⊢ Apply (Hadamard,l) : Qubit ; 1 (FAILS due to linearity)
test2 :: (Bool, String)
test2 = let
        term = Apply hadamard $ Label "l"
        (theta,gamma,q) = (Set.empty, Map.empty, Map.fromList [("l",Qubit),("k",Qubit)])
        (typ, index) = (WireType Qubit, Number 1)
        in termCheckingTest term theta q gamma typ index

-- ∅;∅;∅ ⊢ Apply (Init,*) : Qubit ; 1 (SUCCEEDS)
test3 :: (Bool, String)
test3 = let
        term = Apply qinit UnitValue
        (typ, index) = (WireType Qubit, Number 1)
        (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
        in termCheckingTest term theta q gamma typ index

-- ∅;∅;∅ ⊢ Apply (Init,*) : Qubit ; 2 (SUCCEEDS)
test4 :: (Bool, String)
test4 = let
        term = Apply qinit UnitValue
        (typ, index) = (WireType Qubit, Number 2)
        (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
        in termCheckingTest term theta q gamma typ index

-- ∅;∅;∅ ⊢ Apply (Init,*) : Qubit ; 0 (FAILS due to the produced circuit having width 1)
test5 :: (Bool, String)
test5 = let
        term = Apply qinit UnitValue
        (typ, index) = (WireType Qubit, Number 0)
        (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
        in termCheckingTest term theta q gamma typ index

-- ∅;x:A;∅ ⊢ Apply (Discard,l) : Unit ; 1 (SUCCEEDS)

mainSpec :: Spec
mainSpec = do describe "term checking" $ do
                it "succeeds when the term is well-typed" $ do
                        fst test1 `shouldBe` True
                        fst test3 `shouldBe` True
                        fst test4 `shouldBe` True
                it "fails when there are unused linear resources" $ do
                        fst test2 `shouldBe` False
                it "fails when the circuit produced by the term has width greater than the index" $ do
                        fst test5 `shouldBe` False

main :: IO ()
main = hspec $ do
        primitiveSpec
        mainSpec
