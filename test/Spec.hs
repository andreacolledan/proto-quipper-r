module Main (main) where
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map
import Circuit.Syntax
import Index
import qualified Data.Set as Set
import PrettyPrinter 
import WireBundle.Checking (LabelContext)
import Language.Checking (TypingContext, checkTermType)
import Control.Monad.State.Lazy
import Language.Syntax (VariableId, Value(..), Term(..), Type(..))
import WireBundle.Syntax (LabelId, WireType(..))
import qualified WireBundle.Syntax as Bundle
import Test.Hspec

hadamard :: Value
hadamard = BoxedCircuit (Bundle.Label "a") (Op Hadamard (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
pauliX :: Value
pauliX = BoxedCircuit (Bundle.Label "a") (Op PauliX (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
qinit :: Value
qinit = BoxedCircuit Bundle.UnitValue (Op Init Bundle.UnitValue (Bundle.Label "b")) (Bundle.Label "b")
qdiscard :: Value
qdiscard = BoxedCircuit (Bundle.Label "a") (Op Discard (Bundle.Label "a") Bundle.UnitValue) Bundle.UnitValue
 
termCheckingTest :: Term -> IndexContext -> LabelContext -> TypingContext -> Type -> Index -> (Bool, String)
termCheckingTest term theta q gamma typ index = case evalStateT (checkTermType term typ index) (theta, gamma, q) of
        Left err -> (False,err)
        Right linearResourcesRemaining -> if linearResourcesRemaining
                then (False,"Unused resources in linear environments")
                else (True,"This message is ignored")
        

printTestResults :: Term -> IndexContext -> LabelContext -> TypingContext -> Type -> Index -> Bool -> String -> IO()
printTestResults term theta q gamma typ index outcome msg = do
        putStrLn $
                pretty term ++ "\n"
                ++ (if outcome then "typechecks" else "does not typecheck")
                ++ " against " ++ pretty typ ++ " ; " ++ pretty index ++ "\n"
                ++ "under contexts " ++ pretty (theta :: Set IndexVariableId)
                ++ " ; " ++ pretty (gamma :: Map VariableId Type)
                ++ " ; " ++ pretty (q :: Map LabelId Bundle.WireType) ++ "\n"
                ++ if outcome then "" else "due to: " ++ msg
                ++ "\n"

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

main :: IO ()
main = hspec $ do
        describe "term checking" $ do
                it "succeeds when the term is well-typed" $ do
                        fst test1 `shouldBe` True
                        fst test3 `shouldBe` True
                        fst test4 `shouldBe` True
                it "fails when there are unused linear resources" $ do
                        fst test2 `shouldBe` False
                it "fails when the circuit produced by the term has width greater than the index" $ do
                        fst test5 `shouldBe` False
