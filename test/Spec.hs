module Main (main) where
import WireBundle.Syntax
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map
import Language.Syntax
import Circuit.Syntax
import Index
import qualified Data.Set as Set
import PrettyPrinter 
import WireBundle.Checking (LabelContext)
import Language.Checking (TypingContext, checkTermType)
import Control.Monad.State.Lazy

hadamard :: Value
hadamard = BoxedCircuit (Label "a") (Op Hadamard (Label "a") (Label "b")) (Label "b")
pauliX :: Value
pauliX = BoxedCircuit (Label "a") (Op PauliX (Label "a") (Label "b")) (Label "b")
qinit :: Value
qinit = BoxedCircuit UnitValue (Op Init UnitValue (Label "b")) (Label "b")
qdiscard :: Value
qdiscard = BoxedCircuit (Label "a") (Op Discard (Label "a") UnitValue) UnitValue
 
termCheckingTest :: Term -> IndexContext -> LabelContext -> TypingContext -> Type -> Index -> IO()
termCheckingTest term theta q gamma typ index = do
        let (outcome,msg) = case evalStateT (checkTermType term typ index) (theta, gamma, q) of
                Left err -> (False,err)
                Right lin -> if lin
                        then (True,"This message is ignored")
                        else (False,"Unused resources in linear environments")
        putStrLn
                $ pretty term ++ "\n"
                ++ (if outcome then "typechecks" else "does not typecheck")
                ++ " against " ++ pretty typ ++ " ; " ++ pretty index ++ "\n"
                ++ "under contexts " ++ pretty (theta :: Set IndexVariableId)
                ++ " ; " ++ pretty (gamma :: Map VariableId Type)
                ++ " ; " ++ pretty (q :: Map LabelId WireType) ++ "\n"
                ++ if outcome then "" else "due to: " ++ msg
                ++ "\n"

-- ∅;∅;l:Qubit ⊢ Apply (Hadamard,l) : Qubit ; 1 (SUCCEEDS)
test1 :: IO()
test1 = do
        let term = Apply hadamard $ Bundle $ Label "l"
        let (theta,gamma,q) = (Set.empty, Map.empty, Map.fromList [("l",Qubit)])
        let (typ, index) = (BundleType (WireType Qubit), Number 1)
        termCheckingTest term theta q gamma typ index

-- ∅;∅;l:Qubit,k:Qubit ⊢ Apply (Hadamard,l) : Qubit ; 1 (FAILS due to linearity)
test2 :: IO()
test2 = do
        let term = Apply hadamard $ Bundle $ Label "l"
        let (theta,gamma,q) = (Set.empty, Map.empty, Map.fromList [("l",Qubit),("k",Qubit)])
        let (typ, index) = (BundleType (WireType Qubit), Number 1)
        termCheckingTest term theta q gamma typ index

-- ∅;∅;∅ ⊢ Apply (Init,*) : Qubit ; 1 (SUCCEEDS)
test3 :: IO()
test3 = do
        let term = Apply qinit $ Bundle UnitValue
        let (typ, index) = (BundleType (WireType Qubit), Number 1)
        let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
        termCheckingTest term theta q gamma typ index

-- ∅;∅;∅ ⊢ Apply (Init,*) : Qubit ; 2 (SUCCEEDS)
test4 :: IO()
test4 = do
        let term = Apply qinit $ Bundle UnitValue
        let (typ, index) = (BundleType (WireType Qubit), Number 2)
        let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
        termCheckingTest term theta q gamma typ index

-- ∅;∅;∅ ⊢ Apply (Init,*) : Qubit ; 0 (FAILS due to the produced circuit having width 1)
test5 :: IO()
test5 = do
        let term = Apply qinit $ Bundle UnitValue
        let (typ, index) = (BundleType (WireType Qubit), Number 0)
        let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
        termCheckingTest term theta q gamma typ index

main :: IO ()
main = do
        test1
        test2
        test3
        test4
        test5
