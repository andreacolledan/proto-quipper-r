module Main (main) where
import Wire.Syntax
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State (StateT(runStateT), evalStateT)
import Language.Checking (checkValueType, checkTermType, TypingContext)
import Language.Syntax
import Circuit.Syntax
import Index
import qualified Data.Set as Set
import Wire.Checking (LabelContext)

-- ∅;∅;l:Qubit ⊢ Apply (Hadamard,l) : Qubit ; 1 (SUCCEEDS)
test1 :: IO()
test1 = do
        let v = BoxedCircuit (Label "a") (Op Hadamard (Label "a") (Label "b")) (Label "b")
        let l = Bundle (Label "l")
        let term = Apply v l
        let q = Map.fromList [("l",Qubit)]
        let theta = Set.empty
        let gamma = Map.empty
        let typ = BundleType (WireType Qubit)
        let index = Number 1
        let (success,msg) = case evalStateT (checkTermType term typ index) (theta, gamma, q) of
                Left err -> (False,err)
                Right lin -> if lin
                        then (True,"")
                        else (False,"Unused resources in linear environments")
        putStrLn
                $ show term ++ "\n"
                ++ (if success then "typechecks" else "does not typecheck")
                ++ " against " ++ show typ ++ " ; " ++ show index ++ "\n"
                ++ "under contexts " ++ show (theta :: Set IndexVariableId)
                ++ " ; " ++ show (gamma :: Map VariableId Type)
                ++ " ; " ++ show (q :: Map LabelId WireType) ++ "\n"
                ++ if success then "" else "due to: " ++ msg
                ++ "\n"

-- ∅;∅;l:Qubit,k:Qubit ⊢ Apply (Hadamard,l) : Qubit ; 1 (FAILS due to linearity)
test2 :: IO()
test2 = do
        let v = BoxedCircuit (Label "a") (Op Hadamard (Label "a") (Label "b")) (Label "b")
        let l = Bundle (Label "l")
        let term = Apply v l
        let q = Map.fromList [("l",Qubit),("k",Qubit)]
        let theta = Set.empty
        let gamma = Map.empty
        let typ = BundleType (WireType Qubit)
        let index = Number 1
        let (success,msg) = case evalStateT (checkTermType term typ index) (theta, gamma, q) of
                Left err -> (False,err)
                Right lin -> if lin
                        then (True,"")
                        else (False,"Unused resources in linear environments")
        putStrLn
                $ show term ++ "\n"
                ++ (if success then "typechecks" else "does not typecheck")
                ++ " against " ++ show typ ++ " ; " ++ show index ++ "\n"
                ++ "under contexts " ++ show (theta :: Set IndexVariableId)
                ++ " ; " ++ show (gamma :: Map VariableId Type)
                ++ " ; " ++ show (q :: Map LabelId WireType) ++ "\n"
                ++ if success then "" else "due to: " ++ msg
                ++ "\n"

-- ∅;∅;∅ ⊢ Apply (Init,*) : Qubit ; 1 (SUCCEEDS)
test3 :: IO()
test3 = do
        let v = BoxedCircuit UnitValue (Op Init UnitValue (Label "b")) (Label "b")
        let term = Apply v (Bundle UnitValue)
        let q = Map.empty
        let theta = Set.empty
        let gamma = Map.empty
        let typ = BundleType (WireType Qubit)
        let index = Number 1
        let (success,msg) = case evalStateT (checkTermType term typ index) (theta, gamma, q) of
                Left err -> (False,err)
                Right lin -> if lin
                        then (True,"")
                        else (False,"Unused resources in linear environments")
        putStrLn
                $ show term ++ "\n"
                ++ (if success then "typechecks" else "does not typecheck")
                ++ " against " ++ show typ ++ " ; " ++ show index ++ "\n"
                ++ "under contexts " ++ show (theta :: Set IndexVariableId)
                ++ " ; " ++ show (gamma :: Map VariableId Type)
                ++ " ; " ++ show (q :: Map LabelId WireType) ++ "\n"
                ++ if success then "" else "due to: " ++ msg
                ++ "\n"

-- ∅;∅;∅ ⊢ Apply (Init,*) : Qubit ; 2 (SUCCEEDS)
test4 :: IO()
test4 = do
        let v = BoxedCircuit UnitValue (Op Init UnitValue (Label "b")) (Label "b")
        let term = Apply v (Bundle UnitValue)
        let q = Map.empty
        let theta = Set.empty
        let gamma = Map.empty
        let typ = BundleType (WireType Qubit)
        let index = Number 2
        let (success,msg) = case evalStateT (checkTermType term typ index) (theta, gamma, q) of
                Left err -> (False,err)
                Right lin -> if lin
                        then (True,"")
                        else (False,"Unused resources in linear environments")
        putStrLn
                $ show term ++ "\n"
                ++ (if success then "typechecks" else "does not typecheck")
                ++ " against " ++ show typ ++ " ; " ++ show index ++ "\n"
                ++ "under contexts " ++ show (theta :: Set IndexVariableId)
                ++ " ; " ++ show (gamma :: Map VariableId Type)
                ++ " ; " ++ show (q :: Map LabelId WireType) ++ "\n"
                ++ if success then "" else "due to: " ++ msg
                ++ "\n"

-- ∅;∅;∅ ⊢ Apply (Init,*) : Qubit ; 0 (FAILS due to the produced circuit having width 1)
test5 :: IO()
test5 = do
        let v = BoxedCircuit UnitValue (Op Init UnitValue (Label "b")) (Label "b")
        let term = Apply v (Bundle UnitValue)
        let q = Map.empty
        let theta = Set.empty
        let gamma = Map.empty
        let typ = BundleType (WireType Qubit)
        let index = Number 0
        let (success,msg) = case evalStateT (checkTermType term typ index) (theta, gamma, q) of
                Left err -> (False,err)
                Right lin -> if lin
                        then (True,"")
                        else (False,"Unused resources in linear environments")
        putStrLn
                $ show term ++ "\n"
                ++ (if success then "typechecks" else "does not typecheck")
                ++ " against " ++ show typ ++ " ; " ++ show index ++ "\n"
                ++ "under contexts " ++ show (theta :: Set IndexVariableId)
                ++ " ; " ++ show (gamma :: Map VariableId Type)
                ++ " ; " ++ show (q :: Map LabelId WireType) ++ "\n"
                ++ if success then "" else "due to: " ++ msg
                ++ "\n"

main :: IO ()
main = do
        test1
        test2
        test3
        test4
        test5
