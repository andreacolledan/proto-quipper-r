module Main (main) where
import Wire.Syntax
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State (StateT(runStateT))
import Language.Checking (checkValueType, checkTermType, TypingContext)
import Language.Syntax
import Circuit.Syntax
import Index
import qualified Data.Set as Set
import Wire.Checking (LabelContext)

-- ∅;∅;l:Qubit ⊢ Apply (H,l) : Qubit ; 1 (SUCCEEDS)
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
        let (success,error) = case runStateT (checkTermType term typ index) (theta, gamma, q) of
                Left err -> (False,err)
                Right (lin,(_,remgamma,remq)) -> if lin
                        then (True,"")
                        else (False,"Unused resources in linear environments")
        putStrLn
                $ show term ++ "\n"
                ++ (if success then "typechecks" else "does not typecheck")
                ++ " against " ++ show typ ++ " ; " ++ show index ++ "\n"
                ++ "under contexts " ++ show (theta :: Set IndexVariableId)
                ++ " ; " ++ show (gamma :: Map VariableId Type)
                ++ " ; " ++ show (q :: Map LabelId WireType) ++ "\n"
                ++ if success then "" else "due to: " ++ error

-- ∅;∅;l:Qubit,k:Qubit ⊢ Apply (H,l) : Qubit ; 1 (FAILS due to linearity)
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
        let (success,error) = case runStateT (checkTermType term typ index) (theta, gamma, q) of
                Left err -> (False,err)
                Right (lin,(_,remgamma,remq)) -> if lin
                        then (True,"")
                        else (False,"Unused resources in linear environments")
        putStrLn
                $ show term ++ "\n"
                ++ (if success then "typechecks" else "does not typecheck")
                ++ " against " ++ show typ ++ " ; " ++ show index ++ "\n"
                ++ "under contexts " ++ show (theta :: Set IndexVariableId)
                ++ " ; " ++ show (gamma :: Map VariableId Type)
                ++ " ; " ++ show (q :: Map LabelId WireType) ++ "\n"
                ++ if success then "" else "due to: " ++ error

main :: IO ()
main = do
        test1
        test2
        