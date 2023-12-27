module TestUtils where
import Data.Set (Set)
import Data.Map (Map)
import Circuit.Syntax
import Index
import PrettyPrinter
import WireBundle.Checking (LabelContext)
import Language.Checking (TypingContext, checkTermType, checkValueType)
import Control.Monad.State.Lazy
import Language.Syntax (VariableId, Value(..), Term(..), Type(..))
import WireBundle.Syntax (LabelId, WireType (Qubit))
import qualified WireBundle.Syntax as Bundle
import Test.Hspec
import qualified Data.Set as Set
import qualified Data.Map as Map

hadamard :: Value
hadamard = BoxedCircuit (Bundle.Label "a") (Op Hadamard (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
pauliX :: Value
pauliX = BoxedCircuit (Bundle.Label "a") (Op PauliX (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
qinit :: Value
qinit = BoxedCircuit Bundle.UnitValue (Op Init Bundle.UnitValue (Bundle.Label "b")) (Bundle.Label "b")
qdiscard :: Value
qdiscard = BoxedCircuit (Bundle.Label "a") (Op Discard (Bundle.Label "a") Bundle.UnitValue) Bundle.UnitValue
cnot :: Value
cnot = BoxedCircuit (Bundle.Pair (Bundle.Label "a1") (Bundle.Label "a2"))
    (Op CNot (Bundle.Pair (Bundle.Label "a1") (Bundle.Label "a2")) (Bundle.Pair (Bundle.Label "b1") (Bundle.Label "b2")))
    (Bundle.Pair (Bundle.Label "b1") (Bundle.Label "b2"))

termCheckingTest :: Term -> IndexContext -> LabelContext -> TypingContext -> Type -> Index -> (Bool, String)
termCheckingTest term theta q gamma typ index = case evalStateT (checkTermType term typ index) (theta, gamma, q) of
        Left err -> (False,err)
        Right linearResourcesRemaining -> if linearResourcesRemaining
                then (False,"Unused resources in linear environments")
                else (True,"This message is ignored")

valueCheckingTest :: Value -> IndexContext -> LabelContext -> TypingContext -> Type -> (Bool, String)
valueCheckingTest value theta q gamma typ = case evalStateT (checkValueType value typ) (theta, gamma, q) of
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

primitiveSpec :: Spec
primitiveSpec = do
    describe "hadamard" $ do
        let desiredType = Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest hadamard Set.empty Map.empty Map.empty desiredType
                `shouldBe` (True, "This message is ignored")
    describe "pauli-x" $ do
        let desiredType = Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest pauliX Set.empty Map.empty Map.empty desiredType
                `shouldBe` (True, "This message is ignored")
    describe "qinit" $ do
        let desiredType = Circ (Number 1) Bundle.UnitType (Bundle.WireType Qubit)
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest qinit Set.empty Map.empty Map.empty desiredType
                `shouldBe` (True, "This message is ignored")
    describe "qdiscard" $ do
        let desiredType = Circ (Number 1) (Bundle.WireType Qubit) Bundle.UnitType
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest qdiscard Set.empty Map.empty Map.empty desiredType
                `shouldBe` (True, "This message is ignored")
    describe "cnot" $ do
        let desiredType = Circ (Number 2) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
                (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest cnot Set.empty Map.empty Map.empty desiredType
                `shouldBe` (True, "This message is ignored")