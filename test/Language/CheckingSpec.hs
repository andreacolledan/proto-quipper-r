module Language.CheckingSpec where
import Data.Set (Set)
import Data.Map (Map)
import Circuit.Syntax
import Index
import PrettyPrinter
import WireBundle.Checking (LabelContext)
import Language.Checking (TypingContext, checkTermType, checkValueType)
import Control.Monad.State.Lazy
import Language.Syntax (VariableId, Value(..), Term(..), Type(..))
import WireBundle.Syntax (LabelId, WireType (Qubit, Bit))
import qualified WireBundle.Syntax as Bundle
import Test.Hspec
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.Error.Class
import Control.Monad
import Data.Either (isRight, isLeft)

-- HELPER FUNCTIONS --

termCheckingTest :: Term -> IndexContext -> LabelContext -> TypingContext -> Type -> Index -> Either String ()
termCheckingTest term theta q gamma typ index = case evalStateT (checkTermType term typ index) (theta, gamma, q) of
        Left err -> throwError err
        Right linearResourcesRemaining -> when linearResourcesRemaining $ throwError "Unused resources in linear environments"

valueCheckingTest :: Value -> IndexContext -> LabelContext -> TypingContext -> Type -> Either String ()
valueCheckingTest value theta q gamma typ = case evalStateT (checkValueType value typ) (theta, gamma, q) of
        Left err -> throwError err
        Right linearResourcesRemaining -> when linearResourcesRemaining $ throwError "Unused resources in linear environments"


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


-- PRIMITIVE GATES --

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


-- SPECIFICATION --

primitiveGatesSpec :: Spec
primitiveGatesSpec = do
    describe "hadamard" $ do
        let desiredType = Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest hadamard Set.empty Map.empty Map.empty desiredType
                `shouldSatisfy` isRight
    describe "pauli-x" $ do
        let desiredType = Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest pauliX Set.empty Map.empty Map.empty desiredType
                `shouldSatisfy` isRight
    describe "qinit" $ do
        let desiredType = Circ (Number 1) Bundle.UnitType (Bundle.WireType Qubit)
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest qinit Set.empty Map.empty Map.empty desiredType
                `shouldSatisfy` isRight
    describe "qdiscard" $ do
        let desiredType = Circ (Number 1) (Bundle.WireType Qubit) Bundle.UnitType
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest qdiscard Set.empty Map.empty Map.empty desiredType
                `shouldSatisfy` isRight
    describe "cnot" $ do
        let desiredType = Circ (Number 2) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
                (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
        it ("should have type " ++ pretty desiredType) $ do
            valueCheckingTest cnot Set.empty Map.empty Map.empty desiredType
                `shouldSatisfy` isRight

returnSpec :: Spec
returnSpec = do
    describe "return typechecking" $ do
        it "should succeed when the rule's premises hold" $ do
            -- ∅;∅;∅ ⊢ return * <= Unit ; 0
            let term = Return UnitValue
            let (typ, index) = (UnitType, Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
            -- ∅;x:Qubit;∅ ⊢ return x <= Qubit ; 1
            let term = Return $ Variable "x"
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
            -- ∅;x:Qubit,y:Bit;∅ ⊢ return (x,y) <= Qubit ⊗ Bit ; 2
            let term = Return $ Pair (Variable "x") (Variable "y")
            let (typ, index) = (Tensor (WireType Qubit) (WireType Bit), Number 2)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit),("y",WireType Bit)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "should fail when the type does not match" $ do
            -- ∅;x:Qubit;∅ ⊢ return x <= Bit ; 1
            let term = Return $ Variable "x"
            let (typ, index) = (WireType Bit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "should fail when the index does not match the context's wire count" $ do
            -- ∅;x:Qubit,y:Bit;∅ ⊢ return (x,y) <= Qubit ⊗ Bit ; 1
            let term = Return $ Pair (Variable "x") (Variable "y")
            let (typ, index) = (Tensor (WireType Qubit) (WireType Bit), Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit),("y",WireType Bit)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft


destSpec :: Spec
destSpec = do
    describe "destructuring let typechecking" $ do
        it "should succeed when the rule's premises hold" $ do
            -- ∅;∅;∅ ⊢ let (c,u) = (Init,*) in apply(c,u) <= Qubit ; 1
            let term = Dest "c" "u" (Pair qinit UnitValue) (Apply (Variable "c") (Variable "u"))
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "should fail when binding shadows existing variable" $ do
            -- ∅;c:Unit;∅ ⊢ let (c,u) = (Init,*) in apply(c,u) <= Qubit ; 1
            let term = Dest "c" "u" (Pair qinit UnitValue) (Apply (Variable "c") (Variable "u"))
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("c",UnitType)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "should fail when the two variables shadow each other" $ do
            -- ∅;∅;∅ ⊢ let (c,c) = (Init,*) in apply(c,c) <= Qubit ; 1
            let term = Dest "c" "c" (Pair qinit UnitValue) (Apply (Variable "c") (Variable "c"))
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft