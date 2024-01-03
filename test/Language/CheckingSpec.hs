module Language.CheckingSpec(spec) where
import Data.Set (Set)
import Data.Map (Map)
import Circuit.Syntax
import Index
import PrettyPrinter
import WireBundle.Checking (LabelContext)
import Language.Checking (TypingContext,TypingEnvironment(..), checkTermType, checkValueType, envIsLinear)
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
termCheckingTest term theta q gamma typ index = let env = TypingEnvironment theta gamma q in
    case execStateT (checkTermType term typ index) env of
        Left err -> throwError err
        Right env' -> when (envIsLinear env') $ throwError "Unused resources in linear environments"

valueCheckingTest :: Value -> IndexContext -> LabelContext -> TypingContext -> Type -> Either String ()
valueCheckingTest value theta q gamma typ = let env = TypingEnvironment theta gamma q in
    case execStateT (checkValueType value typ) env of
        Left err -> throwError err
        Right env' -> when (envIsLinear env') $ throwError "Unused resources in linear environments"


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
hadamard = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a",Qubit)])) Hadamard (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
pauliX :: Value
pauliX = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a",Qubit)])) PauliX (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
qinit :: Value
qinit = BoxedCircuit Bundle.UnitValue (Seq (Id Map.empty) Init Bundle.UnitValue (Bundle.Label "a")) (Bundle.Label "a")
qdiscard :: Value
qdiscard = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a",Qubit)])) Discard (Bundle.Label "a") Bundle.UnitValue) Bundle.UnitValue
cnot :: Value
cnot = BoxedCircuit (Bundle.Pair (Bundle.Label "a1") (Bundle.Label "a2"))
    (Seq (Id (Map.fromList [("a1",Qubit),("a2",Qubit)])) CNot (Bundle.Pair (Bundle.Label "a1") (Bundle.Label "a2")) (Bundle.Pair (Bundle.Label "b1") (Bundle.Label "b2")))
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

applySpec :: Spec
applySpec = do
        describe "apply checking" $ do
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

functionSpec :: Spec
functionSpec = do
    describe "function typechecking" $ do
        it "succeeds when the rule's premises hold" $ do
            -- ∅;∅;∅ ⊢ λx:Qubit. return x <= Qubit -o [1,0] Qubit
            let term = Abs "x" (WireType Qubit) (Return $ Variable "x")
            let typ = Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
            -- ∅;∅;l:Qubit ⊢ λx:UnitType. return l <= Qubit-o [1,1] Qubit
            let term = Abs "x" UnitType (Return $ Label "l")
            let typ = Arrow UnitType (WireType Qubit) (Number 1) (Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
            -- ∅;∅;l:Qubit ⊢ λc:Circ[3](Qubit,Qubit). apply(c,l) <= Circ[3](Qubit,Qubit) -o [3,1] Qubit
            let term = Abs "c" (Circ (Number 3) (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Apply (Variable "c") (Label "l"))
            let typ = Arrow (Circ (Number 3) (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (WireType Qubit) (Number 3) (Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
            -- ∅;x:Qubit;∅ ⊢ λy:Qubit. apply(CNOT,(x,y)) <= Qubit -o [2,1] (Qubit,Qubit)
            let term = Abs "y" (WireType Qubit) (Apply cnot (Pair (Variable "x") (Variable "y")))
            let typ = Arrow (WireType Qubit) (Tensor (WireType Qubit) (WireType Qubit)) (Number 2) (Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit)],Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
        it "fails when the function does not use its linear argument" $ do
            -- ∅;∅;∅ ⊢ λx:Qubit. return * <= Qubit -o [1,0] Unit
            let term = Abs "x" (WireType Qubit) (Return UnitValue)
            let typ = Arrow (WireType Qubit) UnitType (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the function uses its linear argument more than once" $ do
            -- ∅;∅;∅ ⊢ λx:Qubit. return (x,x) <= Qubit -o [1,0] (Qubit,Qubit)
            let term = Abs "x" (WireType Qubit) (Return $ Pair (Variable "x") (Variable "x"))
            let typ = Arrow (WireType Qubit) (Tensor (WireType Qubit) (WireType Qubit)) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the function builds too large a circuit" $ do
            -- ∅;∅;∅ ⊢ λx:Qubit⊗Qubit. apply(CNOT,x) <= (Qubit⊗Qubit) -o [1,0] (Qubit⊗Qubit)
            let term = Abs "x" (Tensor (WireType Qubit) (WireType Qubit)) (Apply cnot (Variable "x"))
            let typ = Arrow (Tensor (WireType Qubit) (WireType Qubit)) (Tensor (WireType Qubit) (WireType Qubit)) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the type does not correctly reflect the amount of captured wires" $ do
            -- ∅;∅;l:Qubit ⊢ λx:UnitType. return l <= Qubit-o [1,0] Qubit
            let term = Abs "x" UnitType (Return $ Label "l")
            let typ = Arrow UnitType (WireType Qubit) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
            
applicationSpec :: Spec
applicationSpec = do
    describe "application type checking" $ do
        it "succeeds when the rule's premises hold" $ do
            -- ∅;∅;l:Qubit ⊢ (λx:Qubit.return x)l <= Qubit ; 1
            let term = App (Abs "x" (WireType Qubit) (Return $ Variable "x")) (Label "l")
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight

forceSpec :: Spec
forceSpec = undefined

liftSpec :: Spec
liftSpec = undefined

spec :: Spec
spec = do
    primitiveGatesSpec
    applySpec
    returnSpec
    destSpec
    functionSpec
    applicationSpec