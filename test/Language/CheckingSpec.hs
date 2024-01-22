module Language.CheckingSpec(spec) where
import Data.Set (Set)
import Data.Map (Map)
import Circuit.Syntax
import Index
import PrettyPrinter
import WireBundle.Checking (LabelContext)
import Language.Checking (TypingContext,TypingEnvironment(..), checkTermType, checkValueType, envIsLinear, TypingError(..))
import Control.Monad.State.Lazy
import Language.Syntax (VariableId, Value(..), Term(..), Type(..))
import WireBundle.Syntax (LabelId, WireType (Qubit, Bit))
import qualified WireBundle.Syntax as Bundle
import Test.Hspec
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Monad.Error.Class ( MonadError(throwError) )
import Control.Monad
import Data.Either (isRight, isLeft)

-- HELPER FUNCTIONS --

termCheckingTest :: Term -> IndexContext -> LabelContext -> TypingContext -> Type -> Index -> Either TypingError ()
termCheckingTest term theta q gamma typ index = let env = TypingEnvironment theta gamma q in
    case execStateT (checkTermType term typ index) env of
        Left err -> throwError err
        Right env'@TypingEnvironment{typingContext=gamma, labelContext=q} ->
            when (envIsLinear env') $ throwError $ UnusedLinearResources gamma q

valueCheckingTest :: Value -> IndexContext -> LabelContext -> TypingContext -> Type -> Either TypingError ()
valueCheckingTest value theta q gamma typ = let env = TypingEnvironment theta gamma q in
    case execStateT (checkValueType value typ) env of
        Left err -> throwError err
        Right env'@TypingEnvironment{typingContext=gamma, labelContext=q} ->
            when (envIsLinear env') $ throwError $ UnusedLinearResources gamma q

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

boxedCircuitSpec :: Spec
boxedCircuitSpec = do
    describe "boxed circuit type checking" $ do
        it "fails when the input or output interfaces do not match tha circuit's actual output" $ do
            -- ∅;∅;∅ ⊢ (a,Hadamard,*) <=/= Circ 1 Qubit Unit
            let term = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a",Qubit)])) Hadamard (Bundle.Label "a") (Bundle.Label "b")) Bundle.UnitValue
            let typ = Circ (Number 1) (Bundle.WireType Qubit) Bundle.UnitType
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
            -- ∅;∅;∅ ⊢ (*,Hadamard,b) <=/= Circ 1 Unit Qubit
            let term = BoxedCircuit Bundle.UnitValue (Seq (Id (Map.fromList [("a",Qubit)])) Hadamard (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
            let typ = Circ (Number 1) Bundle.UnitType (Bundle.WireType Qubit)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
            -- ∅;∅;∅ ⊢ (a,Init,b) <=/= Circ 1 Qubit Qubit
            let term = BoxedCircuit (Bundle.Label "a") (Seq (Id Map.empty) Init Bundle.UnitValue (Bundle.Label "b")) (Bundle.Label "b")
            let typ = Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the circuit is wider than the type annotation" $ do
            -- ∅;∅;∅ ⊢ cnot <=/= Circ 1 (Qubit,Qubit) (Qubit,Qubit)
            let typ = Circ (Number 1) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest cnot theta q gamma typ `shouldSatisfy` isLeft
        
varSpec :: Spec
varSpec = do
    describe "variable type checking" $ do
        it "fails when the variable is unbound" $ do
            -- ∅;∅;∅ ⊢ x <=/= Qubit
            let term = Variable "x"
            let typ = WireType Qubit
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the context type and the checked type for the variable do not match" $ do
            -- ∅;x:Qubit;∅ ⊢ x <=/= Bit
            let term = Variable "x"
            let typ = WireType Bit
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit)],Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft

applySpec :: Spec
applySpec = do
        describe "apply checking" $ do
                it "succeeds when the term is well-typed" $ do
                        -- ∅;∅;l:Qubit ⊢ Apply (Hadamard,l) <== Qubit ; 1
                        let term = Apply hadamard $ Label "l"
                        let (theta,gamma,q) = (Set.empty, Map.empty, Map.fromList [("l",Qubit)])
                        let (typ, index) = (WireType Qubit, Number 1)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
                        -- ∅;∅;∅ ⊢ Apply (Init,*) <== Qubit ; 1
                        let term = Apply qinit UnitValue
                        let (typ, index) = (WireType Qubit, Number 1)
                        let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
                        -- ∅;∅;∅ ⊢ Apply (Init,*) <== Qubit ; 2
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
                it "fails when the first argument is not of circuit type" $ do
                        -- ∅;∅;∅ ⊢ Apply (*,*) <=/= Unit ; 1
                        let term = Apply UnitValue UnitValue
                        let (typ, index) = (UnitType, Number 1)
                        let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
                it "fails when the second argument is not of bundle type" $ do
                        -- ∅;x:!Unit;∅ ⊢ Apply (Init,x) <=/= Qubit ; 1
                        let term = Apply qinit $ Variable "x"
                        let (typ, index) = (WireType Qubit, Number 1)
                        let (theta,gamma,q) = (Set.empty,Map.fromList [("x",Bang UnitType)],Map.empty)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
                it "fails when the second argument does not have type matching the circuit's input" $ do
                        -- ∅;∅;l:But ⊢ Apply (Hadamard,l) <=/= Qubit ; 1
                        let term = Apply hadamard $ Label "l"
                        let (typ, index) = (WireType Qubit, Number 1)
                        let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Bit)])
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
                it "fails when the circuits output does not match the checked type" $ do
                        -- ∅;∅;∅ ⊢ Apply (Init,*) <=/= Bit ; 1
                        let term = Apply qinit UnitValue
                        let (typ, index) = (WireType Bit, Number 1)
                        let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
                        termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft


returnSpec :: Spec
returnSpec = do
    describe "return typechecking" $ do
        it "succeeds when the context is empty and the return value is nonlinear" $ do
            -- ∅;∅;∅ ⊢ return * <== Unit ; 0
            let term = Return UnitValue
            let (typ, index) = (UnitType, Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "succeeds when the context is a parameter context and the return value is nonlinear" $ do
            -- ∅;x:Unit,y:!(Qubit -o [1,0] Qubit),z:Circ 1 (Qubit,Qubit);∅ ⊢ return z <== Circ 1 (Qubit,Qubit) ; 0
            let term = Return $ Variable "z"
            let (typ, index) = (Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit), Number 0)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",UnitType),("y",Bang $ Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0)),("z",Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit))],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "succeeds when the the return value does not contain more wires than the resource annotation" $ do
            -- ∅;x:Qubit;∅ ⊢ return x <== Qubit ; 1
            let term = Return $ Variable "x"
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
            -- ∅;x:Qubit,y:Bit;∅ ⊢ return (x,y) <== Qubit ⊗ Bit ; 2
            let term = Return $ Pair (Variable "x") (Variable "y")
            let (typ, index) = (Tensor (WireType Qubit) (WireType Bit), Number 2)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit),("y",WireType Bit)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
            -- ∅;x:Qubit⊗Qubit;∅ ⊢ return x <== Qubit⊗Qubit ; 2
            let term = Return $ Variable "x"
            let (typ, index) = (Tensor (WireType Qubit) (WireType Qubit), Number 2)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",Tensor (WireType Qubit) (WireType Qubit))],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "fails when the type does not match" $ do
            -- ∅;x:Qubit;∅ ⊢ return x <== Bit ; 1
            let term = Return $ Variable "x"
            let (typ, index) = (WireType Bit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the index does not match the context's wire count" $ do
            -- ∅;x:Qubit,y:Bit;∅ ⊢ return (x,y) <== Qubit ⊗ Bit ; 1
            let term = Return $ Pair (Variable "x") (Variable "y")
            let (typ, index) = (Tensor (WireType Qubit) (WireType Bit), Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit),("y",WireType Bit)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft


destSpec :: Spec
destSpec = do
    describe "destructuring let typechecking" $ do
        it "succeeds when the rule's premises hold" $ do
            -- ∅;∅;∅ ⊢ let (c,u) = (Init,*) in apply(c,u) <== Qubit ; 1
            let term = Dest "c" "u" (Pair qinit UnitValue) (Apply (Variable "c") (Variable "u"))
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "fails when binding shadows existing variable" $ do
            -- ∅;c:Unit;∅ ⊢ let (c,u) = (Init,*) in apply(c,u) <== Qubit ; 1
            let term = Dest "c" "u" (Pair qinit UnitValue) (Apply (Variable "c") (Variable "u"))
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("c",UnitType)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the two variables shadow each other" $ do
            -- ∅;∅;∅ ⊢ let (c,c) = (Init,*) in apply(c,c) <== Qubit ; 1
            let term = Dest "c" "c" (Pair qinit UnitValue) (Apply (Variable "c") (Variable "c"))
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the destructurand is not of tensor type" $ do
            -- ∅;∅;∅ ⊢ let (c,u) = * in return * <== Unit ; 0
            let term = Dest "c" "u" UnitValue $ Return UnitValue
            let (typ, index) = (UnitType, Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft

functionSpec :: Spec
functionSpec = do
    describe "function typechecking" $ do
        it "succeeds when the rule's premises hold" $ do
            -- ∅;∅;∅ ⊢ λx:Qubit. return x <== Qubit -o [1,0] Qubit
            let term = Abs "x" (WireType Qubit) (Return $ Variable "x")
            let typ = Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
            -- ∅;∅;l:Qubit ⊢ λx:UnitType. return l <== Qubit-o [1,1] Qubit
            let term = Abs "x" UnitType (Return $ Label "l")
            let typ = Arrow UnitType (WireType Qubit) (Number 1) (Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
            -- ∅;∅;l:Qubit ⊢ λc:Circ[3](Qubit,Qubit). apply(c,l) <== Circ[3](Qubit,Qubit) -o [3,1] Qubit
            let term = Abs "c" (Circ (Number 3) (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Apply (Variable "c") (Label "l"))
            let typ = Arrow (Circ (Number 3) (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (WireType Qubit) (Number 3) (Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
            -- ∅;x:Qubit;∅ ⊢ λy:Qubit. apply(CNOT,(x,y)) <== Qubit -o [2,1] (Qubit,Qubit)
            let term = Abs "y" (WireType Qubit) (Apply cnot (Pair (Variable "x") (Variable "y")))
            let typ = Arrow (WireType Qubit) (Tensor (WireType Qubit) (WireType Qubit)) (Number 2) (Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",WireType Qubit)],Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
        it "fails when the function does not use its linear argument" $ do
            -- ∅;∅;∅ ⊢ λx:Qubit. return * <== Qubit -o [1,0] Unit
            let term = Abs "x" (WireType Qubit) (Return UnitValue)
            let typ = Arrow (WireType Qubit) UnitType (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the function uses its linear argument more than once" $ do
            -- ∅;∅;∅ ⊢ λx:Qubit. return (x,x) <== Qubit -o [1,0] (Qubit,Qubit)
            let term = Abs "x" (WireType Qubit) (Return $ Pair (Variable "x") (Variable "x"))
            let typ = Arrow (WireType Qubit) (Tensor (WireType Qubit) (WireType Qubit)) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the function builds too large a circuit" $ do
            -- ∅;∅;∅ ⊢ λx:Qubit⊗Qubit. apply(CNOT,x) <== (Qubit⊗Qubit) -o [1,0] (Qubit⊗Qubit)
            let term = Abs "x" (Tensor (WireType Qubit) (WireType Qubit)) (Apply cnot (Variable "x"))
            let typ = Arrow (Tensor (WireType Qubit) (WireType Qubit)) (Tensor (WireType Qubit) (WireType Qubit)) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the type does not correctly reflect the amount of captured wires" $ do
            -- ∅;∅;l:Qubit ⊢ λx:UnitType. return l <== Qubit-o [1,0] Qubit
            let term = Abs "x" UnitType (Return $ Label "l")
            let typ = Arrow UnitType (WireType Qubit) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the function is required to have an input type that's different from its annotation" $ do
            -- ∅;∅;∅ ⊢ λx:Qubit. return x <=/= Bit -o [1,0] Qubit
            let term = Abs "x" (WireType Qubit) (Return $ Variable "x")
            let typ = Arrow (WireType Bit) (WireType Qubit) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft

applicationSpec :: Spec
applicationSpec = do
    describe "application type checking" $ do
        it "succeeds when the rule's premises hold" $ do
            -- ∅;∅;l:Qubit ⊢ (λx:Qubit.return x)l <== Qubit ; 1
            let term = App (Abs "x" (WireType Qubit) (Return $ Variable "x")) (Label "l")
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
            -- ∅;∅;l:Qubit,k:Bit ⊢ (λp:Qubit⊗Bit.let (x,y) = p in return (y,x)) (l,k) <== Bit⊗Qubit ; 2
            let term = App
                    (Abs "p" (Tensor (WireType Qubit) (WireType Bit))
                        (Dest "x" "y" (Variable "p") (Return $ Pair (Variable "y") (Variable "x"))))
                    (Pair (Label "l") (Label "k"))
            let (typ, index) = (Tensor (WireType Bit) (WireType Qubit), Number 2)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit),("k",Bit)])
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "fails when the argument type does not match the function's input type" $ do
            -- ∅;∅;l:Bit ⊢ (λx:Qubit.return x)l <=/= Bit ; 1
            let term = App (Abs "x" (WireType Qubit) (Return $ Variable "x")) (Label "l")
            let (typ, index) = (WireType Bit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Bit)])
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the output type does not match the type checked against" $ do
            -- ∅;∅;l:Qubit ⊢ (λx:Qubit.return x)l <=/= Bit ; 1
            let term = App (Abs "x" (WireType Qubit) (Return $ Variable "x")) (Label "l")
            let (typ, index) = (WireType Bit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the function produces too large of a circuit" $ do
            -- ∅;∅;l:Qubit,k:Qubit ⊢ (λx:Qubit. apply(CNOT,(x,l)))k <=/= (Qubit⊗Qubit) ; 1
            let term = App (Abs "x" (WireType Qubit) (Apply cnot (Pair (Variable "x") (Label "l")))) (Label "k")
            let (typ, index) = (Tensor (WireType Qubit) (WireType Qubit), Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit),("k",Qubit)])
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the applicand is not a function" $ do
            -- ∅;∅;∅ ⊢ lift(return *) * <=/= !Unit ; 0
            let term = App (Lift $ Return UnitValue) UnitValue
            let (typ,index) = (Bang UnitType, Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
            -- ∅;f:Qubit,q:Qubit;∅ ⊢ f q <=/= Qubit ; 2
            let term = App (Variable "f") (Variable "q")
            let (typ,index) = (WireType Qubit, Number 2)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("f",WireType Qubit),("q",WireType Qubit)],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft

forceSpec :: Spec
forceSpec = do
    describe "force type checking" $ do
        it "succeeds against type A when the argument is a value of type !A" $ do
            -- ∅;∅;∅ ⊢ force(lift(return *)) <== Unit ; 0
            let term = Force $ Lift $ Return UnitValue
            let (typ,index) = (UnitType,Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
            -- ∅;∅;∅ ⊢ force(lift(return λx:Qubit.return x)) <== Qubit -o [1,0] Qubit ; 0
            let term = Force $ Lift $ Return $ Abs "x" (WireType Qubit) (Return $ Variable "x")
            let (typ,index) = (Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0),Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "fails when the argument is not of bang type" $ do
            -- ∅;∅;∅ ⊢ force(*) <=/= Unit ; 0
            let term = Force UnitValue
            let (typ,index) = (UnitType,Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
            -- ∅;∅;∅ ⊢ force(λx:Qubit.return x) <=/= Qubit -o [1,0] Qubit ; 0
            let term = Force $ Abs "x" (WireType Qubit) (Return $ Variable "x")
            let (typ,index) = (Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0),Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft


liftSpec :: Spec
liftSpec = do
    describe "lift type checking" $ do
        it "succeeds when the rule premises hold" $ do
            -- ∅;∅;∅ ⊢ lift(return(*)) <== !Unit
            let term = Lift $ Return UnitValue
            let typ = Bang UnitType
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
            -- ∅;∅;∅ ⊢ lift(return λx:Qubit.return x) <== !(Qubit -o [1,0] Qubit)
            let term = Lift $ Return $ Abs "x" (WireType Qubit) (Return $ Variable "x")
            let typ = Bang $ Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isRight
        it "fails when the term consumes linear resources" $ do
            -- ∅;f:Unit -o [0,0] Unit;∅ ⊢ lift(return f) <=/= !(Unit -o [0,0] Unit)
            let term = Lift $ Return $ Variable "f"
            let typ = Bang $ Arrow UnitType UnitType (Number 0) (Number 0)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("f",Arrow UnitType UnitType (Number 0) (Number 0))],Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft
        it "fails when the term produces a circuit" $ do
            -- ∅;∅;∅ ⊢ lift(apply(Init,*)) <=/= !Qubit
            let term = Lift $ Apply qinit UnitValue
            let typ = Bang $ WireType Qubit
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            valueCheckingTest term theta q gamma typ `shouldSatisfy` isLeft

letSpec :: Spec
letSpec = do
    describe "let type checking" $ do
        it "succeeds in case of simple sequencing" $ do
            -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in
            --          let q' = apply(H, q) in
            --          return q' <== Qubit ; 1
            let term = Let "q" (Apply qinit UnitValue) (Let "q'" (Apply hadamard (Variable "q")) (Return (Variable "q'")))
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "succeeds in the case of increasing width sequencing" $ do
            -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in
            --          let q' = apply(INIT, *) in
            --          return (q,q') <== Qubit ⊗ Qubit ; 2 
            let term = Let "q" (Apply qinit UnitValue) (Let "q'" (Apply qinit UnitValue) (Return (Pair (Variable "q") (Variable "q'"))))
            let (typ, index) = (Tensor (WireType Qubit) (WireType Qubit), Number 2)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "succeeds in the case of wire reuse" $ do
            -- ∅;∅;∅ ⊢ let q = apply(INIT,*) in
            --          let _ = apply(DISC, q) in
            --          let q' = apply(INIT, *) in
            --          return q' <== Qubit ; 1
            let term = Let "q" (Apply qinit UnitValue) (Let "_" (Apply qdiscard (Variable "q")) (Let "q'" (Apply qinit UnitValue) (Return (Variable "q'"))))
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "succeeds in the case of data hiding" $ do
            -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in
            --          let (f,_) = (λ(x:Unit).apply(DISC, q),*) in -- effectless let binding
            --          let q' = apply(INIT, *) in
            --          return (f,q') <== (Unit -(1,1)-o Unit) * Qubit ; 2
            let term = Let "q" (Apply qinit UnitValue) (Dest "f" "_" (Pair (Abs "x" UnitType (Apply qdiscard (Variable "q"))) UnitValue) (Let "q'" (Apply qinit UnitValue) (Return (Pair (Variable "f") (Variable "q'")))))
            let (typ, index) = (Tensor (Arrow UnitType UnitType (Number 1) (Number 1)) (WireType Qubit), Number 2)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "fails when the new binding shadows an existing linear variable" $ do
            -- ∅;x:Unit -(0,0)-> Unit;∅ ⊢ let x = apply(INIT, *) in return x <=/= Qubit ; 1
            let term = Let "x" (Apply qinit UnitValue) (Return (Variable "x"))
            let (typ, index) = (WireType Qubit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.fromList [("x",Arrow UnitType UnitType (Number 0) (Number 0))],Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the width annotation tries to ignore data hiding" $ do
            -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in
            --          let (f,_) = (λ(x:Unit).apply(DISC, q),*) in -- effectless let binding
            --          let q' = apply(INIT, *) in
            --          return (f,q') <=/= (Unit -(1,1)-o Unit) * Qubit ; 1
            let term = Let "q" (Apply qinit UnitValue) (Dest "f" "_" (Pair (Abs "x" UnitType (Apply qdiscard (Variable "q"))) UnitValue) (Let "q'" (Apply qinit UnitValue) (Return (Pair (Variable "f") (Variable "q'")))))
            let (typ, index) = (Tensor (Arrow UnitType UnitType (Number 1) (Number 1)) (WireType Qubit), Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the locally bound variable is linear and unused" $ do
            -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in return * <=/= Unit ; 1
            let term = Let "q" (Apply qinit UnitValue) (Return UnitValue)
            let (typ, index) = (UnitType, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the locally bound variable is linear and used more than once" $ do
            -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in return (q,q) <=/= Qubit ⊗ Qubit ; 2
            let term = Let "q" (Apply qinit UnitValue) (Return $ Pair (Variable "q") (Variable "q"))
            let (typ, index) = (Tensor (WireType Qubit) (WireType Qubit), Number 2)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when right hand side is not of the correct type" $ do
            -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in return q <=/= Bit ; 1
            let term = Let "q" (Apply qinit UnitValue) (Return $ Variable "q")
            let (typ, index) = (WireType Bit, Number 1)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft

boxSpec :: Spec
boxSpec = do
    describe "box type checking" $ do
        it "succeeds when the circuit-building function is an identity" $ do
            -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.return x))) <== Circ 1 (Qubit,Qubit) ; 0
            let term = Box (Bundle.WireType Qubit) (Lift $ Return $ Abs "x" (WireType Qubit) (Return $ Variable "x"))
            let (typ, index) = (Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit), Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "succeeds when the circuit-building function builds a single-qubit circuit" $ do
            -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.apply(hadamard,x)))) <== Circ 1 (Qubit,Qubit) ; 0
            let term = Box (Bundle.WireType Qubit) (Lift $ Return $ Abs "x" (WireType Qubit) (Apply hadamard (Variable "x")))
            let (typ, index) = (Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit), Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "succeeds when the circuit-building function builds a two-qubit circuit" $ do
            -- ∅;∅;∅ ⊢ box:Qubit⊗Qubit(lift(return(λx:Qubit⊗Qubit.apply(cnot,x)))) <== Circ 2 (Qubit⊗Qubit,Qubit⊗Qubit) ; 0
            let term = Box (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Lift $ Return $ Abs "x" (Tensor (WireType Qubit) (WireType Qubit)) (Apply cnot (Variable "x")))
            let (typ, index) = (Circ (Number 2) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)), Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
            -- ∅;∅;∅ ⊢ box:Qubit⊗Qubit(lift(return(λx:Qubit⊗Qubit.let (y,z) = x in let y' = apply(hadamard,y) in let z' = apply(pauli-x,z) in return (y',z')))) <== Circ 2 (Qubit⊗Qubit,Qubit⊗Qubit) ; 0
            let circuitBuildingFunction = Abs "x" (Tensor (WireType Qubit) (WireType Qubit)) (Dest "y" "z" (Variable "x") (Let "y'" (Apply hadamard (Variable "y")) (Let "z'" (Apply pauliX (Variable "z")) (Return (Pair (Variable "y'") (Variable "z'"))))))
            let term = Box (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Lift $ Return circuitBuildingFunction)
            let (typ, index) = (Circ (Number 2) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)), Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isRight
        it "fails when the argument is not of a copiable circuit-building function" $ do
            -- ∅;∅;∅ ⊢ box:Qubit(λx:Qubit.return x) <=/= Circ 1 (Qubit,Qubit) ; 0
            let term = Box (Bundle.WireType Qubit) (Abs "x" (WireType Qubit) (Return $ Variable "x"))
            let (typ, index) = (Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit), Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the circuit-building function produces a circuit with too many wires" $ do
            -- ∅;∅;∅ ⊢ box:Qubit⊗Qubit(lift(return(λx:Qubit⊗Qubit.apply(cnot,x)))) <=/= Circ 1 (Qubit⊗Qubit,Qubit⊗Qubit) ; 0
            let term = Box (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Lift $ Return $ Abs "x" (Tensor (WireType Qubit) (WireType Qubit)) (Apply cnot (Variable "x")))
            let (typ, index) = (Circ (Number 1) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)), Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the circuit-building function captures a wire from the environment" $ do
            -- ∅;∅;l:Qubit ⊢ box:Qubit(lift(return(λx:Qubit.apply(cnot,(x,l))))) <=/= Circ 2 (Qubit,Qubit⊗Qubit) ; 0
            let term = Box (Bundle.WireType Qubit) (Lift $ Return $ Abs "x" (WireType Qubit) (Apply cnot (Pair (Variable "x") (Label "l"))))
            let (typ, index) = (Circ (Number 2) (Bundle.WireType Qubit) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)), Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.fromList [("l",Qubit)])
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the type checked against is not a circuit type" $ do
            -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.return x))) <=/= Qubit ; 0
            let term = Box (Bundle.WireType Qubit) (Lift $ Return $ Abs "x" (WireType Qubit) (Return $ Variable "x"))
            let (typ, index) = (WireType Qubit, Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
            -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.return x))) <=/= !(Qubit -o [1,0] Qubit) ; 0
            let (typ, index) = (Bang $ Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0), Number 0)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
            -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.return x))) <=/= Unit ; 0
            let (typ, index) = (UnitType, Number 0)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
        it "fails when the circuit building function does not have the same argument type annotation as the box" $ do
            -- ∅;∅;∅ ⊢ box:Bit(lift(return(λx:Qubit.apply(hadamard,x)))) <=/= Circ 1 (Qubit,Qubit) ; 0
            let term = Box (Bundle.WireType Bit) (Lift $ Return $ Abs "x" (WireType Qubit) (Apply hadamard (Variable "x")))
            let (typ, index) = (Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit), Number 0)
            let (theta,gamma,q) = (Set.empty,Map.empty,Map.empty)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
            -- ∅;∅;∅ ⊢ box:Bit(lift(return(λx:Qubit.apply(hadamard,x)))) <=/= Circ 1 (Bit,Qubit) ; 0
            let (typ, index) = (Circ (Number 1) (Bundle.WireType Bit) (Bundle.WireType Qubit), Number 0)
            termCheckingTest term theta q gamma typ index `shouldSatisfy` isLeft
            





spec :: Spec
spec = do
    primitiveGatesSpec
    boxedCircuitSpec
    varSpec
    applySpec
    returnSpec
    destSpec
    functionSpec
    applicationSpec
    liftSpec
    forceSpec
    letSpec
    boxSpec