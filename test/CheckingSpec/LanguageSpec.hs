module CheckingSpec.LanguageSpec (spec) where

import AST.Bundle (WireType (Qubit, Bit))
import qualified AST.Bundle as Bundle
import AST.Circuit
import AST.Index
import AST.Language (Value(..), Term(..), Type(..), simplifyType, checkTypeEq)
import Checking.Language

import Data.Either (isRight, isLeft)
import qualified Data.Map as Map
import PrettyPrinter
import Test.Hspec
import Data.Either.Extra (fromRight')
import Primitive

-- HELPERS --

simplifyResult :: (Type, Index) -> (Type, Index)
simplifyResult (typ, index) = (simplifyType typ, simplify index)

-- SPECIFICATION --

spec :: Spec
spec = do
    describe "primitive circuit operations" $ do
        let desiredType = Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        it ("hadamard has type " ++ pretty desiredType) $ do
            runValueTypeChecking Map.empty Map.empty hadamard desiredType
                `shouldSatisfy` isRight
        let desiredType = Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit)
        it ("pauli-x has type " ++ pretty desiredType) $ do
            runValueTypeChecking Map.empty Map.empty pauliX desiredType
                `shouldSatisfy` isRight
        let desiredType = Circ (Number 1) Bundle.UnitType (Bundle.WireType Qubit)
        it ("qinit has type " ++ pretty desiredType) $ do
            runValueTypeChecking Map.empty Map.empty qinit desiredType
                `shouldSatisfy` isRight
        let desiredType = Circ (Number 1) (Bundle.WireType Qubit) Bundle.UnitType
        it ("qdiscard has type " ++ pretty desiredType) $ do
            runValueTypeChecking Map.empty Map.empty qdiscard desiredType
                `shouldSatisfy` isRight
        let desiredType = Circ (Number 2) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
                (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
        it ("cnot has type " ++ pretty desiredType) $ do
            runValueTypeChecking Map.empty Map.empty cnot desiredType
                `shouldSatisfy` isRight
    describe "boxed circuit typing" $ do
        context "when inferring" $ do
            it "fails when the input or output interfaces do not match tha circuit's actual output" $ do
                -- ∅;∅ ⊢ (a,Hadamard,*) =/=>
                let term = BoxedCircuit (Bundle.Label "a") (Seq (Id (Map.fromList [("a",Qubit)])) Hadamard (Bundle.Label "a") (Bundle.Label "b")) Bundle.UnitValue
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeInference gamma q term `shouldSatisfy` isLeft
                -- ∅;∅ ⊢ (*,Hadamard,b) =/=>
                let term = BoxedCircuit Bundle.UnitValue (Seq (Id (Map.fromList [("a",Qubit)])) Hadamard (Bundle.Label "a") (Bundle.Label "b")) (Bundle.Label "b")
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeInference gamma q term `shouldSatisfy` isLeft
                -- ∅;∅ ⊢ (a,Init,b) =/=>
                let term = BoxedCircuit (Bundle.Label "a") (Seq (Id Map.empty) Init Bundle.UnitValue (Bundle.Label "b")) (Bundle.Label "b")
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeInference gamma q term `shouldSatisfy` isLeft
        context "when checking" $ do
            it "fails when the circuit is wider than the type annotation" $ do
                -- ∅;∅ ⊢ cnot <=/= Circ 1 (Qubit,Qubit) (Qubit,Qubit)
                let typ = Circ (Number 1) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeChecking gamma q cnot typ `shouldSatisfy` isLeft
    describe "variable typing" $ do
        context "when inferring" $ do
            it "fails when the variable is unbound" $ do
                -- ∅;∅;∅ ⊢ x =/=>
                runValueTypeInference Map.empty Map.empty (Variable "x") `shouldSatisfy` isLeft
        context "when checking" $ do
            it "fails when the context type and the checked type for the variable do not match" $ do
                -- ∅;x:Qubit;∅ ⊢ x <=/= Bit
                runValueTypeChecking Map.empty Map.empty (Variable "x") (WireType Bit) `shouldSatisfy` isLeft
    describe "label typing" $ do
        context "when inferring" $ do
            it "succeeds if the label is alone in the environment" $ do
                -- ∅;a:Qubit;∅ ⊢ a ==> Qubit
                runValueTypeInference Map.empty (Map.fromList [("a",Qubit)]) (Label "a") `shouldBe` Right (WireType Qubit)
            it "fails if the label is not in the environment" $ do
                -- ∅;∅;∅ ⊢ a =/=>
                runValueTypeInference Map.empty Map.empty (Label "a") `shouldSatisfy` isLeft
            it "fails if there are other labels in the environment" $ do
                -- ∅;a:Qubit,b:Qubit ⊢ a =/=>
                runValueTypeInference Map.empty (Map.fromList [("a",Qubit),("b",Qubit)]) (Label "a") `shouldSatisfy` isLeft
            it "fails if there are linear variables in the environment" $ do
                -- x:Qubit -o [1,0] Qubit;a:Qubit ⊢ a =/=>
                runValueTypeInference (Map.fromList [("x", Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0))]) (Map.fromList [("a",Qubit)]) (Label "a") `shouldSatisfy` isLeft
        context "when checking" $ do
            it "fails if the type checked against is incorrect" $ do
                -- ∅;a:Qubit ⊢ a <=/= Bit
                runValueTypeChecking Map.empty (Map.fromList [("a",Qubit)]) (Label "a") (WireType Bit) `shouldSatisfy` isLeft
    describe "apply typing" $ do
        context "when inferring" $ do
            it "succeeds when the term is well-typed" $ do
                -- ∅;∅;l:Qubit ⊢ Apply (Hadamard,l) ==> Qubit ; 1
                let term = Apply hadamard $ Label "l"
                let (gamma,q) = (Map.empty, Map.fromList [("l",Qubit)])
                runTermTypeInference gamma q term `shouldBe` Right (WireType Qubit, Number 1)
                -- ∅;∅;∅ ⊢ Apply (Init,*) ==> Qubit ; 1
                let term = Apply qinit UnitValue
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldBe` Right (WireType Qubit, Number 1)
            it "fails when there are unused linear resources" $ do
                -- ∅;∅;l:Qubit,k:Qubit ⊢ Apply (Hadamard,l) =/=>
                let term = Apply hadamard $ Label "l"
                let (gamma,q) = (Map.empty, Map.fromList [("l",Qubit),("k",Qubit)])
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the first argument is not of circuit type" $ do
                -- ∅;∅;∅ ⊢ Apply (*,*) =/=>
                let term = Apply UnitValue UnitValue
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the second argument is not of bundle type" $ do
                -- ∅;x:!Unit;∅ ⊢ Apply (Init,x) =/=>
                let term = Apply qinit $ Variable "x"
                let (gamma,q) = (Map.fromList [("x",Bang UnitType)],Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the second argument does not have type matching the circuit's input" $ do
                -- ∅;∅;l:Bit ⊢ Apply (Hadamard,l) =/=>
                let term = Apply hadamard $ Label "l"
                let (gamma,q) = (Map.empty,Map.fromList [("l",Bit)])
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
        context "when checking" $ do
            it "succeeds when the width upper bound is higher than the circuit's width" $ do
                -- ∅;∅;∅ ⊢ Apply (Init,*) <== Qubit ; 2
                let term = Apply qinit UnitValue
                let (typ, index) = (WireType Qubit, Number 2)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isRight
            it "fails when the circuit produced by the term has width greater than the index" $ do
                -- ∅;∅;∅ ⊢ Apply (Init,*) <=/= Qubit ; 0
                let term = Apply qinit UnitValue
                let (typ, index) = (WireType Qubit, Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
            it "fails when the circuits output does not match the checked type" $ do
                -- ∅;∅;∅ ⊢ Apply (Init,*) <=/= Bit ; 1
                let term = Apply qinit UnitValue
                let (typ, index) = (WireType Bit, Number 1)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
    describe "return typing" $ do
        context "when inferring" $ do
            it "succeeds when the context is empty and the return value is nonlinear" $ do
                -- ∅;∅;∅ ⊢ return * ==> Unit ; 0
                let term = Return UnitValue
                let (typ, index) = (UnitType, Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "succeeds when the context is a parameter context and the return value is nonlinear" $ do
                -- ∅;x:Unit,y:!(Qubit -o [1,0] Qubit),z:Circ 1 (Qubit,Qubit);∅ ⊢ return z ==> Circ 1 (Qubit,Qubit) ; 0
                let term = Return $ Variable "z"
                let (typ, index) = (Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit), Number 0)
                let (gamma,q) = (Map.fromList [("x",UnitType),("y",Bang $ Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0)),("z",Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit))],Map.empty)
                runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "succeeds when the return value is linear and the contexts do not contain any other resources" $ do
                -- ∅;x:!(Qubit -o [1,0] Qubit),y:Qubit;z:Bit ⊢ return (y,z) ==> Qubit ⊗ Bit ; 2
                let term = Return $ Pair (Variable "y") (Label "z")
                let (typ, index) = (Tensor (WireType Qubit) (WireType Bit), Number 2)
                let (gamma,q) = (Map.fromList [("x",Bang $ Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0)),("y",WireType Qubit)],Map.fromList [("z",Bit)])
                runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "fails when the return value is linear and the contexts contain other linear resources" $ do
                -- ∅;x:!(Qubit -o [1,0] Qubit),y:Qubit;z:Bit ⊢ return x =/=>
                let term = Return $ Variable "x"
                let (gamma,q) = (Map.fromList [("x",Bang $ Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0)),("y",WireType Qubit)],Map.fromList [("z",Bit)])
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
        context "when checking" $ do
            it "succeeds when the checked resource bound is at least as high as the wire count of the returned value" $ do
                -- ∅;x:Qubit,y:Bit;∅ ⊢ return (x,y) <== Qubit ⊗ Bit ; 2
                let term = Return $ Pair (Variable "x") (Variable "y")
                let (typ, index) = (Tensor (WireType Qubit) (WireType Bit), Number 2)
                let (gamma,q) = (Map.fromList [("x",WireType Qubit),("y",WireType Bit)],Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isRight
                -- ∅;x:Qubit⊗Qubit;∅ ⊢ return x <== Qubit⊗Qubit ; 2
                let term = Return $ Variable "x"
                let (typ, index) = (Tensor (WireType Qubit) (WireType Qubit), Number 2)
                let (gamma,q) = (Map.fromList [("x",Tensor (WireType Qubit) (WireType Qubit))],Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isRight
            it "succeeds when the checked type is a supertype of the value's type" $ do
                -- ∅;c:Circ [1] (Qubit,Qubit);∅ ⊢ return c <== Circ [2] (Qubit,Qubit) ; 0
                let term = Return $ Variable "c"
                let (typ, index) = (Circ (Number 2) (Bundle.WireType Qubit) (Bundle.WireType Qubit), Number 0)
                let (gamma,q) = (Map.fromList [("c",Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit))],Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isRight
            it "fails when the checked type is not a supertype of the value's type" $ do
                -- ∅;x:Qubit;∅ ⊢ return x <== Bit ; 1
                let term = Return $ Variable "x"
                let (typ, index) = (WireType Bit, Number 1)
                let (gamma,q) = (Map.fromList [("x",WireType Qubit)],Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
            it "fails when the checked resource bound is lower than the wire count of the returned value" $ do
                -- ∅;x:Qubit,y:Bit;∅ ⊢ return (x,y) <== Qubit ⊗ Bit ; 1
                let term = Return $ Pair (Variable "x") (Variable "y")
                let (typ, index) = (Tensor (WireType Qubit) (WireType Bit), Number 1)
                let (gamma,q) = (Map.fromList [("x",WireType Qubit),("y",WireType Bit)],Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
    describe "destructuring let typing" $ do
        context "when inferring" $ do
            it "succeeds when the rule's premises hold" $ do
                -- ∅;∅;∅ ⊢ let (c,u) = (Init,*) in apply(c,u) ==> Qubit ; 1
                let term = Dest "c" "u" (Pair qinit UnitValue) (Apply (Variable "c") (Variable "u"))
                let (typ, index) = (WireType Qubit, Number 1)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "fails when binding shadows existing variable" $ do
                -- ∅;c:Unit;∅ ⊢ let (c,u) = (Init,*) in apply(c,u) =/=>
                let term = Dest "c" "u" (Pair qinit UnitValue) (Apply (Variable "c") (Variable "u"))
                let (gamma,q) = (Map.fromList [("c",UnitType)],Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the two variables shadow each other" $ do
                -- ∅;∅;∅ ⊢ let (c,c) = (Init,*) in apply(c,c) <=/= Qubit ; 1
                let term = Dest "c" "c" (Pair qinit UnitValue) (Apply (Variable "c") (Variable "c"))
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the destructurand is not of tensor type" $ do
                -- ∅;∅;∅ ⊢ let (c,u) = * in return * <=/= Unit ; 0
                let term = Dest "c" "u" UnitValue $ Return UnitValue
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
    describe "force typing" $ do
        context "when inferring" $ do
            it "infers type A when the argument is a value of type !A" $ do
                -- ∅;∅;∅ ⊢ force(lift(return *)) ==> Unit ; 0
                let term = Force $ Lift $ Return UnitValue
                let (typ,index) = (UnitType,Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldBe` Right (typ,index)
                -- ∅;∅;∅ ⊢ force(lift(return λx:Qubit.return x)) ==> Qubit -o [1,0] Qubit ; 0
                let term = Force $ Lift $ Return $ Abs "x" (WireType Qubit) (Return $ Variable "x")
                let (typ,index) = (Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0),Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldBe` Right (typ,index)
            it "fails when the argument is not of bang type" $ do
                -- ∅;∅;∅ ⊢ force(*) =/=>
                let term = Force UnitValue
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
                -- ∅;∅;∅ ⊢ force(λx:Qubit.return x) =/=>
                let term = Force $ Abs "x" (WireType Qubit) (Return $ Variable "x")
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
    describe "lift typing" $ do
        context "when inferring" $ do
            it "succeeds when the rule premises hold" $ do
                -- ∅;∅;∅ ⊢ lift(return(*)) ==> !Unit
                let term = Lift $ Return UnitValue
                let typ = Bang UnitType
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeInference gamma q term `shouldBe` Right typ
                -- ∅;∅;∅ ⊢ lift(return λx:Qubit.return x) ==> !(Qubit -o [1,0] Qubit)
                let term = Lift $ Return $ Abs "x" (WireType Qubit) (Return $ Variable "x")
                let typ = Bang $ Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeInference gamma q term `shouldBe` Right typ
            it "fails when the term consumes linear resources" $ do
                -- ∅;f:Unit -o [0,0] Unit;∅ ⊢ lift(return f) =/=>
                let term = Lift $ Return $ Variable "f"
                let (gamma,q) = (Map.fromList [("f",Arrow UnitType UnitType (Number 0) (Number 0))],Map.empty)
                runValueTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the term produces a circuit" $ do
                -- ∅;∅;∅ ⊢ lift(apply(Init,*)) =/=>
                let term = Lift $ Apply qinit UnitValue
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeInference gamma q term `shouldSatisfy` isLeft
    describe "empty sized list typing" $ do
        context "when checking" $ do
            it "succeeds when the rule premises hold" $ do
                -- ∅;∅;∅ ⊢ [] <== List[0] Qubit
                let term = Nil
                let typ = List (Number 0) (WireType Qubit)
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeChecking gamma q term typ `shouldSatisfy` isRight
            it "fails when the checked length is not 0" $ do
                -- ∅;∅;∅ ⊢ [] <=/= List[1] Qubit
                let term = Nil
                let typ = List (Number 1) (WireType Qubit)
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeChecking gamma q term typ `shouldSatisfy` isLeft
            it "fails when type checking against a non-list type" $ do
                -- ∅;∅;∅ ⊢ [] <=/= *
                let term = Nil
                let typ = UnitType
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeChecking gamma q term typ `shouldSatisfy` isLeft
    describe "non-empty sized list typing" $ do
        context "when inferring" $ do
            it "succeeds when the rule premises hold" $ do
                -- ∅;x:Qubit;a:Qubit,b:Qubit ⊢ [x,a,b] ==> List[x] Qubit and x = 3
                let term = Cons (Variable "x") (Cons (Label "a") (Cons (Label "b") Nil))
                let typ = List (Number 3) (WireType Qubit)
                let (gamma,q) = (Map.fromList [("x",WireType Qubit)],Map.fromList [("a",Qubit),("b",Qubit)])
                simplifyType <$> runValueTypeInference gamma q term `shouldBe` Right typ
                -- ∅;l:List[8] Bit;a:Bit ⊢ a : l ==> List[9] Bit
                let term = Cons (Label "a") (Variable "l")
                let typ = List (Number 9) (WireType Bit)    
                let (gamma,q) = (Map.fromList [("l",List (Number 8) (WireType Bit))],Map.fromList [("a",Bit)])
                simplifyType <$> runValueTypeInference gamma q term `shouldBe` Right typ
                -- i;l:List[i] Bit;a:Bit ⊢ a : l ==> List[i+1] Bit
                let term = Cons (Label "a") (Variable "l")
                let typ = List (Plus (IndexVariable "i") (Number 1)) (WireType Bit)
                let (gamma,q) = (Map.fromList [("l",List (IndexVariable "i") (WireType Bit))],Map.fromList [("a",Bit)])
                runValueTypeInference gamma q term `shouldBe` Right typ
            it "fails when cons-ing elements of mismatching types" $ do
                -- ∅;∅;a:Qubit,b:Bit ⊢ [a,b] =/=>
                let term = Cons (Label "a") (Cons (Label "b") Nil)
                let (gamma,q) = (Map.empty,Map.fromList [("a",Qubit),("b",Bit)])
                runValueTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when cons-ing an element to something that is not a list" $ do
                -- ∅;∅;a:Qubit ⊢ a : * =/=>
                let term = Cons (Label "a") UnitValue
                let (gamma,q) = (Map.empty,Map.fromList [("a",Qubit)])
                runValueTypeInference gamma q term `shouldSatisfy` isLeft
        context "when checking" $ do
            it "fails when the checked length is incorrect" $ do
                -- ∅;l:List[8] Bit;a:Bit ⊢ a : l <=/= List[4] Bit
                let term = Cons (Label "a") (Variable "l")
                let typ = List (Number 4) (WireType Bit)    
                let (gamma,q) = (Map.fromList [("l",List (Number 8) (WireType Bit))],Map.fromList [("a",Bit)])
                runValueTypeChecking gamma q term typ `shouldSatisfy` isLeft
            it "fails when the checked element type is incorrect" $ do
                -- ∅;∅;a:Qubit ⊢ [a] <=/= List[1] Bit
                let term = Cons (Label "a") Nil
                let typ = List (Number 1) (WireType Bit)
                let (gamma,q) = (Map.empty,Map.fromList [("a",Qubit)])
                runValueTypeChecking gamma q term typ `shouldSatisfy` isLeft
            it "fails when type checking against a non-list type" $ do
                -- ∅;∅;a:Qubit ⊢ [a] <=/= Qubit
                let term = Cons (Label "a") Nil
                let typ = WireType Qubit
                let (gamma,q) = (Map.empty,Map.fromList [("a",Qubit)])
                runValueTypeChecking gamma q term typ `shouldSatisfy` isLeft
    describe "let typing" $ do
        context "when inferring" $ do
            it "succeeds in case of simple sequencing" $ do
                -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in
                --          let q' = apply(H, q) in
                --          return q' ==> Qubit ; 1
                let term = Let "q" (Apply qinit UnitValue) (Let "q'" (Apply hadamard (Variable "q")) (Return (Variable "q'")))
                let (typ, index) = (WireType Qubit, Number 1)
                let (gamma,q) = (Map.empty,Map.empty)
                simplifyResult <$> runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "succeeds in the case of increasing width sequencing" $ do
                -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in
                --          let q' = apply(INIT, *) in
                --          return (q,q') ==> Qubit ⊗ Qubit ; 2 
                let term = Let "q" (Apply qinit UnitValue) (Let "q'" (Apply qinit UnitValue) (Return (Pair (Variable "q") (Variable "q'"))))
                let (typ, index) = (Tensor (WireType Qubit) (WireType Qubit), Number 2)
                let (gamma,q) = (Map.empty,Map.empty)
                simplifyResult <$> runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "succeeds in the case of wire reuse" $ do
                -- ∅;∅;∅ ⊢ let q = apply(INIT,*) in
                --          let _ = apply(DISC, q) in
                --          let q' = apply(INIT, *) in
                --          return q' ==> Qubit ; 1
                let term = Let "q" (Apply qinit UnitValue) (Let "_" (Apply qdiscard (Variable "q")) (Let "q'" (Apply qinit UnitValue) (Return (Variable "q'"))))
                let (typ, index) = (WireType Qubit, Number 1)
                let (gamma,q) = (Map.empty,Map.empty)
                simplifyResult <$> runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "succeeds in the case of data hiding" $ do
                -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in
                --          let (f,_) = (λ(x:Unit).apply(DISC, q),*) in -- effectless let binding
                --          let q' = apply(INIT, *) in
                --          return (f,q') ==> (Unit -(1,1)-o Unit) * Qubit ; 2
                let term = Let "q" (Apply qinit UnitValue) (Dest "f" "_" (Pair (Abs "x" UnitType (Apply qdiscard (Variable "q"))) UnitValue) (Let "q'" (Apply qinit UnitValue) (Return (Pair (Variable "f") (Variable "q'")))))
                let (typ, index) = (Tensor (Arrow UnitType UnitType (Number 1) (Number 1)) (WireType Qubit), Number 2)
                let (gamma,q) = (Map.empty,Map.empty)
                simplifyResult <$> runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "fails when the new binding shadows an existing linear variable" $ do
                -- ∅;x:Unit -(0,0)-> Unit;∅ ⊢ let x = apply(INIT, *) in return x =/=>
                let term = Let "x" (Apply qinit UnitValue) (Return (Variable "x"))
                let (gamma,q) = (Map.fromList [("x",Arrow UnitType UnitType (Number 0) (Number 0))],Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the locally bound variable is linear and unused" $ do
                -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in return * =/=>
                let term = Let "q" (Apply qinit UnitValue) (Return UnitValue)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the locally bound variable is linear and used more than once" $ do
                -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in return (q,q) =/=>
                let term = Let "q" (Apply qinit UnitValue) (Return $ Pair (Variable "q") (Variable "q"))
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
        context "when checking" $ do
            it "fails when right hand side is not of the correct type" $ do
                -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in return q <=/= Bit ; 1
                let term = Let "q" (Apply qinit UnitValue) (Return $ Variable "q")
                let (typ, index) = (WireType Bit, Number 1)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
            it "fails when the width annotation tries to ignore data hiding" $ do
                -- ∅;∅;∅ ⊢ let q = apply(INIT, *) in
                --          let (f,_) = (λ(x:Unit).apply(DISC, q),*) in -- effectless let binding
                --          let q' = apply(INIT, *) in
                --          return (f,q') <=/= (Unit -(1,1)-o Unit) * Qubit ; 1
                let term = Let "q" (Apply qinit UnitValue) (Dest "f" "_" (Pair (Abs "x" UnitType (Apply qdiscard (Variable "q"))) UnitValue) (Let "q'" (Apply qinit UnitValue) (Return (Pair (Variable "f") (Variable "q'")))))
                let (typ, index) = (Tensor (Arrow UnitType UnitType (Number 1) (Number 1)) (WireType Qubit), Number 1)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
    describe "function typing" $ do
        context "when inferring" $ do
            it "succeeds when the rule's premises hold" $ do
                -- ∅;∅;∅ ⊢ λx:Qubit. return x ==> Qubit -o [1,0] Qubit
                let term = Abs "x" (WireType Qubit) (Return $ Variable "x")
                let typ = Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeInference gamma q term `shouldBe` Right typ
                -- ∅;∅;l:Qubit ⊢ λx:UnitType. return l ==> Qubit-o [1,1] Qubit
                let term = Abs "x" UnitType (Return $ Label "l")
                let typ = Arrow UnitType (WireType Qubit) (Number 1) (Number 1)
                let (gamma,q) = (Map.empty,Map.fromList [("l",Qubit)])
                runValueTypeInference gamma q term `shouldBe` Right typ
                -- ∅;∅;l:Qubit ⊢ λc:Circ[3](Qubit,Qubit). apply(c,l) ==> Circ[3](Qubit,Qubit) -o [3,1] Qubit
                let term = Abs "c" (Circ (Number 3) (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Apply (Variable "c") (Label "l"))
                let typ = Arrow (Circ (Number 3) (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (WireType Qubit) (Number 3) (Number 1)
                let (gamma,q) = (Map.empty,Map.fromList [("l",Qubit)])
                runValueTypeInference gamma q term `shouldBe` Right typ
                -- ∅;x:Qubit;∅ ⊢ λy:Qubit. apply(CNOT,(x,y)) ==> Qubit -o [2,1] (Qubit,Qubit)
                let term = Abs "y" (WireType Qubit) (Apply cnot (Pair (Variable "x") (Variable "y")))
                let typ = Arrow (WireType Qubit) (Tensor (WireType Qubit) (WireType Qubit)) (Number 2) (Number 1)
                let (gamma,q) = (Map.fromList [("x",WireType Qubit)],Map.empty)
                runValueTypeInference gamma q term `shouldBe` Right typ
                -- i;∅;∅ ⊢ λx:List[i] Qubit. let y = apply(qinit,*) in return y : x ==> List[i] Qubit -o [i+1,0] List[i+1] Qubit
                let term = Abs "x" (List (IndexVariable "i") (WireType Qubit)) (Let "y" (Apply qinit UnitValue) (Return $ Cons (Variable "y") (Variable "x")))
                let typ = Arrow (List (IndexVariable "i") (WireType Qubit)) (List (Plus (IndexVariable "i") (Number 1)) (WireType Qubit)) (Plus (IndexVariable "i") (Number 1)) (Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                fromRight' (runValueTypeInference gamma q term) `shouldSatisfy` checkTypeEq typ
            it "fails when the function does not use its linear argument" $ do
                -- ∅;∅;∅ ⊢ λx:Qubit. return * =/=> 
                let term = Abs "x" (WireType Qubit) (Return UnitValue)
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the function uses its linear argument more than once" $ do
                -- ∅;∅;∅ ⊢ λx:Qubit. return (x,x) =/=>
                let term = Abs "x" (WireType Qubit) (Return $ Pair (Variable "x") (Variable "x"))
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeInference gamma q term `shouldSatisfy` isLeft
        context "when checking" $ do
            it "fails when the function is required to have an input type that's different from its annotation" $ do
                -- ∅;∅;∅ ⊢ λx:Qubit. return x <=/= Qubit -o [1,1] Qubit
                let term = Abs "x" (WireType Qubit) (Return $ Variable "x")
                let typ = Arrow (WireType Bit) (WireType Qubit) (Number 1) (Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeChecking gamma q term typ `shouldSatisfy` isLeft
            it "fails when the function builds too large a circuit" $ do
                -- ∅;∅;∅ ⊢ λx:Qubit⊗Qubit. apply(CNOT,x) <=/= Qubit⊗Qubit -o [1,0] Qubit⊗Qubit
                let term = Abs "x" (Tensor (WireType Qubit) (WireType Qubit)) (Apply cnot (Variable "x"))
                let typ = Arrow (Tensor (WireType Qubit) (WireType Qubit)) (Tensor (WireType Qubit) (WireType Qubit)) (Number 1) (Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runValueTypeChecking gamma q term typ `shouldSatisfy` isLeft
            it "fails when the type does not correctly reflect the amount of captured wires" $ do
                -- ∅;∅;l:Qubit ⊢ λx:UnitType. return l <=/= Qubit -o [1,0] Qubit
                let term = Abs "x" UnitType (Return $ Label "l")
                let typ = Arrow UnitType (WireType Qubit) (Number 1) (Number 0)
                let (gamma,q) = (Map.empty,Map.fromList [("l",Qubit)])
                runValueTypeChecking gamma q term typ `shouldSatisfy` isLeft
    describe "application typing" $ do
        context "when inferring" $ do
            it "succeeds when the rule's premises hold" $ do
                -- ∅;∅;l:Qubit ⊢ (λx:Qubit.return x)l ==> Qubit ; 1
                let term = App (Abs "x" (WireType Qubit) (Return $ Variable "x")) (Label "l")
                let (typ, index) = (WireType Qubit, Number 1)
                let (gamma,q) = (Map.empty,Map.fromList [("l",Qubit)])
                runTermTypeInference gamma q term `shouldBe` Right (typ, index)
                -- ∅;∅;l:Qubit,k:Bit ⊢ (λp:Qubit⊗Bit.let (x,y) = p in return (y,x)) (l,k) ==> Bit⊗Qubit ; 2
                let term = App
                        (Abs "p" (Tensor (WireType Qubit) (WireType Bit))
                            (Dest "x" "y" (Variable "p") (Return $ Pair (Variable "y") (Variable "x"))))
                        (Pair (Label "l") (Label "k"))
                let (typ, index) = (Tensor (WireType Bit) (WireType Qubit), Number 2)
                let (gamma,q) = (Map.empty,Map.fromList [("l",Qubit),("k",Bit)])
                runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "fails when the argument type does not match the function's input type" $ do
                -- ∅;∅;l:Bit ⊢ (λx:Qubit.return x)l =/=>
                let term = App (Abs "x" (WireType Qubit) (Return $ Variable "x")) (Label "l")
                let (gamma,q) = (Map.empty,Map.fromList [("l",Bit)])
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the applicand is not a function" $ do
                -- ∅;∅;∅ ⊢ lift(return *) * =/=>
                let term = App (Lift $ Return UnitValue) UnitValue
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
                -- ∅;f:Qubit,q:Qubit;∅ ⊢ f q =/=>
                let term = App (Variable "f") (Variable "q")
                let (gamma,q) = (Map.fromList [("f",WireType Qubit),("q",WireType Qubit)],Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
        context "when checking" $ do
            it "fails when the output type does not match the type checked against" $ do
                -- ∅;∅;l:Qubit ⊢ (λx:Qubit.return x)l <=/= Bit ; 1
                let term = App (Abs "x" (WireType Qubit) (Return $ Variable "x")) (Label "l")
                let (typ, index) = (WireType Bit, Number 1)
                let (gamma,q) = (Map.empty,Map.fromList [("l",Qubit)])
                runTermTypeChecking  gamma q term typ index `shouldSatisfy` isLeft
            it "fails when the function produces too large of a circuit" $ do
                -- ∅;∅;l:Qubit,k:Qubit ⊢ (λx:Qubit. apply(CNOT,(x,l)))k <=/= (Qubit⊗Qubit) ; 1
                let term = App (Abs "x" (WireType Qubit) (Apply cnot (Pair (Variable "x") (Label "l")))) (Label "k")
                let (typ, index) = (Tensor (WireType Qubit) (WireType Qubit), Number 1)
                let (gamma,q) = (Map.empty,Map.fromList [("l",Qubit),("k",Qubit)])
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
    describe "box typing" $ do
        context "when inferring" $ do
            it "succeeds when the circuit-building function is an identity" $ do
                -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.return x))) ==> Circ 1 (Qubit,Qubit) ; 0
                let term = Box (Bundle.WireType Qubit) (Lift $ Return $ Abs "x" (WireType Qubit) (Return $ Variable "x"))
                let (typ, index) = (Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit), Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "succeeds when the circuit-building function builds a single-qubit circuit" $ do
                -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.apply(hadamard,x)))) ==> Circ 1 (Qubit,Qubit) ; 0
                let term = Box (Bundle.WireType Qubit) (Lift $ Return $ Abs "x" (WireType Qubit) (Apply hadamard (Variable "x")))
                let (typ, index) = (Circ (Number 1) (Bundle.WireType Qubit) (Bundle.WireType Qubit), Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "succeeds when the circuit-building function builds a two-qubit circuit" $ do
                -- ∅;∅;∅ ⊢ box:Qubit⊗Qubit(lift(return(λx:Qubit⊗Qubit.apply(cnot,x)))) ==> Circ 2 (Qubit⊗Qubit,Qubit⊗Qubit) ; 0
                let term = Box (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Lift $ Return $ Abs "x" (Tensor (WireType Qubit) (WireType Qubit)) (Apply cnot (Variable "x")))
                let (typ, index) = (Circ (Number 2) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)), Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                simplifyResult <$> runTermTypeInference gamma q term `shouldBe` Right (typ, index)
                -- ∅;∅;∅ ⊢ box:Qubit⊗Qubit(lift(return(
                --              λx:Qubit⊗Qubit. let (y,z) = x in
                --                              let y' = apply(hadamard,y) in
                --                              let z' = apply(pauli-x,z) in
                --                              return (y',z'))))
                --      ==> Circ 2 (Qubit⊗Qubit,Qubit⊗Qubit) ; 0
                let circuitBuildingFunction = Abs "x" (Tensor (WireType Qubit) (WireType Qubit)) (Dest "y" "z" (Variable "x") (Let "y'" (Apply hadamard (Variable "y")) (Let "z'" (Apply pauliX (Variable "z")) (Return (Pair (Variable "y'") (Variable "z'"))))))
                let term = Box (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Lift $ Return circuitBuildingFunction)
                let (typ, index) = (Circ (Number 2) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)), Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                simplifyResult <$> runTermTypeInference gamma q term `shouldBe` Right (typ, index)
            it "fails when the argument is not of a copiable function" $ do
                -- ∅;∅;∅ ⊢ box:Qubit(λx:Qubit.return x) =/=>
                let term = Box (Bundle.WireType Qubit) (Abs "x" (WireType Qubit) (Return $ Variable "x"))
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the circuit-building function captures a wire from the environment" $ do
                -- ∅;∅;l:Qubit ⊢ box:Qubit(lift(return(λx:Qubit.apply(cnot,(x,l))))) =/=>
                let term = Box (Bundle.WireType Qubit) (Lift $ Return $ Abs "x" (WireType Qubit) (Apply cnot (Pair (Variable "x") (Label "l"))))
                let (gamma,q) = (Map.empty,Map.fromList [("l",Qubit)])
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
            it "fails when the circuit building function does not have the same argument type annotation as the box" $ do
                -- ∅;∅;∅ ⊢ box:Bit(lift(return(λx:Qubit.apply(hadamard,x)))) =/=>
                let term = Box (Bundle.WireType Bit) (Lift $ Return $ Abs "x" (WireType Qubit) (Apply hadamard (Variable "x")))
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
                -- ∅;∅;∅ ⊢ box:Bit(lift(return(λx:Qubit.apply(hadamard,x)))) <=/= Circ 1 (Bit,Qubit) ; 0
                let term = Box (Bundle.WireType Bit) (Lift $ Return $ Abs "x" (WireType Qubit) (Apply hadamard (Variable "x")))
                runTermTypeInference gamma q term `shouldSatisfy` isLeft
        context "when checking" $ do
            it "fails when the circuit-building function produces too wide a circuit" $ do
                -- ∅;∅;∅ ⊢ box:Qubit⊗Qubit(lift(return(λx:Qubit⊗Qubit.apply(cnot,x)))) <=/= Circ 1 (Qubit⊗Qubit,Qubit⊗Qubit) ; 0
                let term = Box (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Lift $ Return $ Abs "x" (Tensor (WireType Qubit) (WireType Qubit)) (Apply cnot (Variable "x")))
                let (typ, index) = (Circ (Number 1) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)) (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit)), Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
            it "fails when the type checked against is not a circuit type" $ do
                -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.return x))) <=/= Qubit ; 0
                let term = Box (Bundle.WireType Qubit) (Lift $ Return $ Abs "x" (WireType Qubit) (Return $ Variable "x"))
                let (typ, index) = (WireType Qubit, Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
                -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.return x))) <=/= !(Qubit -o [1,0] Qubit) ; 0
                let (typ, index) = (Bang $ Arrow (WireType Qubit) (WireType Qubit) (Number 1) (Number 0), Number 0)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
                -- ∅;∅;∅ ⊢ box:Qubit(lift(return(λx:Qubit.return x))) <=/= Unit ; 0
                let (typ, index) = (UnitType, Number 0)
                runTermTypeChecking gamma q term typ index `shouldSatisfy` isLeft
    describe "fold typing" $ do
        context "when inferring" $ do
            it "succeeds when the premises hold" $ do
                -- ∅;∅ ⊢ fold[i] lift(return λx:List[i] Qubit ⊗ Qubit. let (y,z) = x in return z:y) [] ==> List[x0] Qubit -o [x0,0] List[x0] Qubit
                let stepfun = Abs "x" (Tensor (List (IndexVariable "i") (WireType Qubit)) (WireType Qubit)) (Dest "y" "z" (Variable "x") (Return (Cons (Variable "z") (Variable "y"))))
                let term = Fold "i" (Lift (Return stepfun)) Nil
                let typ = Arrow (List (IndexVariable "x1") (WireType Qubit)) (List (IndexVariable "x1") (WireType Qubit)) (IndexVariable "x1") (Number 0)
                let (gamma,q) = (Map.empty,Map.empty)
                simplifyType <$> runValueTypeInference gamma q term `shouldBe` Right typ