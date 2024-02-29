module Lang.Unified.InferSpec (spec) where

import Bundle.AST (BundleType (..), WireType (..),Bundle(..))
import Data.Either
import Index.AST
import Index.Semantics
import Lang.Type.AST
import Lang.Type.Semantics
import Lang.Unified.AST
import Lang.Unified.Infer
import Test.Hspec
import qualified Circuit

simplify :: Either TypingError (Type, Index) -> Either TypingError (Type, Index)
simplify (Left err) = Left err
simplify (Right (t, i)) = Right (simplifyType t, simplifyIndex i)

spec :: Spec
spec = do
  describe "type inference on values" $ do
    context "when typing the unit value" $ do
      it "produces the unit type if the context is empty" $ do
        -- ∅;∅;∅ ⊢ () ==> () ; 0
        runTypeInferenceWith emptyEnv EUnit `shouldBe` Right (TUnit, Number 0)
      it "produces the unit type if the context is non-linear" $ do
        -- ∅;x:(),y:Circ[1](Qubit,Qubit);∅ ⊢ () =/=> () ; 0
        let gamma = [("x", TUnit), ("y", TCirc (Number 1) (BTWire Qubit) (BTWire Qubit))]
        runTypeInferenceWith (makeEnv gamma []) EUnit `shouldBe` Right (TUnit, Number 0)
      it "fails when there are linear resources in the environment" $ do
        -- ∅;x:Qubit;∅ ⊢ () =/=>
        let gamma = [("x", TWire Qubit)]
        runTypeInferenceWith (makeEnv gamma []) EUnit `shouldSatisfy` isLeft
        -- ∅;∅;x:Qubit ⊢ () =/=>
        let q = [("x", Qubit)]
        runTypeInferenceWith (makeEnv [] q) EUnit `shouldSatisfy` isLeft
    context "when typing labels" $ do
      it "produces the type of the label if the rest of the context is empty" $ do
        -- ∅;∅;l:Qubit ⊢ l ==> Qubit ; 1
        let q = [("l", Qubit)]
        runTypeInferenceWith (makeEnv [] q) (ELabel "l") `shouldBe` Right (TWire Qubit, Number 1)
        -- ∅;∅;l:Bit ⊢ l ==> Bit ; 1
        let b = [("l", Bit)]
        runTypeInferenceWith (makeEnv [] b) (ELabel "l") `shouldBe` Right (TWire Bit, Number 1)
      it "produces the type of the label if the rest of the context is nonlinear" $ do
        -- ∅;x:();l:Qubit ⊢ l ==> Qubit ; 1
        let gamma = [("x", TUnit)]
        let q = [("l", Qubit)]
        runTypeInferenceWith (makeEnv gamma q) (ELabel "l") `shouldBe` Right (TWire Qubit, Number 1)
      it "fails when there are other linear resources in the environment" $ do
        -- ∅;x:Qubit;l:Qubit ⊢ l =/=>
        let gamma = [("x", TWire Qubit)]
        let q = [("l", Qubit)]
        runTypeInferenceWith (makeEnv gamma q) (ELabel "l") `shouldSatisfy` isLeft
        -- ∅;∅;x:Qubit,l:Qubit ⊢ l =/=>
        let q = [("x", Qubit), ("l", Qubit)]
        runTypeInferenceWith (makeEnv [] q) (ELabel "l") `shouldSatisfy` isLeft
    context "when typing variables" $ do
      it "produces the type of the variable if the rest of the context is empty" $ do
        -- ∅;x:Qubit;∅ ⊢ x ==> Qubit ; 1
        let gamma = [("x", TWire Qubit)]
        runTypeInferenceWith (makeEnv gamma []) (EVar "x") `shouldBe` Right (TWire Qubit, Number 1)
      it "produces the type of the variable if the rest of the context is nonlinear" $ do
        -- ∅;x:(),y:Qubit;∅ ⊢ y ==> Qubit ; 1
        let gamma = [("x", TUnit), ("y", TWire Qubit)]
        runTypeInferenceWith (makeEnv gamma []) (EVar "y") `shouldBe` Right (TWire Qubit, Number 1)
      it "fails when there are other linear resources in the environment" $ do
        -- ∅;x:Qubit,y:Qubit;∅ ⊢ y =/=>
        let gamma = [("x", TWire Qubit), ("y", TWire Qubit)]
        runTypeInferenceWith (makeEnv gamma []) (EVar "y") `shouldSatisfy` isLeft
    context "when typing pairs" $ do
      context "when the subexpressions are values" $ do
        it "produces the correct tensor type and the sum of the wirecounts of the elements" $ do
          -- ∅;∅;∅ ⊢ ((),()) ==> ((),()) ; 0
          let expr = EPair EUnit EUnit
          let expected = (TPair TUnit TUnit, Number 0)
          simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
          -- ∅;x:Qubit,y:Bit;∅ ⊢ (x,y) ==> (Qubit,Bit) ; 2
          let gamma = [("x", TWire Qubit), ("y", TWire Bit)]
          let expr = EPair (EVar "x") (EVar "y")
          let expected = (TPair (TWire Qubit) (TWire Bit), Number 2)
          simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
          -- ∅;x:Qubit,y:Bit,z:Qubit;∅ ⊢ (x,(y,z)) ==> (Qubit,(Bit,Qubit)) ; 3
          let gamma = [("x", TWire Qubit), ("y", TWire Bit), ("z", TWire Qubit)]
          let expr = EPair (EVar "x") (EPair (EVar "y") (EVar "z"))
          let expected = (TPair (TWire Qubit) (TPair (TWire Bit) (TWire Qubit)), Number 3)
          simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
    context "when typing the empty list" $ do
      it "produces an empty list type and wirecount zero if the context is empty" $ do
        -- ∅;∅;∅ ⊢ [] ==> List[0] a0 ; 0
        -- Note: type variables only appear internally for the empty list,
        -- they are not visible to the programmer
        runTypeInferenceWith emptyEnv ENil `shouldBe` Right (TList (Number 0) (TVar "a0"), Number 0)
      it "produces an empty list type and wirecount zero if the context is non-linear" $ do
        -- ∅;x:();∅ ⊢ [] ==> List[0] a0 ; 0
        let gamma = [("x", TUnit)]
        runTypeInferenceWith (makeEnv gamma []) ENil `shouldBe` Right (TList (Number 0) (TVar "a0"), Number 0)
      it "fails when there are linear resources in the environment" $ do
        -- ∅;x:Qubit;∅ ⊢ [] =/=> 
        let gamma = [("x", TWire Qubit)]
        runTypeInferenceWith (makeEnv gamma []) ENil `shouldSatisfy` isLeft
        -- ∅;∅;l:Qubit ⊢ [] =/=>
        let q = [("l", Qubit)]
        runTypeInferenceWith (makeEnv [] q) ENil `shouldSatisfy` isLeft
    context "when typing cons" $ do
      it "produces the correct list type and the wirecount of the elements times the length of the list" $ do
        -- ∅;x:Qubit;∅ ⊢ x:[] ==> List[1] Qubit ; 1
        let gamma = [("x", TWire Qubit)]
        let expr = ECons (EVar "x") ENil
        let expected = (TList (Number 1) (TWire Qubit), Number 1)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
        -- ∅;x:Qubit,y:Qubit;∅ ⊢ x:y:[] ==> List[2] (Qubit,Bit) ; 2
        let gamma = [("x", TWire Qubit), ("y", TWire Qubit)]
        let expr = ECons (EVar "x") (ECons (EVar "y") ENil)
        let expected = (TList (Number 2) (TWire Qubit), Number 2)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
        -- ∅;x:(Bit,Bit),xs:List[100] (Bit,Bit) ⊢ x:xs ==> List[101] (Bit,Bit) ; 202
        let gamma = [("x", TPair (TWire Bit) (TWire Bit)), ("xs", TList (Number 100) (TPair (TWire Bit) (TWire Bit)))]
        let expr = ECons (EVar "x") (EVar "xs")
        let expected = (TList (Number 101) (TPair (TWire Bit) (TWire Bit)), Number 202)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
      it "fails when the head is of a different type than the rest of the list" $ do
        -- ∅;x:Qubit,y:Bit;∅ ⊢ x:y:[] =/=> 
        let gamma = [("x", TWire Qubit), ("y", TWire Bit)]
        let expr = ECons (EVar "x") (ECons (EVar "y") ENil)
        runTypeInferenceWith (makeEnv gamma []) expr `shouldSatisfy` isLeft
    context "when typing abstractions" $ do
      it "produces the correct arrow type and a wirecount equal to the second annotation of the arrow" $ do
        -- ∅;∅;∅ ⊢ \x :: Qubit . x ==> Qubit ->[1,0] Qubit ; 0
        let expr = EAbs "x" (TWire Qubit) (EVar "x")
        let expected = (TArrow (TWire Qubit) (TWire Qubit) (Number 1) (Number 0), Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
        -- ∅;x:Qubit;∅ ⊢ \y :: Bit . (x,y) ==> Bit ->[2,1] (Qubit,Bit) ; 1
        let gamma = [("x", TWire Qubit)]
        let expr = EAbs "y" (TWire Bit) (EPair (EVar "x") (EVar "y"))
        let expected = (TArrow (TWire Bit) (TPair (TWire Qubit) (TWire Bit)) (Number 2) (Number 1), Number 1)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
        -- i;x:Qubit;∅ ⊢ \y :: List[i] Qubit . x:y => List[i] Qubit ->[i+1,1] List[i+1] Qubit ; 1
        let gamma = [("x", TWire Qubit)]
        let expr = EAbs "y" (TList (IndexVariable "i") (TWire Qubit)) (ECons (EVar "x") (EVar "y"))
        let expected = (TArrow (TList (IndexVariable "i") (TWire Qubit)) (TList (Plus (IndexVariable "i") (Number 1)) (TWire Qubit)) (Plus (Number 1) (IndexVariable "i")) (Number 1), Number 1)
        let theta = ["i"]
        simplify (runTypeInferenceWith (makeEnvForall theta gamma []) expr) `shouldBe` Right expected
      it "succeeds if the argument is of parameter type and is used more than once" $ do
        -- ∅;∅;∅ ⊢ \x :: () . (x,x) ==> () ->[0,0] ((),()) ; 0
        let expr = EAbs "x" TUnit (EPair (EVar "x") (EVar "x"))
        let expected = (TArrow TUnit (TPair TUnit TUnit) (Number 0) (Number 0), Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
      it "succeeds if the argument is of parameter type and is not used" $ do
        -- ∅;∅;∅ ⊢ \x :: () . () ==> () ->[0,0] () ; 0
        let expr = EAbs "x" TUnit EUnit
        let expected = (TArrow TUnit TUnit (Number 0) (Number 0), Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
      it "fails when the body uses the argument more than once" $ do
        -- ∅;∅;∅ ⊢ \x :: Qubit . (x,x) =/=>
        let expr = EAbs "x" (TWire Qubit) (EPair (EVar "x") (EVar "x"))
        runTypeInferenceWith emptyEnv expr `shouldSatisfy` isLeft
      it "fails when the body does not use the argument" $ do
        -- ∅;∅;∅ ⊢ \x :: Qubit . () =/=>
        let expr = EAbs "x" (TWire Qubit) EUnit
        runTypeInferenceWith emptyEnv expr `shouldSatisfy` isLeft
      it "succeeds in the case of shadowing, provided every linear variable is used once" $ do
        -- ∅;x:Qubit;∅ ⊢ (\x :: Qubit . x) x ==> Qubit ; 1
        let gamma = [("x", TWire Qubit)]
        let expr = EApp (EAbs "x" (TWire Qubit) (EVar "x")) (EVar "x")
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right (TWire Qubit, Number 1)
      it "fails if the formal parameter type mentions an undeclared index variable" $ do
        -- ∅;∅;∅ ⊢ \x :: List[i] Qubit . x =/=>
        let expr = EAbs "x" (TList (IndexVariable "i") (TWire Qubit)) (EVar "x")
        runTypeInferenceWith emptyEnv expr `shouldSatisfy` isLeft
    context "when typing lifted expressions" $ do
      it "produces the correct bang type and a wirecount of zero" $ do
        -- ∅;∅;∅ ⊢ lift () ==> !() ; 0
        let expr = ELift EUnit
        let expected = (TBang TUnit, Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
        -- ∅;∅;∅ ⊢ !(\x :: Qubit . x) ==> !(Qubit ->[1,0] Qubit) ; 0
      it "fails if the lifted expression consumes linear resources" $ do
        -- ∅;x:Qubit;∅ ⊢ lift x =/=> 
        let gamma = [("x", TWire Qubit)]
        let expr = ELift (EVar "x")
        runTypeInferenceWith (makeEnv gamma []) expr `shouldSatisfy` isLeft
      it "fails if the lifted expression builds a circuit" $ do
        -- ∅;∅;∅ ⊢ lift apply(QInit0,()) =/=>
        let expr = ELift (EApply (EVar "QInit0") EUnit)
        runTypeInferenceWith emptyEnv expr `shouldSatisfy` isLeft
    context "when typing boxed circuits" $ do
      it "produces the correct type and a wirecount of zero" $ do
        -- ∅;∅;∅ ⊢ ((),qinit0,a) ==> Circ[1]((),Qubit) ; 0
        let expr = ECirc UnitValue Circuit.qinit0 (Label "a")
        let expected = (TCirc (Number 1) BTUnit (BTWire Qubit), Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
        -- ∅;∅;∅ ⊢ ((a,b),cnot,(c,d)) ==> Circ[2]((Qubit,Qubit),(Qubit,Qubit)) ; 0
        let expr = ECirc (Pair (Label "a") (Label "b")) Circuit.cnot (Pair (Label "c") (Label "d"))
        let expected = (TCirc (Number 2) (BTPair (BTWire Qubit) (BTWire Qubit)) (BTPair (BTWire Qubit) (BTWire Qubit)), Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
      it "fails if the input interface is not adequate for the circuit object" $ do
        -- ∅;∅;∅ ⊢ ((),cnot,(c,d) =/=>
        let expr = ECirc UnitValue Circuit.cnot (Pair (Label "c") (Label "d"))
        runTypeInferenceWith emptyEnv expr `shouldSatisfy` isLeft
      it "fails if the output interface is not adequate for the circuit object" $ do
        -- ∅;∅;∅ ⊢ (a,hadamard,()) =/=>
        let expr = ECirc (Label "a") Circuit.hadamard UnitValue
        runTypeInferenceWith emptyEnv expr `shouldSatisfy` isLeft
    context "when typing index abstraction" $ do
      it "produces the correct forall type and the wirecount of the environment" $ do
        -- ∅;∅;∅ ⊢ @i . () ==> i ->[0,0] () ; 0
        let expr = EIAbs "i" EUnit
        let expected = (TIForall "i" TUnit (Number 0) (Number 0), Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
        -- ∅;x:Qubit;∅ ⊢ @i . \xs :: List[i] Qubit . x:xs ==> i ->[1,1] List[i] Qubit ->[i+1,1] List[i+1] Qubit ; 1
        let gamma = [("x", TWire Qubit)]
        let expr = EIAbs "i" (EAbs "xs" (TList (IndexVariable "i") (TWire Qubit)) (ECons (EVar "x") (EVar "xs")))
        let expected = (TIForall "i" (TArrow (TList (IndexVariable "i") (TWire Qubit)) (TList (Plus (IndexVariable "i") (Number 1)) (TWire Qubit)) (Plus (Number 1) (IndexVariable "i")) (Number 1)) (Number 1) (Number 1), Number 1)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
      it "fails if the index variable already exists" $ do
        -- i;∅;∅ ⊢ @i . () =/=>
        let expr = EIAbs "i" EUnit
        runTypeInferenceWith (makeEnvForall ["i"] [] []) expr `shouldSatisfy` isLeft
        -- ∅;∅;∅ ⊢ @i . (@i . ()) @i =/=>
        let expr = EIAbs "i" (EIApp (EIAbs "i" EUnit) (IndexVariable "i"))
        runTypeInferenceWith emptyEnv expr `shouldSatisfy` isLeft
    context "when typing index application" $ do
      it "produces the instantiated type of body expression and its wirecount" $ do
        -- ∅;∅;∅ ⊢ (@i . \x :: List[i] Qubit . x) @100 ==> List[100] Qubit -o[100,0] List[100] Qubit ; 0
        let expr = EIApp (EIAbs "i" (EAbs "x" (TList (IndexVariable "i") (TWire Qubit)) (EVar "x"))) (Number 100)
        let expected = (TArrow (TList (Number 100) (TWire Qubit)) (TList (Number 100) (TWire Qubit)) (Number 100) (Number 0), Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
    context "when typing fold" $ do
      it "works :)" $ do
        pending -- TODO
  describe "type inference on effectful expressions" $ do
    context "when typing pairs" $ do
      it "produces the correct tensor type and upper bound when the first element computes" $ do
        -- ∅;f:Qubit ->[2,0] Bit,x:Qubit,y:Bit;∅ ⊢ (f x, y) ==> (Bit,Bit) ; 3
        -- while f x builds something of width 2, y of width 1 flows alongside: width is 3
        let gamma = [
              ("f", TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0)),
              ("x", TWire Qubit), ("y", TWire Bit)]
        let expr = EPair (EApp (EVar "f") (EVar "x")) (EVar "y")
        let expected = (TPair (TWire Bit) (TWire Bit), Number 3)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
      it "produces the correct tensor type and upper bound when the second element computes" $ do
        -- ∅;x:Qubit,y:Qubit,g:Qubit ->[2,0] Bit;∅ ⊢ (x, g y) ==> (Qubit,Bit) ; 3
        -- while g y builds something of width 2, x of width 1 flows alongside: width is 3
        let gamma = [
              ("x", TWire Qubit), ("y", TWire Qubit),
              ("g", TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0))]
        let expr = EPair (EVar "x") (EApp (EVar "g") (EVar "y"))
        let expected = (TPair (TWire Qubit) (TWire Bit), Number 3)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
  describe "type checking (annotated terms)" $ do
    it "should work" $ do
      pending -- TODO
  describe "subsumption" $ do
    it "should work" $ do
      pending -- TODO


