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
  -- Tests for the type inference of terms that do not produce any side-effect
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
        -- ∅;∅;∅ ⊢ [] ==> List[0] () ; 0
        runTypeInferenceWith emptyEnv ENil `shouldBe` Right (TList (Number 0) TUnit, Number 0)
      it "produces an empty list type and wirecount zero if the context is non-linear" $ do
        -- ∅;x:();∅ ⊢ [] ==> List[0] a0 ; 0
        let gamma = [("x", TUnit)]
        runTypeInferenceWith (makeEnv gamma []) ENil `shouldBe` Right (TList (Number 0) TUnit, Number 0)
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
      it "succeeds if the lifted expression consumes linear resources from within its scope" $ do
        -- ∅;∅;∅ ⊢ lift (\x::Qubit . x) ==> !(Qubit ->[1,0] Qubit) ; 0
        let expr = ELift (EAbs "x" (TWire Qubit) (EVar "x"))
        let expected = (TBang (TArrow (TWire Qubit) (TWire Qubit) (Number 1) (Number 0)), Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
      it "fails if the lifted expression consumes linear resources from outside its scope" $ do
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
  describe "type inference on effectful expressions" $ do
  -- Tests for the type inference of terms that produce side-effects
  -- Either by nature or because some sub-terms are effectful
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
    context "when typing cons" $ do
      it "produces the correct list type and upper bound when the head computes" $ do
        -- ∅;f:Qubit ->[2,0] Bit,x:Qubit,y:List[3] Bit;∅ ⊢ f x:y ==> List[4] Bit ; 5
        -- while f x builds something of width 2, y of width 3 flows alongside: width is 5
        let gamma = [
              ("f", TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0)),
              ("x", TWire Qubit), ("y", TList (Number 3) (TWire Bit))]
        let expr = ECons (EApp (EVar "f") (EVar "x")) (EVar "y")
        let expected = (TList (Number 4) (TWire Bit), Number 5)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
      it "produces the correct list type and upper bound when the tail computes" $ do
        -- ∅;x:Qubit,y:Qubit,g:Qubit ->[7,0] List[2] Qubit ⊢ x:g y ==> List[3] Qubit ; 8
        -- while g y builds something of width 7, x of width 1 flows alongside: width is 8
        let gamma = [
              ("x", TWire Qubit), ("y", TWire Qubit),
              ("g", TArrow (TWire Qubit) (TList (Number 2) (TWire Qubit)) (Number 7) (Number 0))]
        let expr = ECons (EVar "x") (EApp (EVar "g") (EVar "y"))
        let expected = (TList (Number 3) (TWire Qubit), Number 8)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
    context "when typing application" $ do
      it "produces the correct type and upper bound when both function and argument are values" $ do
        -- ∅;∅;l:Qubit ⊢ (\x::Qubit.x) l ==> Qubit ; 1
        let q = [("l", Qubit)]
        let expr = EApp (EAbs "x" (TWire Qubit) (EVar "x")) (ELabel "l")
        simplify (runTypeInferenceWith (makeEnv [] q) expr) `shouldBe` Right (TWire Qubit, Number 1)
      it "produces the correct type and wirecount when the applied term computes" $ do
        -- ∅;f:Qubit ->[2,0] Qubit ->[3,1] Bit, x:Qubit, y:Qubit;∅ ⊢ (f x) y ==> Bit ; 3
        -- while f x builds something of width 2, y of width 1 flows alongside: width is 3
        let gamma = [
              ("f", TArrow (TWire Qubit) (TArrow (TWire Qubit) (TWire Bit) (Number 3) (Number 1)) (Number 2) (Number 0)),
              ("x", TWire Qubit), ("y", TWire Qubit)]
        let expr = EApp (EApp (EVar "f") (EVar "x")) (EVar "y")
        let expected = (TWire Bit, Number 3)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
      it "produces the correct type and wirecount when the argument computes" $ do
        -- ∅;f:Qubit ->[2,0] Bit, g : Qubit ->[3,1] Qubit, x:Qubit;∅ ⊢ f (g x) => Bit ; 3
        -- while g x builds something of width 3, f of width 0 flows alongside: width is 3
        let gamma = [
              ("f", TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0)),
              ("g", TArrow (TWire Qubit) (TWire Qubit) (Number 3) (Number 1)),
              ("x", TWire Qubit)]
        let expr = EApp (EVar "f") (EApp (EVar "g") (EVar "x"))
        let expected = (TWire Bit, Number 3)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
      it "produces the correct type and wirecount when both function and argument compute" $ do
        -- ∅;f:!(Qubit ->[2,0] Bit), g : Qubit ->[3,1] Qubit, x:Qubit;∅ ⊢ (force f) (g x) => Bit ; 3
        -- while g x builds something of width 3, f of width 0 flows alongside: width is 3
        let gamma = [
              ("f", TBang (TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0))),
              ("g", TArrow (TWire Qubit) (TWire Qubit) (Number 3) (Number 1)),
              ("x", TWire Qubit)]
        let expr = EApp (EForce (EVar "f")) (EApp (EVar "g") (EVar "x"))
        let expected = (TWire Bit, Number 3)
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right expected
      it "succeeds if the argument is of a subtype of the formal paramete" $ do
        -- ∅;c:Circ[1](Qubit,Qubit);∅ ⊢ (\x::Circ[2](Qubit,Qubit).x) c ==> Circ[2](Qubit,Qubit) ; 0
        let gamma = [("c", TCirc (Number 1) (BTWire Qubit) (BTWire Qubit))]
        let expr = EApp (EAbs "x" (TCirc (Number 2) (BTWire Qubit) (BTWire Qubit)) (EVar "x")) (EVar "c")
        simplify (runTypeInferenceWith (makeEnv gamma []) expr) `shouldBe` Right (TCirc (Number 2) (BTWire Qubit) (BTWire Qubit), Number 0)
      it "fails if the function is not a function type" $ do
        -- ∅;∅;l:Qubit ⊢ l (\x::Qubit.x) =/=>
        let q = [("l", Qubit)]
        let expr = EApp (ELabel "l") (EAbs "x" (TWire Qubit) (EVar "x"))
        runTypeInferenceWith (makeEnv [] q) expr `shouldSatisfy` isLeft
      it "fails if the argument is not of the expected type" $ do
        -- ∅;∅;l:Qubit ⊢ (\x::Bit.x) l =/=>
        let q = [("l", Qubit)]
        let expr = EApp (EAbs "x" (TWire Bit) (EVar "x")) (ELabel "l")
        runTypeInferenceWith (makeEnv [] q) expr `shouldSatisfy` isLeft
    context "when typing apply" $ do
      it "produces the correct type and wirecount when both function and argument are values" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the applied circuit term computes" $ do
        pending -- TODO 
      it "produces the correct type and wirecount when the circuit application argument computes" $ do
        pending -- TODO
      it "produces the correct type and wirecount when both circuit term and argument compute" $ do
        pending -- TODO
      it "fails if the applied term is not a circuit term" $ do
        pending -- TODO
      it "fails if the argument is not of the expected bundle type" $ do
        pending -- TODO
    context "when typing box" $ do
      it "produces the correct type and wirecount when the argument is a value" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the argument computes" $ do
        pending -- TODO
      it "fails if the argument is not a duplicable function" $ do
        pending -- TODO
      it "fails if the argument is not a circuit building function" $ do
        pending -- TODO
    context "when typing index application" $ do
      it "produces the instantiated type of body expression and its wirecount" $ do
        -- ∅;∅;∅ ⊢ (@i . \x :: List[i] Qubit . x) @100 ==> List[100] Qubit -o[100,0] List[100] Qubit ; 0
        let expr = EIApp (EIAbs "i" (EAbs "x" (TList (IndexVariable "i") (TWire Qubit)) (EVar "x"))) (Number 100)
        let expected = (TArrow (TList (Number 100) (TWire Qubit)) (TList (Number 100) (TWire Qubit)) (Number 100) (Number 0), Number 0)
        simplify (runTypeInferenceWith emptyEnv expr) `shouldBe` Right expected
    context "when typing let-in" $ do
      it "produces the right type and wirecount when both the bound expression and the body are values" $ do
        pending -- TODO
      it "produces the right type and wirecount when the bound expression computes" $ do
        pending -- TODO
      it "produces the right type and wirecount when the body computes" $ do
        pending -- TODO
      it "produces the right type and wirecount when both the bound expression and the body compute" $ do
        pending -- TODO
    context "when typing the destructuring let-in" $ do
      it "produces the right type and wirecount when both the bound expression and the body are values" $ do
        pending -- TODO
      it "produces the right type and wirecount when the bound expression computes" $ do
        pending -- TODO
      it "produces the right type and wirecount when the body computes" $ do
        pending -- TODO
      it "produces the right type and wirecount when both the bound expression and the body compute" $ do
        pending -- TODO
    context "when typing force" $ do
      it "produces the right type and wirecount when the argument is a value" $ do
        pending -- TODO
      it "produces the right type and wirecount when the argument computes" $ do
        pending -- TODO
    context "when typing fold" $ do
      it "produces the right type and wirecount when all the arguments are values" $ do
        pending -- TODO
      it "produces the right type and wirecount when the step function computes" $ do
        pending -- TODO
      it "produces the right type and wirecount when the starting accumulator computes" $ do
        pending -- TODO
      it "produces the right type and wirecount when the argument list computes" $ do
        pending -- TODO
      it "produces the right type and wirecount when all the arguments compute" $ do
        pending -- TODO
      -- We do not test other combinations of computing arguments so far
  describe "domination tests" $ do
  -- Testing by cases on which evaluation step consumes more resources than the others
  -- E.g. for application M N, three tests in which: M dominates the cost, N dominates, the result of the application dominates
    context "when typing pairs" $ do
      it "produces the correct type and wirecount when the first element dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the second element dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the result dominates" $ do
        pending -- TODO
    context "when typing cons" $ do
      it "produces the correct type and wirecount when the head dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the tail dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the result dominates" $ do
        pending -- TODO
    context "when typing application" $ do
      it "produces the correct type and wirecount when the function dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the argument dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the result dominates" $ do
        pending -- TODO
    context "when typing apply" $ do
      it "produces the correct type and wirecount when the circuit term dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the argument dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the result dominates" $ do
        pending -- TODO
    context "when typing fold" $ do
      it "produces the correct type and wirecount when the step function dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the starting accumulator dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the argument list dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the result dominates" $ do
        pending -- TODO
    context "when typing let-in" $ do
      it "produces the correct type and wirecount when the bound expression dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the body dominates" $ do
        pending -- TODO
    context "when typing the destructuring let-in" $ do
      it "produces the correct type and wirecount when the bound expression dominates" $ do
        pending -- TODO
      it "produces the correct type and wirecount when the body dominates" $ do
        pending -- TODO
  describe "Checking and subsumption" $ do
  -- Testing the subtyping relation and the annotation construct
    it "should work" $ do
      pending -- TODO


