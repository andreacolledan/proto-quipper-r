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
import Lang.Unified.Constant
import Lang.Unified.Derivation
    ( emptyEnv, makeEnv, makeEnvForall, TypeError, TypingEnvironment )
import Solving.CVC5 (withSolver, SolverHandle)

runInferenceForTesting :: TypingEnvironment -> Expr -> SolverHandle -> IO (Either TypeError (Type, Index))
runInferenceForTesting env expr qfh = do
  outcome <- runTypeInferenceWith env expr qfh
  case outcome of
    Left err -> return $ Left err
    Right (t, i) -> do
      t' <- simplifyType qfh t
      i' <- simplifyIndexStrong qfh i
      return $ Right (t', i')

shouldSatisfyIO :: (HasCallStack, Show a) => IO a -> (a -> Bool) -> Expectation
action `shouldSatisfyIO` p = action >>= (`shouldSatisfy` p)

shouldFailWIth :: (HasCallStack, Show a) => IO (Either TypeError a) -> (TypeError -> Bool) -> Expectation
action `shouldFailWIth` p = do
  result <- action
  case result of
    Left e -> if p e then return () else expectationFailure $ "Expectation failed on " ++ show e
    Right x -> expectationFailure $ "Expected the action to fail, but it returned " ++ show x

-- -- The datatype of errors that can occur during a derivation
-- data TypeError
--   = WireTypingError WireTypingError
--   | UnboundVariable VariableId [Expr]
--   | UnboundIndexVariable IndexVariableId [Expr]
--   | UnexpectedType Expr Type Type [Expr]
--   | UnexpectedIndex Index Index [Expr]
--   | UnexpectedWidthAnnotation Expr Index Index [Expr]
--   | ExpectedBundleType Expr Type [Expr]
--   | CannotSynthesizeType Expr [Expr]
--   | -- Linearity errors
--     UnusedLinearVariable VariableId [Expr]
--   | OverusedLinearVariable VariableId [Expr]
--   | LiftedLinearVariable VariableId [Expr]
--   | -- Boxed circuit errors
--     MismatchedInputInterface Circuit LabelContext Bundle [Expr]
--   | MismatchedOutputInterface Circuit LabelContext Bundle [Expr]
--   | -- Box errors
--     UnboxableType Expr Type [Expr]
--   | -- Fold errors
--     UnfoldableStepfunction Expr Type [Expr]
--   | UnfoldableAccumulator Expr Type [Expr]
--   | UnfoldableArg Expr Type [Expr]
--   | -- Other
--     ShadowedIndexVariable IndexVariableId [Expr]
--   | UnexpectedEmptyList Expr Type [Expr]
--   deriving (Eq)

spec :: Spec
spec = around (withSolver "test-inference") $ do
    describe "type inference on values" $ do
    -- Tests for the type inference of terms that do not produce any side-effect
      context "when typing the unit value" $ do
        it "produces the unit type if the context is empty" $ \qfh -> do
          -- ∅;∅;∅ ⊢ () ==> () ; 0
          runInferenceForTesting emptyEnv EUnit qfh `shouldReturn` Right (TUnit, Number 0)
        it "produces the unit type if the context is non-linear" $ \qfh -> do
          -- ∅;x:(),y:Circ[1](Qubit,Qubit);∅ ⊢ () =/=> () ; 0
          let gamma = [("x", TUnit), ("y", TCirc (Number 1) (BTWire Qubit) (BTWire Qubit))]
          runInferenceForTesting (makeEnv gamma []) EUnit qfh `shouldReturn` Right (TUnit, Number 0)
        it "fails when there are linear resources in the environment" $ \qfh -> do
          -- ∅;x:Qubit;∅ ⊢ () =/=>
          let gamma = [("x", TWire Qubit)]
          runInferenceForTesting (makeEnv gamma []) EUnit qfh `shouldSatisfyIO` isLeft
          -- ∅;∅;x:Qubit ⊢ () =/=>
          let q = [("x", Qubit)]
          runInferenceForTesting (makeEnv [] q) EUnit qfh `shouldSatisfyIO` isLeft
      context "when typing labels" $ do
        it "produces the type of the label if the rest of the context is empty" $ \qfh -> do
          -- ∅;∅;l:Qubit ⊢ l ==> Qubit ; 1
          let q = [("l", Qubit)]
          runInferenceForTesting (makeEnv [] q) (ELabel "l") qfh `shouldReturn` Right (TWire Qubit, Number 1)
          -- ∅;∅;l:Bit ⊢ l ==> Bit ; 1
          let b = [("l", Bit)]
          runInferenceForTesting (makeEnv [] b) (ELabel "l") qfh `shouldReturn` Right (TWire Bit, Number 1)
        it "produces the type of the label if the rest of the context is nonlinear" $ \qfh -> do
          -- ∅;x:();l:Qubit ⊢ l ==> Qubit ; 1
          let gamma = [("x", TUnit)]
          let q = [("l", Qubit)]
          runInferenceForTesting (makeEnv gamma q) (ELabel "l") qfh `shouldReturn` Right (TWire Qubit, Number 1)
        it "fails when there are other linear resources in the environment" $ \qfh -> do
          -- ∅;x:Qubit;l:Qubit ⊢ l =/=>
          let gamma = [("x", TWire Qubit)]
          let q = [("l", Qubit)]
          runInferenceForTesting (makeEnv gamma q) (ELabel "l") qfh `shouldSatisfyIO` isLeft
          -- ∅;∅;x:Qubit,l:Qubit ⊢ l =/=>
          let q = [("x", Qubit), ("l", Qubit)]
          runInferenceForTesting (makeEnv [] q) (ELabel "l") qfh `shouldSatisfyIO` isLeft
      context "when typing variables" $ do
        it "produces the type of the variable if the rest of the context is empty" $ \qfh -> do
          -- ∅;x:Qubit;∅ ⊢ x ==> Qubit ; 1
          let gamma = [("x", TWire Qubit)]
          runInferenceForTesting (makeEnv gamma []) (EVar "x") qfh `shouldReturn` Right (TWire Qubit, Number 1)
        it "produces the type of the variable if the rest of the context is nonlinear" $ \qfh -> do
          -- ∅;x:(),y:Qubit;∅ ⊢ y ==> Qubit ; 1
          let gamma = [("x", TUnit), ("y", TWire Qubit)]
          runInferenceForTesting (makeEnv gamma []) (EVar "y") qfh `shouldReturn` Right (TWire Qubit, Number 1)
        it "fails when there are other linear resources in the environment" $ \qfh -> do
          -- ∅;x:Qubit,y:Qubit;∅ ⊢ y =/=>
          let gamma = [("x", TWire Qubit), ("y", TWire Qubit)]
          runInferenceForTesting (makeEnv gamma []) (EVar "y") qfh `shouldSatisfyIO` isLeft
      context "when typing pairs" $ do
        it "produces the correct tensor type and the sum of the wirecounts of the elements" $ \qfh -> do
          -- ∅;∅;∅ ⊢ ((),()) ==> ((),()) ; 0
          let expr = EPair EUnit EUnit
          let expected = (TPair TUnit TUnit, Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
          -- ∅;x:Qubit,y:Bit;∅ ⊢ (x,y) ==> (Qubit,Bit) ; 2
          let gamma = [("x", TWire Qubit), ("y", TWire Bit)]
          let expr = EPair (EVar "x") (EVar "y")
          let expected = (TPair (TWire Qubit) (TWire Bit), Number 2)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
          -- ∅;x:Qubit,y:Bit,z:Qubit;∅ ⊢ (x,(y,z)) ==> (Qubit,(Bit,Qubit)) ; 3
          let gamma = [("x", TWire Qubit), ("y", TWire Bit), ("z", TWire Qubit)]
          let expr = EPair (EVar "x") (EPair (EVar "y") (EVar "z"))
          let expected = (TPair (TWire Qubit) (TPair (TWire Bit) (TWire Qubit)), Number 3)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
      context "when typing the empty list" $ do
        it "produces an empty list type and wirecount zero if the context is empty" $ \qfh -> do
          -- ∅;∅;∅ ⊢ [] :: List[0] () ==> List[0] () ; 0
          runInferenceForTesting emptyEnv (EAnno (ENil Nothing) (TList (Number 0) TUnit)) qfh `shouldReturn` Right (TList (Number 0) TUnit, Number 0)
        it "produces an empty list type and wirecount zero if the context is non-linear" $ \qfh -> do
          -- ∅;x:();∅ ⊢ [] :: List[0] () ==> List[0] () ; 0
          let gamma = [("x", TUnit)]
          runInferenceForTesting (makeEnv gamma []) (EAnno (ENil Nothing) (TList (Number 0) TUnit)) qfh `shouldReturn` Right (TList (Number 0) TUnit, Number 0)
        it "fails when there are linear resources in the environment" $ \qfh -> do
          -- ∅;x:Qubit;∅ ⊢ [] :: List[0] () =/=> 
          let gamma = [("x", TWire Qubit)]
          runInferenceForTesting (makeEnv gamma []) (EAnno (ENil Nothing) (TList (Number 0) TUnit)) qfh `shouldSatisfyIO` isLeft
          -- ∅;∅;l:Qubit ⊢ [] :: List[0] () =/=>
          let q = [("l", Qubit)]
          runInferenceForTesting (makeEnv [] q) (EAnno (ENil Nothing) (TList (Number 0) TUnit)) qfh `shouldSatisfyIO` isLeft
        it "fails when the parameter type is unconstrained" $ \qfh -> do
          -- ∅;∅;∅ ⊢ [] =/=>
          runInferenceForTesting emptyEnv (ENil Nothing) qfh `shouldSatisfyIO` isLeft
      context "when typing cons" $ do
        it "produces the correct list type and the wirecount of the elements times the length of the list" $ \qfh -> do
          -- ∅;x:Qubit;∅ ⊢ x:[] ==> List[1] Qubit ; 1
          let gamma = [("x", TWire Qubit)]
          let expr = ECons (EVar "x") (ENil Nothing)
          let expected = (TList (Number 1) (TWire Qubit), Number 1)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
          -- ∅;x:Qubit,y:Qubit;∅ ⊢ x:y:[] ==> List[2] (Qubit,Bit) ; 2
          let gamma = [("x", TWire Qubit), ("y", TWire Qubit)]
          let expr = ECons (EVar "x") (ECons (EVar "y") (ENil Nothing))
          let expected = (TList (Number 2) (TWire Qubit), Number 2)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
          -- ∅;x:(Bit,Bit),xs:List[100] (Bit,Bit) ⊢ x:xs ==> List[101] (Bit,Bit) ; 202
          let gamma = [("x", TPair (TWire Bit) (TWire Bit)), ("xs", TList (Number 100) (TPair (TWire Bit) (TWire Bit)))]
          let expr = ECons (EVar "x") (EVar "xs")
          let expected = (TList (Number 101) (TPair (TWire Bit) (TWire Bit)), Number 202)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "fails when the head is of a different type than the rest of the list" $ \qfh -> do
          -- ∅;x:Qubit,y:Bit;∅ ⊢ x:y:[] =/=> 
          let gamma = [("x", TWire Qubit), ("y", TWire Bit)]
          let expr = ECons (EVar "x") (ECons (EVar "y") (ENil Nothing))
          runInferenceForTesting (makeEnv gamma []) expr qfh `shouldSatisfyIO` isLeft
      context "when typing abstractions" $ do
        it "produces the correct arrow type and a wirecount equal to the second annotation of the arrow" $ \qfh -> do
          -- ∅;∅;∅ ⊢ \x :: Qubit . x ==> Qubit ->[1,0] Qubit ; 0
          let expr = EAbs "x" (TWire Qubit) (EVar "x")
          let expected = (TArrow (TWire Qubit) (TWire Qubit) (Number 1) (Number 0), Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
          -- ∅;x:Qubit;∅ ⊢ \y :: Bit . (x,y) ==> Bit ->[2,1] (Qubit,Bit) ; 1
          let gamma = [("x", TWire Qubit)]
          let expr = EAbs "y" (TWire Bit) (EPair (EVar "x") (EVar "y"))
          let expected = (TArrow (TWire Bit) (TPair (TWire Qubit) (TWire Bit)) (Number 2) (Number 1), Number 1)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
          -- i;x:Qubit;∅ ⊢ \y :: List[i] Qubit . x:y => List[i] Qubit ->[i+1,1] List[i+1] Qubit ; 1
          let gamma = [("x", TWire Qubit)]
          let expr = EAbs "y" (TList (IndexVariable "i") (TWire Qubit)) (ECons (EVar "x") (EVar "y"))
          let expected = (TArrow (TList (IndexVariable "i") (TWire Qubit)) (TList (Plus (IndexVariable "i") (Number 1)) (TWire Qubit)) (Plus (Number 1) (IndexVariable "i")) (Number 1), Number 1)
          let theta = ["i"]
          runInferenceForTesting  (makeEnvForall theta gamma []) expr qfh `shouldReturn` Right expected
        it "succeeds if the argument is of parameter type and is used more than once" $ \qfh -> do
          -- ∅;∅;∅ ⊢ \x :: () . (x,x) ==> () ->[0,0] ((),()) ; 0
          let expr = EAbs "x" TUnit (EPair (EVar "x") (EVar "x"))
          let expected = (TArrow TUnit (TPair TUnit TUnit) (Number 0) (Number 0), Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "succeeds if the argument is of parameter type and is not used" $ \qfh -> do
          -- ∅;∅;∅ ⊢ \x :: () . () ==> () ->[0,0] () ; 0
          let expr = EAbs "x" TUnit EUnit
          let expected = (TArrow TUnit TUnit (Number 0) (Number 0), Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "fails when the body uses the argument more than once" $ \qfh -> do
          -- ∅;∅;∅ ⊢ \x :: Qubit . (x,x) =/=>
          let expr = EAbs "x" (TWire Qubit) (EPair (EVar "x") (EVar "x"))
          runInferenceForTesting emptyEnv expr qfh `shouldSatisfyIO` isLeft
        it "fails when the body does not use the argument" $ \qfh -> do
          -- ∅;∅;∅ ⊢ \x :: Qubit . () =/=>
          let expr = EAbs "x" (TWire Qubit) EUnit
          runInferenceForTesting emptyEnv expr qfh `shouldSatisfyIO` isLeft
        it "succeeds in the case of shadowing, provided every linear variable is used once" $ \qfh -> do
          -- ∅;x:Qubit;∅ ⊢ (\x :: Qubit . x) x ==> Qubit ; 1
          let gamma = [("x", TWire Qubit)]
          let expr = EApp (EAbs "x" (TWire Qubit) (EVar "x")) (EVar "x")
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right (TWire Qubit, Number 1)
        it "fails if the formal parameter type mentions an undeclared index variable" $ \qfh -> do
          -- ∅;∅;∅ ⊢ \x :: List[i] Qubit . x =/=>
          let expr = EAbs "x" (TList (IndexVariable "i") (TWire Qubit)) (EVar "x")
          runInferenceForTesting emptyEnv expr qfh `shouldSatisfyIO` isLeft
      context "when typing lifted expressions" $ do
        it "produces the correct bang type and a wirecount of zero" $ \qfh -> do
          -- ∅;∅;∅ ⊢ lift () ==> !() ; 0
          let expr = ELift EUnit
          let expected = (TBang TUnit, Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
          -- ∅;∅;∅ ⊢ !(\x :: Qubit . x) ==> !(Qubit ->[1,0] Qubit) ; 0
        it "succeeds if the lifted expression consumes linear resources from within its scope" $ \qfh -> do
          -- ∅;∅;∅ ⊢ lift (\x::Qubit . x) ==> !(Qubit ->[1,0] Qubit) ; 0
          let expr = ELift (EAbs "x" (TWire Qubit) (EVar "x"))
          let expected = (TBang (TArrow (TWire Qubit) (TWire Qubit) (Number 1) (Number 0)), Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "fails if the lifted expression consumes linear resources from outside its scope" $ \qfh -> do
          -- ∅;x:Qubit;∅ ⊢ lift x =/=> 
          let gamma = [("x", TWire Qubit)]
          let expr = ELift (EVar "x")
          runInferenceForTesting (makeEnv gamma []) expr qfh `shouldSatisfyIO` isLeft
        it "fails if the lifted expression builds a circuit" $ \qfh -> do
          -- ∅;∅;∅ ⊢ lift apply(QInit0,()) =/=>
          let expr = ELift (EApply (EVar "QInit0") EUnit)
          runInferenceForTesting emptyEnv expr qfh `shouldSatisfyIO` isLeft
      context "when typing boxed circuits" $ do
        it "produces the correct type and a wirecount of zero" $ \qfh -> do
          -- ∅;∅;∅ ⊢ ((),qinit0,a) ==> Circ[1]((),Qubit) ; 0
          let expr = ECirc UnitValue Circuit.qinit0 (Label "a")
          let expected = (TCirc (Number 1) BTUnit (BTWire Qubit), Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
          -- ∅;∅;∅ ⊢ ((a,b),cnot,(c,d)) ==> Circ[2]((Qubit,Qubit),(Qubit,Qubit)) ; 0
          let expr = ECirc (Pair (Label "a") (Label "b")) Circuit.cnot (Pair (Label "c") (Label "d"))
          let expected = (TCirc (Number 2) (BTPair (BTWire Qubit) (BTWire Qubit)) (BTPair (BTWire Qubit) (BTWire Qubit)), Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "fails if the input interface is not adequate for the circuit object" $ \qfh -> do
          -- ∅;∅;∅ ⊢ ((),cnot,(c,d) =/=>
          let expr = ECirc UnitValue Circuit.cnot (Pair (Label "c") (Label "d"))
          runInferenceForTesting emptyEnv expr qfh `shouldSatisfyIO` isLeft
        it "fails if the output interface is not adequate for the circuit object" $ \qfh -> do
          -- ∅;∅;∅ ⊢ (a,hadamard,()) =/=>
          let expr = ECirc (Label "a") Circuit.hadamard UnitValue
          runInferenceForTesting emptyEnv expr qfh `shouldSatisfyIO` isLeft
      context "when typing index abstraction" $ do
        it "produces the correct forall type and the wirecount of the environment" $ \qfh -> do
          -- ∅;∅;∅ ⊢ @i . () ==> i ->[0,0] () ; 0
          let expr = EIAbs "i" EUnit
          let expected = (TIForall "i" TUnit (Number 0) (Number 0), Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
          -- ∅;x:Qubit;∅ ⊢ @i . \xs :: List[i] Qubit . x:xs ==> i ->[1,1] List[i] Qubit ->[i+1,1] List[i+1] Qubit ; 1
          let gamma = [("x", TWire Qubit)]
          let expr = EIAbs "i" (EAbs "xs" (TList (IndexVariable "i") (TWire Qubit)) (ECons (EVar "x") (EVar "xs")))
          let expected = (TIForall "i" (TArrow (TList (IndexVariable "i") (TWire Qubit)) (TList (Plus (IndexVariable "i") (Number 1)) (TWire Qubit)) (Plus (Number 1) (IndexVariable "i")) (Number 1)) (Number 1) (Number 1), Number 1)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "fails if the index variable already exists" $ \qfh -> do
          -- i;∅;∅ ⊢ @i . () =/=>
          let expr = EIAbs "i" EUnit
          runInferenceForTesting (makeEnvForall ["i"] [] []) expr qfh `shouldSatisfyIO` isLeft
          -- ∅;∅;∅ ⊢ @i . (@i . ()) @i =/=>
          let expr = EIAbs "i" (EIApp (EIAbs "i" EUnit) (IndexVariable "i"))
          runInferenceForTesting emptyEnv expr qfh `shouldSatisfyIO` isLeft
    describe "type inference on effectful expressions" $ do
    -- Tests for the type inference of terms that produce side-effects
    -- Either by nature or because some sub-terms are effectful
      context "when typing pairs" $ do
        it "produces the correct tensor type and upper bound when the first element computes" $ \qfh -> do
          -- ∅;f:Qubit ->[2,0] Bit,x:Qubit,y:Bit;∅ ⊢ (f x, y) ==> (Bit,Bit) ; 3
          -- while f x builds something of width 2, y of width 1 flows alongside: width is 3
          let gamma = [
                ("f", TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0)),
                ("x", TWire Qubit), ("y", TWire Bit)]
          let expr = EPair (EApp (EVar "f") (EVar "x")) (EVar "y")
          let expected = (TPair (TWire Bit) (TWire Bit), Number 3)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "produces the correct tensor type and upper bound when the second element computes" $ \qfh -> do
          -- ∅;x:Qubit,y:Qubit,g:Qubit ->[2,0] Bit;∅ ⊢ (x, g y) ==> (Qubit,Bit) ; 3
          -- while g y builds something of width 2, x of width 1 flows alongside: width is 3
          let gamma = [
                ("x", TWire Qubit), ("y", TWire Qubit),
                ("g", TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0))]
          let expr = EPair (EVar "x") (EApp (EVar "g") (EVar "y"))
          let expected = (TPair (TWire Qubit) (TWire Bit), Number 3)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
      context "when typing cons" $ do
        it "produces the correct list type and upper bound when the head computes" $ \qfh -> do
          -- ∅;f:Qubit ->[2,0] Bit,x:Qubit,y:List[3] Bit;∅ ⊢ f x:y ==> List[4] Bit ; 5
          -- while f x builds something of width 2, y of width 3 flows alongside: width is 5
          let gamma = [
                ("f", TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0)),
                ("x", TWire Qubit), ("y", TList (Number 3) (TWire Bit))]
          let expr = ECons (EApp (EVar "f") (EVar "x")) (EVar "y")
          let expected = (TList (Number 4) (TWire Bit), Number 5)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "produces the correct list type and upper bound when the tail computes" $ \qfh -> do
          -- ∅;x:Qubit,y:Qubit,g:Qubit ->[7,0] List[2] Qubit ⊢ x:g y ==> List[3] Qubit ; 8
          -- while g y builds something of width 7, x of width 1 flows alongside: width is 8
          let gamma = [
                ("x", TWire Qubit), ("y", TWire Qubit),
                ("g", TArrow (TWire Qubit) (TList (Number 2) (TWire Qubit)) (Number 7) (Number 0))]
          let expr = ECons (EVar "x") (EApp (EVar "g") (EVar "y"))
          let expected = (TList (Number 3) (TWire Qubit), Number 8)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
      context "when typing application" $ do
        it "produces the correct type and upper bound when both function and argument are values" $ \qfh -> do
          -- ∅;∅;l:Qubit ⊢ (\x::Qubit.x) l ==> Qubit ; 1
          let q = [("l", Qubit)]
          let expr = EApp (EAbs "x" (TWire Qubit) (EVar "x")) (ELabel "l")
          runInferenceForTesting  (makeEnv [] q) expr qfh `shouldReturn` Right (TWire Qubit, Number 1)
        it "produces the correct type and wirecount when the applied term computes" $ \qfh -> do
          -- ∅;f:Qubit ->[2,0] Qubit ->[3,1] Bit, x:Qubit, y:Qubit;∅ ⊢ (f x) y ==> Bit ; 3
          -- while f x builds something of width 2, y of width 1 flows alongside: width is 3
          let gamma = [
                ("f", TArrow (TWire Qubit) (TArrow (TWire Qubit) (TWire Bit) (Number 3) (Number 1)) (Number 2) (Number 0)),
                ("x", TWire Qubit), ("y", TWire Qubit)]
          let expr = EApp (EApp (EVar "f") (EVar "x")) (EVar "y")
          let expected = (TWire Bit, Number 3)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "produces the correct type and wirecount when the argument computes" $ \qfh -> do
          -- ∅;f:Qubit ->[2,0] Bit, g : Qubit ->[3,1] Qubit, x:Qubit;∅ ⊢ f (g x) => Bit ; 3
          -- while g x builds something of width 3, f of width 0 flows alongside: width is 3
          let gamma = [
                ("f", TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0)),
                ("g", TArrow (TWire Qubit) (TWire Qubit) (Number 3) (Number 1)),
                ("x", TWire Qubit)]
          let expr = EApp (EVar "f") (EApp (EVar "g") (EVar "x"))
          let expected = (TWire Bit, Number 3)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "produces the correct type and wirecount when both function and argument compute" $ \qfh -> do
          -- ∅;f:!(Qubit ->[2,0] Bit), g : Qubit ->[3,1] Qubit, x:Qubit;∅ ⊢ (force f) (g x) => Bit ; 3
          -- while g x builds something of width 3, f of width 0 flows alongside: width is 3
          let gamma = [
                ("f", TBang (TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0))),
                ("g", TArrow (TWire Qubit) (TWire Qubit) (Number 3) (Number 1)),
                ("x", TWire Qubit)]
          let expr = EApp (EForce (EVar "f")) (EApp (EVar "g") (EVar "x"))
          let expected = (TWire Bit, Number 3)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "succeeds if the argument is of a subtype of the formal paramete" $ \qfh -> do
          -- ∅;c:Circ[1](Qubit,Qubit);∅ ⊢ (\x::Circ[2](Qubit,Qubit).x) c ==> Circ[2](Qubit,Qubit) ; 0
          let gamma = [("c", TCirc (Number 1) (BTWire Qubit) (BTWire Qubit))]
          let expr = EApp (EAbs "x" (TCirc (Number 2) (BTWire Qubit) (BTWire Qubit)) (EVar "x")) (EVar "c")
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right (TCirc (Number 2) (BTWire Qubit) (BTWire Qubit), Number 0)
        it "fails if the function is not a function type" $ \qfh -> do
          -- ∅;∅;l:Qubit ⊢ l (\x::Qubit.x) =/=>
          let q = [("l", Qubit)]
          let expr = EApp (ELabel "l") (EAbs "x" (TWire Qubit) (EVar "x"))
          runInferenceForTesting (makeEnv [] q) expr qfh `shouldSatisfyIO` isLeft
        it "fails if the argument is not of the expected type" $ \qfh -> do
          -- ∅;∅;l:Qubit ⊢ (\x::Bit.x) l =/=>
          let q = [("l", Qubit)]
          let expr = EApp (EAbs "x" (TWire Bit) (EVar "x")) (ELabel "l")
          runInferenceForTesting (makeEnv [] q) expr qfh `shouldSatisfyIO` isLeft
      context "when typing apply" $ do
        it "produces the correct type and wirecount when both function and argument are values" $ \qfh -> do
          -- ∅;∅;∅ ⊢ apply(QInit0,()) ==> Qubit ; 1
          let expr = EApply (EConst QInit0) EUnit
          let expected = (TWire Qubit, Number 1)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "produces the correct type and wirecount when the applied circuit term computes" $ \qfh -> do
          -- ∅;f:!(Qubit -o[2,0] Qubit);q:Qubit;∅ ⊢ apply(box::Qubit f, q) ==> Qubit ; 2
          let gamma = [
                ("f", TBang (TArrow (TWire Qubit) (TWire Qubit) (Number 2) (Number 0))),
                ("q", TWire Qubit)]
          let expr = EApply (EBox (BTWire Qubit) (EVar "f")) (EVar "q")
          let expected = (TWire Qubit, Number 2)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "produces the correct type and wirecount when the circuit application argument computes" $ \qfh -> do
          -- ∅;rev:!(i ->[0,0] List[i] Qubit -o[i,0] List[i] Qubit),c:Circ[16](List[8] Qubit, List[8] Qubit), qs:List[8] Qubit;∅ ⊢ apply(c, (force rev) @8 qs) ==> List[8] Qubit ; 16
          let gamma = [
                ("rev", TBang (TIForall "i" (TArrow (TList (IndexVariable "i") (TWire Qubit)) (TList (IndexVariable "i") (TWire Qubit)) (IndexVariable "i") (Number 0)) (Number 0) (Number 0))),
                ("c", TCirc (Number 16) (BTList (Number 8) (BTWire Qubit)) (BTList (Number 8) (BTWire Qubit))),
                ("qs", TList (Number 8) (TWire Qubit))]
          let expr = EApply (EVar "c") (EApp (EIApp (EForce (EVar "rev")) (Number 8)) (EVar "qs"))
          let expected = (TList (Number 8) (TWire Qubit), Number 16)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "produces the correct type and wirecount when both circuit term and argument compute" $ \qfh -> do
          -- ∅;f:!(Qubit -o[2,0] Qubit),q:Qubit,g:Qubit ->[2,0] Qubit;∅ ⊢ apply(box::Qubit f, g q) ==> Qubit ; 2
          let gamma = [
                ("f", TBang (TArrow (TWire Qubit) (TWire Qubit) (Number 2) (Number 0))),
                ("q", TWire Qubit),
                ("g", TArrow (TWire Qubit) (TWire Qubit) (Number 2) (Number 0))]
          let expr = EApply (EBox (BTWire Qubit) (EVar "f")) (EApp (EVar "g") (EVar "q"))
          let expected = (TWire Qubit, Number 2)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "fails if the applied term is not a circuit term" $ \qfh -> do
          -- ∅;f:Qubit ->[2,0] Qubit,q:Qubit;∅ ⊢ apply(f,q) =/=>
          let gamma = [
                ("f", TArrow (TWire Qubit) (TWire Qubit) (Number 2) (Number 0)),
                ("q", TWire Qubit)]
          let expr = EApply (EVar "f") (EVar "q")
          runInferenceForTesting (makeEnv gamma []) expr qfh `shouldSatisfyIO` isLeft
        it "fails if the argument is not of the expected bundle type" $ \qfh -> do
          -- ∅;b:Bit;∅ ⊢ apply(QInit0,b) =/=>
          let gamma = [("b", TWire Bit)]
          let expr = EApply (EConst QInit0) (EVar "b")
          runInferenceForTesting (makeEnv gamma []) expr qfh `shouldSatisfyIO` isLeft
      context "when typing box" $ do
        it "produces the correct type and wirecount when the argument is a value" $ \qfh -> do
          -- ∅;f:!(Qubit -o[2,0] Qubit);∅ ⊢ box::Qubit f ==> Circ[2](Qubit,Qubit) ; 0
          let gamma = [("f", TBang (TArrow (TWire Qubit) (TWire Qubit) (Number 2) (Number 0)))]
          let expr = EBox (BTWire Qubit) (EVar "f")
          let expected = (TCirc (Number 2) (BTWire Qubit) (BTWire Qubit), Number 0)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "produces the correct type and wirecount when the argument computes" $ \qfh -> do
          -- ∅;f:() -o[3,0] !(Qubit -o[2,0] Bit);∅ ⊢ box::Qubit (f ()) ==> Circ[2](Qubit,Bit) ; 3
          let gamma = [("f", TArrow TUnit (TBang (TArrow (TWire Qubit) (TWire Bit) (Number 2) (Number 0))) (Number 3) (Number 0))]
          let expr = EBox (BTWire Qubit) (EApp (EVar "f") EUnit)
          let expected = (TCirc (Number 2) (BTWire Qubit) (BTWire Bit), Number 3)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "fails if the argument is not a duplicable function" $ \qfh -> do
          -- ∅;f:Qubit ->[2,0] Qubit;∅ ⊢ box::Qubit f =/=>
          let gamma = [("f", TArrow (TWire Qubit) (TWire Qubit) (Number 2) (Number 0))]
          let expr = EBox (BTWire Qubit) (EVar "f")
          runInferenceForTesting (makeEnv gamma []) expr qfh `shouldSatisfyIO` isLeft
        it "fails if the argument is not a circuit building function" $ \qfh -> do
          -- ∅;f:!(Qubit -o[2,0] Circ[2](Qubit,Qubit));∅ ⊢ box::Qubit f =/=>
          let gamma = [("f", TBang (TArrow (TWire Qubit) (TCirc (Number 2) (BTWire Qubit) (BTWire Qubit)) (Number 2) (Number 0)))]
          let expr = EBox (BTWire Qubit) (EVar "f")
          runInferenceForTesting (makeEnv gamma []) expr qfh `shouldSatisfyIO` isLeft
      context "when typing index application" $ do
        it "produces the instantiated type of body expression and its wirecount" $ \qfh -> do
          -- ∅;∅;∅ ⊢ (@i . \x :: List[i] Qubit . x) @100 ==> List[100] Qubit -o[100,0] List[100] Qubit ; 0
          let expr = EIApp (EIAbs "i" (EAbs "x" (TList (IndexVariable "i") (TWire Qubit)) (EVar "x"))) (Number 100)
          let expected = (TArrow (TList (Number 100) (TWire Qubit)) (TList (Number 100) (TWire Qubit)) (Number 100) (Number 0), Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
      context "when typing let-in" $ do
        it "produces the right type and wirecount when both the bound expression and the body are values" $ \qfh -> do
          -- ∅;∅;∅ ⊢ let x = () in (x,x) ==> ((),()) ; 0
          let expr = ELet "x" EUnit (EPair (EVar "x") (EVar "x"))
          let expected = (TPair TUnit TUnit, Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "produces the right type and wirecount when the bound expression computes" $ \qfh -> do
          -- ∅;∅;∅ ⊢ let x = apply(QInit0,()) in (x,()) ==> (Qubit,()) ; 1
          let expr = ELet "x" (EApply (EConst QInit0) EUnit) (EPair (EVar "x") EUnit)
          let expected = (TPair (TWire Qubit) TUnit, Number 1)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "produces the right type and wirecount when the body computes" $ \qfh -> do
          -- ∅;∅;∅ ⊢ let x = () in apply(QInit0,x) ==> Qubit ; 1
          let expr = ELet "x" EUnit (EApply (EConst QInit0) (EVar "x"))
          let expected = (TWire Qubit, Number 1)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "produces the right type and wirecount when both the bound expression and the body compute" $ \qfh -> do
          -- ∅;∅;∅ ⊢ let x = apply(QInit0,()) in apply(Hadamard,x) ==> Qubit ; 1
          let expr = ELet "x" (EApply (EConst QInit0) EUnit) (EApply (EConst Hadamard) (EVar "x"))
          let expected = (TWire Qubit, Number 1)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
      context "when typing the destructuring let-in" $ do
        it "produces the right type and wirecount when both the bound expression and the body are values" $ \qfh -> do
          -- ∅;∅;∅ ⊢ let (x,y) = ((),()) in (y,x) ==> ((),()) ; 0
          let expr = EDest "x" "y" (EPair EUnit EUnit) (EPair (EVar "y") (EVar "x"))
          let expected = (TPair TUnit TUnit, Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "produces the right type and wirecount when the bound expression computes" $ \qfh -> do
          -- ∅;initTwo:() -o[2,0] (Qubit,Qubit);∅ ⊢ let (x,y) = initTwo () in (y,x) ==> (Qubit,Qubit) ; 2
          let gamma = [("initTwo", TArrow TUnit (TPair (TWire Qubit) (TWire Qubit)) (Number 2) (Number 0))]
          let expr = EDest "x" "y" (EApp (EVar "initTwo") EUnit) (EPair (EVar "y") (EVar "x"))
          let expected = (TPair (TWire Qubit) (TWire Qubit), Number 2)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "produces the right type and wirecount when the body computes" $ \qfh -> do
          -- ∅;initTwo:() -o[2,0] (Qubit,Qubit);∅ ⊢ let (x,y) = ((),()) in initTwo y ==> (Qubit,Qubit) ; 2
          let gamma = [("initTwo", TArrow TUnit (TPair (TWire Qubit) (TWire Qubit)) (Number 2) (Number 0))]
          let expr = EDest "x" "y" (EPair EUnit EUnit) (EApp (EVar "initTwo") (EVar "y"))
          let expected = (TPair (TWire Qubit) (TWire Qubit), Number 2)  
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "produces the right type and wirecount when both the bound expression and the body compute" $ \qfh -> do
          -- ∅;initTwo:() -o[2,0] (Qubit,Qubit);∅ ⊢ let (x,y) = initTwo () in apply(CNot,(y,x)) ==> (Qubit,Qubit) ; 2
          let gamma = [("initTwo", TArrow TUnit (TPair (TWire Qubit) (TWire Qubit)) (Number 2) (Number 0))]
          let expr = EDest "x" "y" (EApp (EVar "initTwo") EUnit) (EApply (EConst CNot) (EPair (EVar "y") (EVar "x")))
          let expected = (TPair (TWire Qubit) (TWire Qubit), Number 2)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "fails when the bound expression is not of tensor type" $ \qfh -> do
          -- ∅;∅;∅ ⊢ let (x,y) = apply(QInit0,()) in (y,x) =/=>
          let expr = EDest "x" "y" (EApply (EConst QInit0) EUnit) (EPair (EVar "y") (EVar "x"))
          runInferenceForTesting emptyEnv expr qfh `shouldSatisfyIO` isLeft
      context "when typing force" $ do
        it "produces the right type and wirecount when the argument is a value" $ \qfh -> do
          -- ∅;∅;∅ ⊢ force (lift \x::Qubit . x) ==> Qubit -o[1,0] Qubit ; 0
          let expr = EForce (ELift (EAbs "x" (TWire Qubit) (EVar "x")))
          let expected = (TArrow (TWire Qubit) (TWire Qubit) (Number 1) (Number 0), Number 0)
          runInferenceForTesting  emptyEnv expr qfh `shouldReturn` Right expected
        it "produces the right type and wirecount when the argument computes" $ \qfh -> do
          -- ∅;f:i ->[1,0] !(Qubit -o[i,0] Qubit);∅ ⊢ force (f @5) ==> Qubit -o[5,0] Qubit ; 1
          let gamma = [("f", TIForall "i" (TBang (TArrow (TWire Qubit) (TWire Qubit) (IndexVariable "i") (Number 0))) (Number 1) (Number 0))]
          let expr = EForce (EIApp (EVar "f") (Number 5))
          let expected = (TArrow (TWire Qubit) (TWire Qubit) (Number 5) (Number 0), Number 1)
          runInferenceForTesting  (makeEnv gamma []) expr qfh `shouldReturn` Right expected
        it "fails if the argument is not of bang type" $ \qfh -> do
          -- ∅;∅;∅ ⊢ force QInit0 =/=>
          let expr = EForce (EConst QInit0)
          runInferenceForTesting emptyEnv expr qfh `shouldSatisfyIO` isLeft 
      context "when typing fold" $ do
        it "produces the right type and wirecount when all the arguments are values" $ \qfh -> do
          pending -- TODO
        it "produces the right type and wirecount when the step function computes" $ \qfh -> do
          pending -- TODO
        it "produces the right type and wirecount when the starting accumulator computes" $ \qfh -> do
          pending -- TODO
        it "produces the right type and wirecount when the argument list computes" $ \qfh -> do
          pending -- TODO
        it "produces the right type and wirecount when all the arguments compute" $ \qfh -> do
          pending -- TODO
        -- We do not test other combinations of computing arguments so far
        it "fails if the step argument is not of function type" $ \qfh -> do
          pending -- TODO
        it "fails if the step function is not duplicable" $ \qfh -> do
          pending -- TODO
        it "fails if the step function is non-increasing" $ \qfh -> do
          pending -- TODO
        it "fails if the starting accumulator is not of the expected type" $ \qfh -> do
          pending -- TODO
        it "fails if the argument is not of list type" $ \qfh -> do
          pending -- TODO
    describe "domination tests" $ do
    -- Testing by cases on which evaluation step consumes more resources than the others
    -- E.g. for application M N, three tests in which: M dominates the cost, N dominates, the result of the application dominates
      context "when typing pairs" $ do
        it "produces the correct type and wirecount when the first element dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the second element dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the result dominates" $ \qfh -> do
          pending -- TODO
      context "when typing cons" $ do
        it "produces the correct type and wirecount when the head dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the tail dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the result dominates" $ \qfh -> do
          pending -- TODO
      context "when typing application" $ do
        it "produces the correct type and wirecount when the function dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the argument dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the result dominates" $ \qfh -> do
          pending -- TODO
      context "when typing apply" $ do
        it "produces the correct type and wirecount when the circuit term dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the argument dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the result dominates" $ \qfh -> do
          pending -- TODO
      context "when typing fold" $ do
        it "produces the correct type and wirecount when the step function dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the starting accumulator dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the argument list dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the result dominates" $ \qfh -> do
          pending -- TODO
      context "when typing let-in" $ do
        it "produces the correct type and wirecount when the bound expression dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the body dominates" $ \qfh -> do
          pending -- TODO
      context "when typing the destructuring let-in" $ do
        it "produces the correct type and wirecount when the bound expression dominates" $ \qfh -> do
          pending -- TODO
        it "produces the correct type and wirecount when the body dominates" $ \qfh -> do
          pending -- TODO
    describe "Checking and subsumption" $ do
    -- Testing the subtyping relation and the annotation construct
      it "should work" $ \qfh -> do
        pending -- TODO





