module Lang.Unified.ParseSpec (spec) where

import Bundle.AST (WireType (..), BundleType (..))
import Index.AST
import Lang.Type.AST
import Lang.Unified.AST
import Lang.Unified.Parse
import Test.Hspec
import Text.Parsec

spec :: Spec
spec = do
  describe "basic expression parser" $ do
    it "parses '()' as the unit value" $ do
      parse parseProgram "" "()" `shouldBe` Right EUnit
    it "parses '[]' as the empty list" $ do
      parse parseProgram "" "[]" `shouldBe` Right ENil
    it "parses a lowercase identifier as a variable" $ do
      parse parseProgram "" "x" `shouldBe` Right (EVar "x")
    it "parses an uppercase identifier as a constant" $ do
      parse parseProgram "" "Hadamard" `shouldBe` Right (EConst Hadamard)
    it "parses '\\x :: () . (x,x)' as an abstraction" $ do
      parse parseProgram "" "\\x :: () . (x,x)" `shouldBe` Right (EAbs "x" TUnit (EPair (EVar "x") (EVar "x")))
    it "parses 'let x = () in x' as a let binding" $ do
      parse parseProgram "" "let x = () in x" `shouldBe` Right (ELet "x" EUnit (EVar "x"))
    it "parses 'let (x,y) = ((),[]) in ([],())' as a destructuring let" $ do
      parse parseProgram "" "let (x,y) = ((),[]) in ([],())" `shouldBe` Right (EDest "x" "y" (EPair EUnit ENil) (EPair ENil EUnit))
    it "parses 'apply(c,l)' as circuit application" $ do
      parse parseProgram "" "apply(c,l)" `shouldBe` Right (EApply (EVar "c") (EVar "l"))
    it "parses 'lift e' as lifting" $ do
      parse parseProgram "" "lift e" `shouldBe` Right (ELift (EVar "e"))
    it "parses 'force e' as forcing" $ do
      parse parseProgram "" "force e" `shouldBe` Right (EForce (EVar "e"))
    it "parses 'box[Qubit] f' as boxing" $ do
      parse parseProgram "" "box[Qubit] f" `shouldBe` Right (EBox (BTWire Qubit) (EVar "f"))
    it "parses 'f x' as function application" $ do
      parse parseProgram "" "f x" `shouldBe` Right (EApp (EVar "f") (EVar "x"))
    it "parses 'x:xs' as list cons" $ do
      parse parseProgram "" "x:xs" `shouldBe` Right (ECons (EVar "x") (EVar "xs"))
    it "parses 'e :: List[3] Qubit' as type annotation" $ do
      parse parseProgram "" "e :: List[3] Qubit" `shouldBe` Right (EAnno (EVar "e") (TList (Number 3) (TWire Qubit)))
    it "parses 'fold(f,acc)' as folding" $ do
      parse parseProgram "" "fold(f,acc)" `shouldBe` Right (EFold (EVar "f") (EVar "acc"))
    it "parses 'forall i . e' as index abstraction" $ do
      parse parseProgram "" "forall i . e" `shouldBe` Right (EIAbs "i" (EVar "e"))
    it "parses 'e @ i' as index application" $ do
      parse parseProgram "" "e @ i" `shouldBe` Right (EIApp (EVar "e") (IndexVariable "i"))
  describe "desugaring" $ do
    it "parses '(x,y,z,w)' as (((x,y),z),w)" $ do
      parse parseProgram "" "(x,y,z,w)" `shouldBe` Right (EPair (EPair (EPair (EVar "x") (EVar "y")) (EVar "z")) (EVar "w"))
    it "parses '[x,y,z,q]' as x:(y:(z:(q:[])))" $ do
      parse parseProgram "" "[x,y,z,q]" `shouldBe` Right (ECons (EVar "x") (ECons (EVar "y") (ECons (EVar "z") (ECons (EVar "q") ENil))))
  describe "associativity" $ do
    it "application is left associative" $ do
      parse parseProgram "" "f x y" `shouldBe` Right (EApp (EApp (EVar "f") (EVar "x")) (EVar "y"))
    it "cons'ing is right associative" $ do
      parse parseProgram "" "x:y:z:[]" `shouldBe` Right (ECons (EVar "x") (ECons (EVar "y") (ECons (EVar "z") ENil)))
    it "nested built-in operators are right associative" $ do
      parse parseProgram "" "box[Qubit] let f = force x in lift f" `shouldBe` Right (EBox (BTWire Qubit) (ELet "f" (EForce (EVar "x")) (ELift (EVar "f"))))
  describe "precedence" $ do
    it "application has precedence over abstraction" $ do
      parse parseProgram "" "\\x :: () . x y" `shouldBe` Right (EAbs "x" TUnit (EApp (EVar "x") (EVar "y")))
    it "cons'ing has precedence over abstraction" $ do
      parse parseProgram "" "\\x :: () . x:y:[]" `shouldBe` Right (EAbs "x" TUnit (ECons (EVar "x") (ECons (EVar "y") ENil)))
    it "application has precedence over cons'ing" $ do
      parse parseProgram "" "f x:y:[]" `shouldBe` Right (ECons (EApp (EVar "f") (EVar "x")) (ECons (EVar "y") ENil))
    it "annotation has precedence over abstraction" $ do
      parse parseProgram "" "\\x :: () . apply(QInit0,x) :: () ->[1,0] Qubit" `shouldBe` Right (EAbs "x" TUnit (EAnno (EApply (EConst QInit0) (EVar "x")) (TArrow TUnit (TWire Qubit) (Number 1) (Number 0))))
    it "index application has precedence over index abstraction" $ do
      parse parseProgram "" "forall i . e @ i" `shouldBe` Right (EIAbs "i" (EIApp (EVar "e") (IndexVariable "i")))
