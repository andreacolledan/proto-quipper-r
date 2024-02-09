module ParsingSpec.LanguageSpec where

import Test.Hspec
import Parsing.Language
import Text.Parsec (parse)
import AST.Language
import qualified Primitive
import AST.Bundle (WireType(..))
import qualified AST.Bundle as Bundle

spec :: Spec
spec = do
    describe "value parser" $ do
        it "parses a variable name" $ do
            parse parseProgram "" "x" `shouldBe` Right (Return (Variable "x"))
        it "parses a constant name" $ do
            parse parseProgram "" "Hadamard" `shouldBe` Right (Return Primitive.hadamard)
        it "parses a unit value" $ do
            parse parseProgram "" "()" `shouldBe` Right (Return UnitValue)
        it "parses a pair" $ do
            parse parseProgram "" "(x, y)" `shouldBe` Right (Return (Pair (Variable "x") (Variable "y")))
        it "parses the empty list" $ do
            parse parseProgram "" "[]" `shouldBe` Right (Return Nil)
        it "parses a list" $ do
            parse parseProgram "" "[x, y]" `shouldBe` Right (Return (Cons (Variable "x") (Cons (Variable "y") Nil)))
        it "parses a lambda" $ do
            parse parseProgram "" "\\x::Qubit . return x" `shouldBe` Right (Return (Abs "x" (WireType Qubit) (Return (Variable "x"))))
        it "parses a lifted value" $ do
            parse parseProgram "" "lift return x" `shouldBe` Right (Return (Lift (Return (Variable "x"))))
        it "parses a fold" $ do
            parse parseProgram "" "fold[i] step base" `shouldBe` Right (Return (Fold "i" (Variable "step") (Variable "base")))
        it "parses cons's right-associatively" $ do
            parse parseProgram "" "():():tail" `shouldBe` Right (Return (Cons UnitValue (Cons UnitValue (Variable "tail"))))
        it "parses nested prefix constructors correctly" $ do
            parse parseProgram "" "lift force lift return x" `shouldBe` Right (Return (Lift (Force (Lift (Return (Variable "x"))))))
    describe "term parser" $ do
        it "parses a let binding" $ do
            parse parseProgram "" "let x = return () in return x" `shouldBe` Right (Let "x" (Return UnitValue) (Return (Variable "x")))
        it "parses a function application" $ do
            parse parseProgram "" "f x" `shouldBe` Right (App (Variable "f") (Variable "x"))
        it "parses apply" $ do
            parse parseProgram "" "apply(c,l)" `shouldBe` Right (Apply (Variable "c") (Variable "l"))
        it "parses box" $ do
            parse parseProgram "" "box[(Qubit,Qubit)] (lift return f)" `shouldBe` Right (Box
                (Bundle.Tensor (Bundle.WireType Qubit) (Bundle.WireType Qubit))
                (Lift (Return (Variable "f"))))
        it "parses force" $ do
            parse parseProgram "" "force v" `shouldBe` Right (Force (Variable "v"))
        it "parses dest" $ do
            parse parseProgram "" "let(x,y) = z in return z" `shouldBe` Right  (Dest "x" "y" (Variable "z") (Return (Variable "z")))
        it "parses return" $ do
            parse parseProgram "" "return x" `shouldBe` Right (Return (Variable "x"))
        it "parses nested let bindings correctly" $ do
            parse parseProgram "" "let x = let y = return () in return y in let z = return x in return z" `shouldBe` Right (Let "x" (Let "y" (Return UnitValue) (Return (Variable "y"))) (Let "z" (Return (Variable "x")) (Return (Variable "z"))))
        
        
