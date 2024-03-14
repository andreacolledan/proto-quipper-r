module Bundle.ParseSpec (spec) where
  
import Bundle.AST
import Bundle.Parse
import Test.Hspec
import Text.Parsec (parse)

spec :: Spec
spec = do
  describe "bundle parser" $ do
    it "parses a label" $ do
      parse parseBundle "" "a" `shouldBe` Right (Label "a")
    it "parses a tuple" $ do
      parse parseBundle "" "(a, b, c)" `shouldBe` Right (Pair (Pair (Label "a") (Label "b")) (Label "c"))
    it "parses a unit" $ do
      parse parseBundle "" "()" `shouldBe` Right UnitValue
    it "parses a Nil" $ do
      parse parseBundle "" "[]" `shouldBe` Right Nil
    it "parses a list" $ do
      parse parseBundle "" "[a, b, c]" `shouldBe` Right (Cons (Label "a") (Cons (Label "b") (Cons (Label "c") Nil)))
    it "parses complex expressions" $ do
      parse parseBundle "" "([a, b], c)" `shouldBe` Right (Pair (Cons (Label "a") (Cons (Label "b") Nil)) (Label "c"))
