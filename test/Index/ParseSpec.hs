module Index.ParseSpec (spec) where

import Index.AST
import Index.Parse
import Test.Hspec
import Text.Parsec (parse)

spec :: Spec
spec = do
  describe "index parser" $ do
    it "parses a natural number" $ do
      parse parseIndex "" "123" `shouldBe` Right (Number 123)
    it "parses an index variable" $ do
      parse parseIndex "" "a" `shouldBe` Right (IndexVariable "a")
    it "parses a max" $ do
      parse parseIndex "" "max(1,2)" `shouldBe` Right (Max (Number 1) (Number 2))
    it "parses a sum" $ do
      parse parseIndex "" "1+2" `shouldBe` Right (Plus (Number 1) (Number 2))
    it "parses a product" $ do
      parse parseIndex "" "1*2" `shouldBe` Right (Mult (Number 1) (Number 2))
    it "parses a maximum" $ do
      parse parseIndex "" "max[i<4] i*2 + 2" `shouldBe` Right (Maximum "i" (Number 4) (Plus (Mult (IndexVariable "i") (Number 2)) (Number 2)))
    it "parses complex expressions" $ do
      parse parseIndex "" "max[j<k](max(1, max[i<j] (i+1 + (j-1-i) * 2)))" `shouldBe` Right (Maximum "j" (IndexVariable "k") (Max (Number 1) (Maximum "i" (IndexVariable "j") (Plus (Plus (IndexVariable "i") (Number 1)) (Mult (Minus (Minus (IndexVariable "j") (Number 1)) (IndexVariable "i")) (Number 2))))))
      parse parseIndex "" "max[j<k] max[i<j] i+j+k" `shouldBe` Right (Maximum "j" (IndexVariable "k") (Maximum "i" (IndexVariable "j") (Plus (Plus (IndexVariable "i") (IndexVariable "j")) (IndexVariable "k"))))

