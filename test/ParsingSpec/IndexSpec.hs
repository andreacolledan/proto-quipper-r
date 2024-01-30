module ParsingSpec.IndexSpec (
    spec
) where

import Test.Hspec
import Text.Parsec (parse)
import AST.Index
import Parsing.Index

spec :: Spec
spec = do
    describe "index parsing" $ do
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
            parse parseIndex "" "max[i<4] (i*2 + 2)" `shouldBe` Right (Maximum "i" (Number 4) (Plus (Mult (IndexVariable "i") (Number 2)) (Number 2)))
        it "parses complex expressions" $ do
            parse parseIndex "" "max[j<k](max(1, max[i<j] (i+1 + (j-1-i) * 2)))" `shouldBe` Right (Maximum "j" (IndexVariable "k") (Max (Number 1) (Maximum "i" (IndexVariable "j") (Plus (Plus (IndexVariable "i") (Number 1)) (Mult (Minus (Minus (IndexVariable "j") (Number 1)) (IndexVariable "i")) (Number 2))))))