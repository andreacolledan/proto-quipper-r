module Index.ASTSpec where

import Test.Hspec
import Index.AST
import qualified Data.HashSet as Set

spec :: Spec
spec = do
  describe "HasIndex instance" $ do
    describe "iv" $ do
      it "returns the set of index variables (bound or free) that occur in an index" $ do
        iv (IndexVariable "i") `shouldBe` Set.fromList ["i"]
        iv (Number 0) `shouldBe` Set.empty
        iv (Plus (IndexVariable "i") (IndexVariable "j")) `shouldBe` Set.fromList ["i", "j"]
        iv (Max (IndexVariable "i") (IndexVariable "j")) `shouldBe` Set.fromList ["i", "j"]
        iv (Mult (IndexVariable "i") (IndexVariable "j")) `shouldBe` Set.fromList ["i", "j"]
        iv (Minus (IndexVariable "i") (IndexVariable "j")) `shouldBe` Set.fromList ["i", "j"]
        iv (Maximum "id" (IndexVariable "i") (IndexVariable "id")) `shouldBe` Set.fromList ["id", "i"]
    describe "ifv" $ do
      it "returns the set of free index variables that occur in an index" $ do
        ifv (IndexVariable "i") `shouldBe` Set.fromList ["i"]
        ifv (Number 0) `shouldBe` Set.empty
        ifv (Plus (IndexVariable "i") (IndexVariable "j")) `shouldBe` Set.fromList ["i", "j"]
        ifv (Max (IndexVariable "i") (IndexVariable "j")) `shouldBe` Set.fromList ["i", "j"]
        ifv (Mult (IndexVariable "i") (IndexVariable "j")) `shouldBe` Set.fromList ["i", "j"]
        ifv (Minus (IndexVariable "i") (IndexVariable "j")) `shouldBe` Set.fromList ["i", "j"]
        ifv (Maximum "id" (IndexVariable "i") (IndexVariable "id")) `shouldBe` Set.fromList ["i"]
    describe "isub" $ do
      it "correctly substitutes the index variable id by the index i in x" $ do
        isub (IndexVariable "i") "id" (Number 0) `shouldBe` Number 0
        isub (IndexVariable "i") "id" (IndexVariable "id") `shouldBe` IndexVariable "i"
        isub (IndexVariable "i") "id" (IndexVariable "nid") `shouldBe` IndexVariable "nid"
        isub (IndexVariable "i") "id" (Plus (IndexVariable "id") (IndexVariable "j")) `shouldBe` Plus (IndexVariable "i") (IndexVariable "j")
        isub (IndexVariable "i") "id" (Max (IndexVariable "id") (IndexVariable "j")) `shouldBe` Max (IndexVariable "i") (IndexVariable "j")
        isub (IndexVariable "i") "id" (Mult (IndexVariable "id") (IndexVariable "j")) `shouldBe` Mult (IndexVariable "i") (IndexVariable "j")
        isub (IndexVariable "i") "id" (Minus (IndexVariable "id") (IndexVariable "j")) `shouldBe` Minus (IndexVariable "i") (IndexVariable "j")
      it "works correctly in the case of variable binding" $ do
        isub (IndexVariable "i") "id" (Maximum "nid" (IndexVariable "id") (IndexVariable "j")) `shouldBe` Maximum "nid" (IndexVariable "i") (IndexVariable "j")
        isub (IndexVariable "i") "id" (Maximum "nid" (IndexVariable "j") (IndexVariable "id")) `shouldBe` Maximum "nid" (IndexVariable "j") (IndexVariable "i")
        isub (IndexVariable "i") "id" (Maximum "id" (IndexVariable "id") (IndexVariable "j")) `shouldBe` Maximum "id0" (IndexVariable "i") (IndexVariable "j")
        isub (IndexVariable "i") "id" (Maximum "id" (IndexVariable "j") (IndexVariable "id")) `shouldBe` Maximum "id0" (IndexVariable "j") (IndexVariable "id0")