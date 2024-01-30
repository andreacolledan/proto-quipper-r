module ASTSpec.IndexSpec (spec) where

import AST.Index

import qualified Data.Set as Set
import Test.Hspec


-- SPECIFICATION --

semanticSpec :: Spec
semanticSpec = do
    describe "index equality" $ do
        it "works for simple closed terms" $ do
            -- ∅ ⊨ 1 + 2 = 3
            let i = Plus (Number 1) (Number 2)
            let j = Number 3
            checkEq Set.empty i j `shouldBe` True
            -- ∅ ⊨ 1 + 3 ≠ 3
            let i = Plus (Number 1) (Number 3)
            let j = Number 3
            checkEq Set.empty i j `shouldBe` False
        it "works for simple open terms" $ do
            let theta = Set.fromList ["a", "b", "c"]
            -- {a, b, c} ⊨ (a + b) + c = a + (b + c)
            let i = Plus (Plus (IndexVariable "a") (IndexVariable "b")) (IndexVariable "c")
            let j = Plus (IndexVariable "a") (Plus (IndexVariable "b") (IndexVariable "c"))
            checkEq theta i j `shouldBe` True
            -- {a, b, c} |=/= a+c = max(a,b) + c
            let i = Plus (IndexVariable "a") (IndexVariable "c")
            let j = Plus (Max (IndexVariable "a") (IndexVariable "b")) (IndexVariable "c")
            checkEq theta i j `shouldBe` False
        it "works for closed maxima" $ do
            -- ∅ ⊨ max[i<4] i*2 + 2 = 8
            let i = Maximum "i" (Number 4) (Plus (Mult (IndexVariable "i") (Number 2)) (Number 2))
            let j = Number 8
            checkEq Set.empty i j `shouldBe` True
            -- ∅ ⊨ max[i<4] i*2 + 2 ≠ 9
            let j = Number 9
            checkEq Set.empty i j `shouldBe` False
    describe "index inequality" $ do
        it "works for closed terms" $ do
            -- ∅ ⊨ 1 + 1 <= 3
            let i = Plus (Number 1) (Number 1)
            let j = Number 3
            checkLeq Set.empty i j `shouldBe` True
        it "works for open terms" $ do
            -- {a, b, c} ⊨ max(a,b) <= max(a+c,b)
            let i = Max (IndexVariable "a") (IndexVariable "b")
            let j = Max (Plus (IndexVariable "a") (IndexVariable "c")) (IndexVariable "b")
            let theta = Set.fromList ["a", "b", "c"]
            checkLeq theta i j `shouldBe` True
            -- {a, b, c} ⊨ a+c <= max(a,b) + c
            let i = Plus (IndexVariable "a") (IndexVariable "c")
            let j = Plus (Max (IndexVariable "a") (IndexVariable "b")) (IndexVariable "c")
            let theta = Set.fromList ["a", "b", "c"]
            checkLeq theta i j `shouldBe` True
            -- {a, b, c} |=/= max(a,b) <= a+c
            let i = Max (IndexVariable "a") (IndexVariable "b")
            let j = Plus (IndexVariable "a") (IndexVariable "c")
            let theta = Set.fromList ["a", "b", "c"]
            checkLeq theta i j `shouldBe` False
        it "works for maxima" $ do
            -- j ⊨ max[i<j] i + 1 <= j + 1
            let i = Maximum "i" (IndexVariable "j") (Plus (IndexVariable "i") (Number 1))
            let j = IndexVariable "j" `Plus` Number 1
            let theta = Set.fromList ["j"]
            checkLeq theta i j `shouldBe` True
        


-- SPECIFICATION --

spec :: Spec
spec = do
    semanticSpec