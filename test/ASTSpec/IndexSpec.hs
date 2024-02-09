module ASTSpec.IndexSpec (spec) where

import AST.Index
import Semantics.Index

import Test.Hspec


-- SPECIFICATION --

spec :: Spec
spec = do
    describe "index equality" $ do
        it "works for simple closed terms" $ do
            -- |== 1 + 2 = 3
            let i = Plus (Number 1) (Number 2)
            let j = Number 3
            checkEq i j `shouldBe` True
            -- |== 1 + 3 ≠ 3
            let i = Plus (Number 1) (Number 3)
            let j = Number 3
            checkEq i j `shouldBe` False
        it "works for simple open terms" $ do
            -- |== ∀a,b,c. (a + b) + c = a + (b + c)
            let i = Plus (Plus (IndexVariable "a") (IndexVariable "b")) (IndexVariable "c")
            let j = Plus (IndexVariable "a") (Plus (IndexVariable "b") (IndexVariable "c"))
            checkEq i j `shouldBe` True
            -- |=/= ∀a,b,c. a+c = max(a,b) + c
            let i = Plus (IndexVariable "a") (IndexVariable "c")
            let j = Plus (Max (IndexVariable "a") (IndexVariable "b")) (IndexVariable "c")
            checkEq i j `shouldBe` False
        it "works for closed maxima" $ do
            -- |== max[i<4] i*2 + 2 = 8
            let i = Maximum "i" (Number 4) (Plus (Mult (IndexVariable "i") (Number 2)) (Number 2))
            let j = Number 8
            checkEq i j `shouldBe` True
            -- |== max[i<4] i*2 + 2 ≠ 9
            let j = Number 9
            checkEq i j `shouldBe` False
    describe "index inequality" $ do
        it "works for closed terms" $ do
            -- |== + 1 <= 3
            let i = Plus (Number 1) (Number 1)
            let j = Number 3
            checkLeq i j `shouldBe` True
        it "works for open terms" $ do
            -- |== ∀a,b,c. max(a,b) <= max(a+c,b)
            let i = Max (IndexVariable "a") (IndexVariable "b")
            let j = Max (Plus (IndexVariable "a") (IndexVariable "c")) (IndexVariable "b")
            checkLeq i j `shouldBe` True
            -- |== ∀a,b,c. a+c <= max(a,b) + c
            let i = Plus (IndexVariable "a") (IndexVariable "c")
            let j = Plus (Max (IndexVariable "a") (IndexVariable "b")) (IndexVariable "c")
            checkLeq i j `shouldBe` True
            -- |=/= ∀a,b,c. max(a,b) <= a+c
            let i = Max (IndexVariable "a") (IndexVariable "b")
            let j = Plus (IndexVariable "a") (IndexVariable "c")
            checkLeq i j `shouldBe` False
        it "works for maxima" $ do
            -- |== ∀j. max[i<j] i + 1 <= j + 1
            let i = Maximum "i" (IndexVariable "j") (Plus (IndexVariable "i") (Number 1))
            let j = IndexVariable "j" `Plus` Number 1
            checkLeq i j `shouldBe` True