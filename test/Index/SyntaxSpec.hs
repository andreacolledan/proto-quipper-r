module Index.SyntaxSpec where

import Test.Hspec

import Index
import qualified Data.Set as Set
import Data.Either (isLeft, isRight)

semanticSpec :: Spec
semanticSpec = do
    describe "index equality" $ do
        it "works for closed terms" $ do
            -- ∅ ⊨ 1 + 2 = 3
            let i = Plus (Number 1) (Number 2)
            let j = Number 3
            checkEq Set.empty i j `shouldSatisfy` isRight
            -- ∅ ⊨ 1 + 3 ≠ 3
            let i = Plus (Number 1) (Number 3)
            let j = Number 3
            checkEq Set.empty i j `shouldSatisfy` isLeft
        it "works for open terms" $ do
            let theta = Set.fromList ["a", "b", "c"]
            -- {a, b, c} ⊨ (a + b) + c = a + (b + c)
            let i = Plus (Plus (IndexVariable "a") (IndexVariable "b")) (IndexVariable "c")
            let j = Plus (IndexVariable "a") (Plus (IndexVariable "b") (IndexVariable "c"))
            checkEq theta i j `shouldSatisfy` isRight
    describe "index inequality" $ do
        it "works for closed terms" $ do
            -- ∅ ⊨ 1 + 1 <= 3
            let i = Plus (Number 1) (Number 1)
            let j = Number 3
            checkLeq Set.empty i j `shouldSatisfy` isRight
        it "works for open terms" $ do
            -- {a, b, c} ⊨ max(a,b) <= max(a+c,b)
            let i = Max (IndexVariable "a") (IndexVariable "b")
            let j = Max (Plus (IndexVariable "a") (IndexVariable "c")) (IndexVariable "b")
            let theta = Set.fromList ["a", "b", "c"]
            checkLeq theta i j `shouldSatisfy` isRight

-- SPECIFICATION --

spec :: Spec
spec = do
    semanticSpec