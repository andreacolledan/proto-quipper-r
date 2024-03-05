module Lang.Type.SemanticsSpec where

import Test.Hspec 
import Lang.Type.AST
import Lang.Type.Semantics

spec :: Spec
spec = do
  describe "subtyping" $ do
    it "should work :)" $ do
      pending --TODO