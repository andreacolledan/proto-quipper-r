module Language.PretyPrinter where

import Language.Syntax


class Show a => Pretty a where 
  pretty :: a -> String
  pretty = show