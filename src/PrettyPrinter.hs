module PrettyPrinter where

class Show a => Pretty a where 
  pretty :: a -> String
  pretty = show