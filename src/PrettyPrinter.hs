{-# LANGUAGE FlexibleInstances #-}

module PrettyPrinter where
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set

class Show a => Pretty a where 
  pretty :: a -> String
  pretty = show

instance Pretty Int
instance Pretty String where
  pretty = id

instance (Pretty k, Pretty v) => Pretty (Map.Map k v) where
  pretty m = "{" ++ List.intercalate ", " (List.map (\(k,v) -> pretty k ++ " : " ++ pretty v) (Map.toList m)) ++ "}"

instance Pretty a => Pretty (Set.Set a) where
  pretty s = "{" ++ List.intercalate ", " (List.map pretty (Set.toList s)) ++ "}"