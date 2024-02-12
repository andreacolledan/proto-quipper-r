{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
module Parsing.Bundle
  ( parseBundle,
  )
where

import AST.Bundle
import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token

bundleLang :: LanguageDef st
bundleLang =
  emptyDef
    { identStart = lower,
      identLetter = alphaNum,
      reservedNames = ["()", "[]"]
    }

bundleTokenParser :: TokenParser st
bundleTokenParser@TokenParser
  { parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    commaSep = m_commaSep,
    commaSep1 = m_commaSep1,
    brackets = m_brackets
  } = makeTokenParser bundleLang

-- Parses an identifier "id" as (Label id)
lab :: Parser Bundle
lab = do
  id <- m_identifier
  return $ Label id
  <?> "label"

-- Parses "(b1, b2, ..., bn)" as (Pair (Pair ... (Pair b1 b2) ... bn)
-- Sugar: n-tuples are desugared left-associatively into nested pairs
tuple :: Parser Bundle
tuple = do
  elements <- m_parens $ m_commaSep1 parseBundle
  return $ foldl1 Pair elements
  <?> "tuple"

-- Parses "()" as UnitValue
unitValue :: Parser Bundle
unitValue = do
  m_reserved "()"
  return UnitValue
    <?> "unit value"

-- Parses "[b1, b2, ..., bn]" as (Cons b1 (Cons ... (Cons bn Nil) ...))
-- Sugar: n-lists are desugared right-associatively into nested cons with Nil at the end
list :: Parser Bundle
list = do
    elements <- m_brackets $ m_commaSep parseBundle
    return $ foldr Cons Nil elements
    <?> "list"

-- Parses a bundle
parseBundle :: Parser Bundle
parseBundle = try unitValue <|> tuple <|> list <|> lab <?> "bundle"