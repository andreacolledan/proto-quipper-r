{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Bundle.Parse
  ( parseBundle,
    parseBundleType,
  )
where

import Bundle.AST
import Index.Parse
import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token

bundleLang :: LanguageDef st
bundleLang =
  emptyDef
    { identStart = lower,
      identLetter = alphaNum,
      reservedNames = ["()", "[]", "Bit", "Qubit", "List"]
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

--- BUNDLE TYPES ---------------------------------------------------------------------------------


-- Parses "()" as UnitType
unitType :: Parser BundleType
unitType = m_reserved "()" >> return BTUnit <?> "unit type"

-- Parses "Bit" as BTWire Bit
bit :: Parser BundleType
bit = m_reserved "Bit" >> return (BTWire Bit) <?> "bit type"

-- Parses "Qubit" as BTWire Qubit
qubit :: Parser BundleType
qubit = m_reserved "Qubit" >> return (BTWire Qubit) <?> "qubit type"

-- Parses "(t1, t2, ..., tn)" as (BTPair (BTPair ... (BTPair t1 t2) ... tn)
-- Sugar: n-tensors are desugared left-associatively
tensor :: Parser BundleType
tensor =
  do
    elems <- m_parens $ m_commaSep1 parseBundleType
    return $ foldl1 BTPair elems
    <?> "tensor type"

-- Parses "List[i] bt" as (BTList i bt)
listType :: Parser BundleType
listType =
  do
    m_reserved "List"
    i <- m_brackets parseIndex
    bt <- parseBundleType
    return $ BTList i bt
    <?> "list type"

-- Parses a bundle type
parseBundleType :: Parser BundleType
parseBundleType =
  try unitType <|> try bit <|> try qubit <|> try tensor <|> try listType <?> "bundle type"
