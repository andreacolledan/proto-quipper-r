{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
module Parsing.BundleType
  ( parseBundleType,
  )
where

import AST.Bundle
import Parsing.Index
import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token

bundleTypeLang :: LanguageDef st
bundleTypeLang =
  emptyDef
    { reservedOpNames = ["List"],
      reservedNames = ["()", "Bit", "Qubit"]
    }

bundleTypeTokenParser :: TokenParser st
bundleTypeTokenParser@TokenParser
  { parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    commaSep1 = m_commaSep1,
    brackets = m_brackets
  } = makeTokenParser bundleTypeLang


-- Parses "()" as UnitType
unitType :: Parser BundleType
unitType = m_reserved "()" >> return UnitType <?> "unit type"

-- Parses "Bit" as WireType Bit
bit :: Parser BundleType
bit = m_reserved "Bit" >> return (WireType Bit) <?> "bit type"

-- Parses "Qubit" as WireType Qubit
qubit :: Parser BundleType
qubit = m_reserved "Qubit" >> return (WireType Qubit) <?> "qubit type"

-- Parses "(t1, t2, ..., tn)" as (Tensor (Tensor ... (Tensor t1 t2) ... tn)
-- Sugar: n-tensors are desugared left-associatively
tensor :: Parser BundleType
tensor =
  do
    elems <- m_parens $ m_commaSep1 parseBundleType
    return $ foldl1 Tensor elems
    <?> "tensor type"

-- Parses "List[i] bt" as (List i bt)
listType :: Parser BundleType
listType =
  do
    m_reserved "List"
    i <- m_brackets parseIndex
    bt <- parseBundleType
    return $ List i bt
    <?> "list type"

-- Parses a bundle type
parseBundleType :: Parser BundleType
parseBundleType =
  try unitType <|> try bit <|> try qubit <|> try tensor <|> try listType <?> "bundle type"
