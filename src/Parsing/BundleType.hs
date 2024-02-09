{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Parsing.BundleType (
    parseBundleType
) where


import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec

import Parsing.Index

import Text.Parsec.String

import AST.Bundle

bundleTypeLang :: LanguageDef st
bundleTypeLang = emptyDef {
    reservedOpNames = ["List"],
    reservedNames = ["()", "Bit", "Qubit"]
}

bundleTypeTokenParser :: TokenParser st
bundleTypeTokenParser@TokenParser{
    parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    commaSep1 = m_commaSep1,
    brackets = m_brackets
} = makeTokenParser bundleTypeLang

unitType :: Parser BundleType
unitType =  m_reserved "()" >> return UnitType <?> "unit type"

bit :: Parser BundleType
bit = m_reserved "Bit" >> return (WireType Bit) <?> "bit type"

qubit :: Parser BundleType
qubit = m_reserved "Qubit" >> return (WireType Qubit) <?> "qubit type"

tensor :: Parser BundleType
tensor = do
    elems <- m_parens $ m_commaSep1 parseBundleType
    return $ foldl1 Tensor elems
    <?> "tensor type"

listType :: Parser BundleType
listType = do
    m_reserved "List"
    i <- m_brackets parseIndex
    typ <- parseBundleType
    return $ List i typ
    <?> "list type"

parseBundleType :: Parser BundleType
parseBundleType =
    try unitType <|> try bit <|> try qubit <|> try tensor <|> try listType <?> "bundle type"

