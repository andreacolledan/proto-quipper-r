{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Parsing.BundleType (
    parseBundleType
) where
    
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec

import Parsing.Index

import Parsing

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
unitType =  m_reserved "()" >> return UnitType

bit :: Parser BundleType
bit = m_reserved "Bit" >> return (WireType Bit)

qubit :: Parser BundleType
qubit = m_reserved "Qubit" >> return (WireType Qubit)

tensor :: Parser BundleType
tensor = do
    elems <- m_brackets $ m_commaSep1 parseBundleType
    return $ foldl1 Tensor elems

listType :: Parser BundleType
listType = do
    m_reserved "List"
    i <- m_brackets parseIndex
    typ <- parseBundleType
    return $ List i typ

parseBundleType :: Parser BundleType
parseBundleType =
    try unitType <|> try bit <|> try qubit <|> try tensor <|> listType <?> "bundle type"

