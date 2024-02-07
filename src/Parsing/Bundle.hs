{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Parsing.Bundle (
    parseBundle
) where

import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec

import AST.Bundle
import Parsing


bundleLang :: LanguageDef st
bundleLang = emptyDef {
    identStart = lower,
    identLetter = alphaNum,
    reservedNames = ["()", "[]"]
}

bundleTokenParser :: TokenParser st
bundleTokenParser@TokenParser{
    parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    commaSep = m_commaSep,
    commaSep1 = m_commaSep1,
    brackets = m_brackets
} = makeTokenParser bundleLang

lab :: Parser Bundle
lab = do
    l <- m_identifier
    return $ Label l

tuple :: Parser Bundle
tuple = do
    elements <- m_parens $ m_commaSep1 parseBundle
    return $ foldl1 Pair elements

unitValue :: Parser Bundle
unitValue = do
    m_reserved "()"
    return UnitValue

list :: Parser Bundle
list = do
    elements <- m_brackets $ m_commaSep parseBundle
    return $ foldr Cons Nil elements

parseBundle :: Parser Bundle
parseBundle = try unitValue <|> tuple <|> list <|> lab <?> "bundle"