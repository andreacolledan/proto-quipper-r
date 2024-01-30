{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Parsing.Bundle (
    parseBundle
) where

import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec (oneOf, alphaNum, lower, (<|>), try, sepBy1, (<?>))

import AST.Bundle

TokenParser{
    parens = m_parens,
    identifier = m_identifier,
    reservedOp = m_reservedOp,
    reserved = m_reserved,
    whiteSpace = m_whiteSpace,
    natural = m_natural,
    symbol = m_symbol,
    commaSep1 = m_commaSep1,
    brackets = m_brackets
} = makeTokenParser emptyDef {
    identStart = lower,
    identLetter = alphaNum,
    opStart = oneOf ":",
    opLetter = oneOf ":",
    reservedOpNames = [":"],
    reservedNames = ["*", "[]"]
}

parseLabel :: Parser Bundle
parseLabel = do
    l <- m_identifier
    return $ Label l

parseTuple :: Parser Bundle
parseTuple = do
    elements <- m_parens $ m_commaSep1 parseBundle
    return $ foldl1 Pair elements

parseUnit :: Parser Bundle
parseUnit = do
    m_reserved "*"
    return UnitValue

parseNil :: Parser Bundle
parseNil = do
    m_reserved "[]"
    return Nil

parseList :: Parser Bundle
parseList = do
    elements <- m_brackets $ m_commaSep1 parseBundle
    return $ foldr Cons Nil elements

parseBundle :: Parser Bundle
parseBundle = let 
    bundleOperators = [[Infix (m_reservedOp ":" >> return Cons) AssocRight]]
    bundleTerm = parseUnit <|> parseNil <|> parseList <|> parseTuple <|> parseLabel
    in buildExpressionParser bundleOperators bundleTerm <?> "bundle"


