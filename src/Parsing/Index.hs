{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Parsing.Index (
    parseIndex
) where

import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec (oneOf, alphaNum, lower, (<|>), try)
import AST.Index

import Text.Parsec.String

TokenParser{
    parens = m_parens,
    identifier = m_identifier,
    reservedOp = m_reservedOp,
    reserved = m_reserved,
    whiteSpace = m_whiteSpace,
    natural = m_natural,
    symbol = m_symbol
} = makeTokenParser emptyDef {
    identStart = lower,
    identLetter = alphaNum,
    opStart = oneOf "+-*<",
    opLetter = oneOf "+-*<",
    reservedOpNames = ["+", "-", "*", "<"],
    reservedNames = ["max"]
}

parseNat :: Parser Index
parseNat = do
    n <- m_natural
    return $ Number $ fromInteger n

parseIndexVariable :: Parser Index
parseIndexVariable = do
    v <- m_identifier
    return $ IndexVariable v

parseMax :: Parser Index
parseMax = do
    m_reserved "max"
    m_parens $ do
        i1 <- parseIndex
        m_symbol ","
        i2 <- parseIndex
        return $ Max i1 i2

parseMaximum :: Parser Index
parseMaximum = do
    m_reserved "max"
    m_symbol "["
    ivar <- m_identifier
    m_reservedOp "<"
    i <- parseIndex
    m_symbol "]"
    j <- m_parens parseIndex
    return $ Maximum ivar i j

parseIndex :: Parser Index
parseIndex = let
    indexOperators = [
            [Infix (m_reservedOp "*" >> return Mult) AssocLeft],
            [Infix (m_reservedOp "+" >> return Plus) AssocLeft, Infix (m_reservedOp "-" >> return Minus) AssocLeft]
            ]
    indexTerm = 
            m_parens parseIndex
            <|> parseNat
            <|> parseIndexVariable
            <|> try parseMax
            <|> parseMaximum
    in buildExpressionParser indexOperators indexTerm
