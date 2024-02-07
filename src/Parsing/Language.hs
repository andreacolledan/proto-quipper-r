{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Parsing.Language (
    parseExpression
) where

import Text.Parsec.Token
import Text.Parsec.Language
import Parsing.BundleType (parseBundleType)

import AST.Language
import Text.Parsec
import Parsing.Index

import Parsing
import Parsing.Type



languageDef :: LanguageDef st
languageDef = emptyDef {
    identStart = letter,
    identLetter = alphaNum,
    reservedNames = ["()","[]"],
    reservedOpNames = ["\\","->","force","lift","let","in","box","apply","return",":","fold","=","."]
}

tokenParser :: TokenParser st
tokenParser@TokenParser{
    parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    reservedOp = m_reservedOp,
    brackets = m_brackets,
    commaSep1 = m_commaSep1,
    commaSep = m_commaSep,
    comma = m_comma
} = makeTokenParser languageDef

--- VALUE PARSING ---

unitValue :: Parser Value
unitValue = m_reserved "()" >> return UnitValue <?> "unit value"

variable :: Parser Value
variable = do
    name <- m_identifier
    return $ Variable name
    <?> "variable"

lambda :: Parser Value
lambda = do
    m_reservedOp "\\"
    name <- m_identifier
    m_reservedOp "::"
    ty <- parseType
    m_reservedOp "."
    body <- parseTerm
    return $ Abs name ty body
    <?> "lambda"

lift :: Parser Value
lift = do
    m_reservedOp "lift"
    m <- parseTerm
    return $ Lift m
    <?> "lift"

tuple :: Parser Value
tuple = do
    elements <- m_parens $ m_commaSep1 parseValue
    return $ foldl1 Pair elements
    <?> "tuple"

list :: Parser Value
list = do
    elements <- m_brackets $ m_commaSep parseValue
    return $ foldr Cons Nil elements
    <?> "list"

fold :: Parser Value
fold = do
    m_reservedOp "fold"
    i <- m_brackets m_identifier
    v <- parseValue
    w <- parseValue
    return $ Fold i v w
    <?> "fold"

parseValue :: Parser Value
parseValue = chainl1 baseValue (m_reservedOp ":" >> return Cons)
    where baseValue =
            try unitValue
            <|> try tuple
            <|> try lambda
            <|> try lift
            <|> try list
            <|> try fold
            <|> variable
            <?> "value"

--- TERM PARSING ---

app :: Parser Term
app = do
    f <- parseValue
    x <- parseValue
    return $ App f x
    <?> "application"

letin :: Parser Term
letin = do
    m_reserved "let"
    name <- m_identifier
    m_reservedOp "="
    m <- parseTerm
    m_reservedOp "in"
    n <- parseTerm
    return $ Let name m n
    <?> "let-in"

dest :: Parser Term
dest = do
    m_reserved "let"
    (x1,x2) <- m_parens $ do
        x1 <- m_identifier
        m_comma
        x2 <- m_identifier
        return (x1,x2)
    m_reservedOp "="
    v <- parseValue
    m_reservedOp "in"
    m <- parseTerm
    return $ Dest x1 x2 v m
    <?> "destructuring let-in"

force :: Parser Term
force = do
    m_reservedOp "force"
    v <- parseValue
    return $ Force v
    <?> "force"

box :: Parser Term
box = do
    m_reservedOp "box"
    btype <- m_brackets parseBundleType
    v <- parseValue
    return $ Box btype v 
    <?> "box"

apply :: Parser Term
apply = do
    m_reservedOp "apply"
    (c,l) <- m_parens $ do
        c <- parseValue
        m_comma
        l <- parseValue
        return (c,l)
    return $ Apply c l
    <?> "apply"

ret :: Parser Term
ret = do
    m_reservedOp "return"
    m <- parseValue
    return $ Return m
    <?> "return"

parseTerm :: Parser Term
parseTerm =
    try force
    <|> try letin
    <|> try box
    <|> try apply
    <|> try ret
    <|> try dest
    <|> app
    <?> "term"

parseExpression :: Parser (Either Term Value)
parseExpression =
    Left <$> try parseTerm
    <|> Right <$> try parseValue
    <?> "expression"