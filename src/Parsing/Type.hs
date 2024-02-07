module Parsing.Type (
    parseType
) where

import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec

import AST.Language
import Text.Parsec.Expr
import Parsing.Index
import AST.Bundle (WireType (..))
import Parsing
import Parsing.BundleType

typeLang :: LanguageDef st
typeLang = emptyDef {
    reservedOpNames = ["->","!","List","Circ"],
    reservedNames = ["Bit","Qubit","()"]
}

typeTokenParser :: TokenParser st
typeTokenParser@TokenParser{
    parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    reservedOp = m_reservedOp,
    brackets = m_brackets,
    comma = m_comma,
    commaSep1 = m_commaSep1
} = makeTokenParser typeLang

arrowOperator :: Parser (Type -> Type -> Type)
arrowOperator = do
    m_reservedOp "->"
    (i,j) <- m_brackets $ do
        i <- parseIndex
        m_comma
        j <- parseIndex
        return (i,j)
    return $ \t1 t2 -> Arrow t1 t2 i j

listOperator :: Parser (Type -> Type)
listOperator = do
    m_reservedOp "List"
    i <- m_brackets parseIndex
    return $ List i

circ :: Parser Type
circ = do
    m_reservedOp "Circ"
    i <- m_brackets parseIndex
    (btype1, btype2) <- m_parens $ do
        btype1 <- parseBundleType
        m_comma
        btype2 <- parseBundleType
        return (btype1, btype2)
    return $ Circ i btype1 btype2

bit :: Parser Type
bit = m_reserved "Bit" >> return (WireType Bit)

qubit :: Parser Type
qubit = m_reserved "Qubit" >> return (WireType Qubit)

unitType :: Parser Type
unitType = m_reserved "()" >> return UnitType

tensor :: Parser Type
tensor = do
    elems <- m_brackets $ m_commaSep1 parseType
    return $ foldl1 Tensor elems


parseType :: Parser Type
parseType = let
    table = [
        [Prefix listOperator, Prefix (m_reservedOp "!" >> return Bang)],
        [Infix arrowOperator AssocRight] -- arrows have lower precedence than bangs and list constructors
        ]
    baseType = try unitType <|> bit <|> qubit <|> tensor <|> circ <?> "base type"
    in buildExpressionParser table baseType <?> "type"