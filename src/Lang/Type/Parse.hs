{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Lang.Type.Parse
  ( parseType,
  )
where

import Bundle.AST (WireType (..))
import Lang.Type.AST
import Bundle.Parse
import Index.Parse
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token

typeLang :: LanguageDef st
typeLang =
  emptyDef
    { reservedOpNames = ["->", "!", "List", "Circ"],
      reservedNames = ["Bit", "Qubit", "()"]
    }

typeTokenParser :: TokenParser st
typeTokenParser@TokenParser
  { parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    reservedOp = m_reservedOp,
    brackets = m_brackets,
    comma = m_comma,
    commaSep1 = m_commaSep1
  } = makeTokenParser typeLang

-- Parses "t1 ->[i,j] t2" as (Arrow t1 t2 i j)
arrowOperator :: Parser (Type -> Type -> Type)
arrowOperator = do
  m_reservedOp "->"
  (i, j) <- m_brackets $ do
    i <- parseIndex
    _ <- m_comma
    j <- parseIndex
    return (i, j)
  return $ \t1 t2 -> Arrow t1 t2 i j

-- Parses "Circ[i](btype1, btype2)" as (Circ i btype1 btype2)
circ :: Parser Type
circ = do
  m_reservedOp "Circ"
  i <- m_brackets parseIndex
  (btype1, btype2) <- m_parens $ do
    btype1 <- parseBundleType
    _ <- m_comma
    btype2 <- parseBundleType
    return (btype1, btype2)
  return $ Circ i btype1 btype2

-- Parses "Bit" as (WireType Bit)
bit :: Parser Type
bit = m_reserved "Bit" >> return (WireType Bit)

-- Parses "Qubit" as (WireType Qubit)
qubit :: Parser Type
qubit = m_reserved "Qubit" >> return (WireType Qubit)

-- Parses "()" as UnitType
unitType :: Parser Type
unitType = m_reserved "()" >> return UnitType

-- Parses "(t1, t2, ..., tn)" as (Tensor (Tensor ... (Tensor t1 t2) ... tn))
-- Sugar: n-tensors are desugared left-associatively
tensor :: Parser Type
tensor = do
  elems <- m_parens $ m_commaSep1 parseType
  return $ foldl1 Tensor elems

-- Parses "List[i]" as a prefix operator t |-> List[i] t
listOperator :: Parser (Type -> Type)
listOperator = do
  m_reservedOp "List"
  i <- m_brackets parseIndex
  return $ List i

bangOperator :: Parser (Type -> Type)
bangOperator = m_reservedOp "!" >> return Bang

-- Parses a type
parseType :: Parser Type
parseType =
  let table =
        [ [Prefix listOperator, Prefix bangOperator],
          [Infix arrowOperator AssocRight] -- arrows have lower precedence than bangs and list constructors
        ]
      baseType = try unitType <|> bit <|> qubit <|> tensor <|> circ <?> "type"
   in buildExpressionParser table baseType <?> "type"