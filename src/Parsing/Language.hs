{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
module Parsing.Language
  ( parseProgram,
  )
where

import AST.Language
import Data.Char
import Parsing.BundleType (parseBundleType)
import Parsing.Type
import qualified Primitive
import Text.Parsec
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token
import Text.Parsec.Expr (buildExpressionParser, Operator (Postfix, Infix), Assoc (AssocRight))

languageDef :: LanguageDef st
languageDef =
  emptyDef
    { commentLine = "--",
      identStart = letter <|> char '_',
      identLetter = alphaNum <|> char '_',
      reservedOpNames = ["\\", "->", "force", "lift", "let", "in", "box", "apply", "return", ":", "fold", "=", "."],
      reservedNames = ["force", "lift", "let", "in", "box", "apply", "return", "fold"]
    }

tokenParser :: TokenParser st
tokenParser@TokenParser
  { parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    reservedOp = m_reservedOp,
    brackets = m_brackets,
    commaSep1 = m_commaSep1,
    commaSep = m_commaSep,
    comma = m_comma
  } = makeTokenParser languageDef

--- VALUE PARSING -----------------------------------------------

-- Parses "()" as UnitValue
unitValue :: Parser Value
unitValue = m_reserved "()" >> return UnitValue <?> "unit value"

-- Parses a lowercase identifier as a variable
variable :: Parser Value
variable =
  do
    name@(first : _) <- m_identifier
    if isLower first
      then return $ Variable name
      else fail "Variable names must start with a lowercase letter"
    <?> "variable"

-- Parses an uppercase identifier as a constant
constant :: Parser Value
constant = do
  name <- m_identifier
  case name of
    "Hadamard" -> return Primitive.hadamard
    "PauliX" -> return Primitive.pauliX
    "QInit" -> return Primitive.qinit
    "QDiscard" -> return Primitive.qdiscard
    "CNot" -> return Primitive.cnot
    _ -> fail "Unknown constant"

-- Parses "\x :: t . m" as (Abs x t m)
lambda :: Parser Value
lambda =
  do
    m_reservedOp "\\"
    name <- m_identifier
    m_reservedOp "::"
    ty <- parseType
    m_reservedOp "."
    body <- parseTerm
    return $ Abs name ty body
    <?> "lambda"

-- Parses "lift m" as (Lift m)
lift :: Parser Value
lift =
  do
    m_reservedOp "lift"
    m <- parseTerm
    return $ Lift m
    <?> "lift"

-- Parses "(v1, v2, ..., vn)" as (Pair (Pair ... (Pair v1 v2) ... vn)
-- Sugar: n-tuples are desugared left-associatively into nested pairs
tuple :: Parser Value
tuple =
  do
    elements <- m_parens $ m_commaSep1 parseValue
    return $ foldl1 Pair elements
    <?> "tuple"

-- Parses "[v1, v2, ..., vn]" as (Cons v1 (Cons ... (Cons vn Nil) ...))
-- Sugar: list literals are desugared right-associatively into nested Cons with Nil at the end
list :: Parser Value
list =
  do
    elements <- m_brackets $ m_commaSep parseValue
    return $ foldr Cons Nil elements
    <?> "list"

-- Parses "fold[i] v w" as (Fold i v w)
fold :: Parser Value
fold =
  do
    m_reservedOp "fold"
    i <- m_brackets m_identifier
    v <- parseValue
    w <- parseValue
    return $ Fold i v w
    <?> "fold"

consOperator :: Parser (Value -> Value -> Value)
consOperator = m_reservedOp ":" >> return Cons

annOperator :: Parser (Value -> Value)
annOperator = do
  m_reservedOp "::"
  t <- parseType
  return $ \v -> Anno v t


-- Parser for values
parseValue :: Parser Value
-- the parsing of cons is left-recursive, so we need chainr1
parseValue = let
  operators = [[Infix consOperator AssocRight], [Postfix annOperator]]
  baseValue = unitValue
        <|> tuple
        <|> lambda
        <|> lift
        <|> list
        <|> fold
        <|> m_parens parseValue
        <|> try constant
        <|> try variable
        <?> "value"
  in buildExpressionParser operators baseValue
      


--- TERM PARSING -----------------------------------------------

-- Parses "v w" as (App v w)
app :: Parser Term
app =
  do
    f <- parseValue
    x <- parseValue
    return $ App f x
    <?> "application"

-- Parses "let x = m in n" as (Let x m n)
letin :: Parser Term
letin =
  do
    m_reserved "let"
    name <- m_identifier
    m_reservedOp "="
    m <- parseTerm
    m_reservedOp "in"
    n <- parseTerm
    return $ Let name m n
    <?> "let-in"

-- Parses "let (x1, x2) = v in m" as (Dest x1 x2 v m)
dest :: Parser Term
dest =
  do
    m_reserved "let"
    (x1, x2) <- m_parens $ do
      x1 <- m_identifier
      _ <- m_comma
      x2 <- m_identifier
      return (x1, x2)
    m_reservedOp "="
    v <- parseValue
    m_reservedOp "in"
    m <- parseTerm
    return $ Dest x1 x2 v m
    <?> "destructuring let-in"

-- Parses "force v" as (Force v)
force :: Parser Term
force =
  do
    m_reservedOp "force"
    v <- parseValue
    return $ Force v
    <?> "force"

-- Parses "box[bt] v" as (Box bt v)
box :: Parser Term
box =
  do
    m_reservedOp "box"
    btype <- m_brackets parseBundleType
    v <- parseValue
    return $ Box btype v
    <?> "box"

-- Parses "apply (c, l)" as (Apply c l)
apply :: Parser Term
apply =
  do
    m_reservedOp "apply"
    (c, l) <- m_parens $ do
      c <- parseValue
      _ <- m_comma
      l <- parseValue
      return (c, l)
    return $ Apply c l
    <?> "apply"

-- Parses "return v" as (Return v)
ret :: Parser Term
ret =
  do
    m_reservedOp "return"
    m <- parseValue
    return $ Return m
    <?> "return"

-- Parser for terms
parseTerm :: Parser Term
parseTerm =
  try letin
    <|> try dest
    <|> force
    <|> box
    <|> apply
    <|> ret
    <|> try app
    <|> try (m_parens parseTerm)
    -- Sugar: if value v appears where a term is expected, desugar it into (Return v)
    <|> Return <$> try parseValue
    <?> "term"

-- Parse either a term or a value
-- A parsed value v is returned as (Return v)
parseProgram :: Parser Term
parseProgram =
  do
    whiteSpace tokenParser
    result <- parseTerm
    eof
    return result
    <?> "program"