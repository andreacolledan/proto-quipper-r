{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
module Lang.Unified.Parse (
  parseProgram
) where

import Lang.Unified.AST
import Bundle.Parse
import Index.Parse
import Lang.Type.Parse
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token
import Data.Char

unifiedLang :: LanguageDef st
unifiedLang =
  emptyDef
    { commentLine = "--",
      commentStart = "{-",
      commentEnd = "-}",
      identStart = letter <|> char '_',
      identLetter = alphaNum <|> char '_',
      reservedNames = ["let", "in", "forall", "Circ", "apply", "fold", "lift", "box", "force", "dest", "let", "in", "[]", "()"],
      opStart = oneOf "@:\\.=",
      opLetter = char ':',
      reservedOpNames = ["@", "::", ":", "\\", ".", "="]
    }

unifiedTokenParser :: TokenParser st
unifiedTokenParser@TokenParser
  { parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    comma = m_comma,
    commaSep = m_commaSep,
    commaSep1 = m_commaSep1,
    brackets = m_brackets,
    reservedOp = m_reservedOp,
    operator = m_operator,
    whiteSpace = m_whiteSpace
  } = makeTokenParser unifiedLang

-- parse "()" as EUnit
unitValue :: Parser Expr
unitValue = do
  m_reserved "()"
  return EUnit
  <?> "unit value"

-- parse "[]" as ENil
nil :: Parser Expr
nil = do
  m_reserved "[]"
  return ENil
  <?> "empty list"

-- parse a lowercase identifier as a variable
variable :: Parser Expr
variable = do
  name@(first : _) <- m_identifier
  if isLower first
    then return $ EVar name
    else fail "Variable names must start with a lowercase letter"
  <?> "variable"

-- parse an uppercase identifier as a constant
constant :: Parser Expr
constant = do
  name <- m_identifier
  case name of
    "QInit0" -> return $ EConst QInit0
    "QInit1" -> return $ EConst QInit1
    "QDiscard" -> return $ EConst QDiscard
    "Meas" -> return $ EConst Meas
    "Hadamard" -> return $ EConst Hadamard
    "PauliX" -> return $ EConst PauliX
    "PauliY" -> return $ EConst PauliY
    "PauliZ" -> return $ EConst PauliZ
    "CNot" -> return $ EConst CNot
    "Toffoli" -> return $ EConst Toffoli
    "MakeRGate" -> return $ EConst MakeRGate
    _ -> fail $ "Unrecognized constant \"" ++ name ++ "\""
  <?> "constant"

-- parse "\x :: t . e" as the (EAbs x t e)
lambda :: Parser Expr
lambda = do
  m_reservedOp "\\"
  name <- m_identifier
  m_reservedOp "::"
  typ <- parseType
  m_reservedOp "."
  e <- parseExpr
  return $ EAbs name typ e
  <?> "abstraction"

-- parse "(e1, e2, ..., en)" as (EPair (EPair ... (EPair e1 e2) ... en)
-- Sugar: n-tuples are desugared left-associatively into nested pairs
tuple :: Parser Expr
tuple = do
  elems <- m_parens $ m_commaSep1 parseExpr
  return $ foldl1 EPair elems
  <?> "tuple"

-- parse "lift e" as (ELift e)
lift :: Parser Expr
lift = do
  m_reserved "lift"
  e <- parseExpr
  return $ ELift e
  <?> "lift"

-- parse "box[bt] e" as (EBox bt e)
box :: Parser Expr
box = do
  m_reserved "box"
  bt <- m_brackets parseBundleType
  e <- parseExpr
  return $ EBox bt e
  <?> "box"

-- parse "force e" as (EForce e)
force :: Parser Expr
force = do
  m_reserved "force"
  e <- parseExpr
  return $ EForce e
  <?> "force"

-- parse "let (x,y) = e1 in e2" as (EDest x y e1 e2)
dest :: Parser Expr
dest = do
  m_reserved "let"
  (x, y) <- m_parens $ do
    x <- m_identifier
    _ <- m_comma
    y <- m_identifier
    return (x, y)
  m_reservedOp "="
  e1 <- parseExpr
  m_reserved "in"
  e2 <- parseExpr
  return $ EDest x y e1 e2
  <?> "destructuring let-in"

-- parse "let x = e1 in e2" as (ELet x e1 e2)
letIn :: Parser Expr
letIn = do
  m_reserved "let"
  x <- m_identifier
  m_reservedOp "="
  e1 <- parseExpr
  m_reserved "in"
  e2 <- parseExpr
  return $ ELet x e1 e2
  <?> "let-in"

-- parse "[e1, e2, ..., en]" as (ECons e1 (ECons ... (ECons en ENil) ...))
-- Sugar: list literals are desugared right-associatively into nested Cons with Nil at the end
list :: Parser Expr
list = do
  elems <- m_brackets $ m_commaSep parseExpr
  return $ foldr ECons ENil elems
  <?> "list literal"

-- parse ":" as the infix operator Cons
consOp :: Parser (Expr -> Expr -> Expr)
consOp = m_reservedOp ":" >> return ECons <?> "cons operator"

-- parse ":: t" as the postfix operator (\e -> EAnno e t)
annOp :: Parser (Expr -> Expr)
annOp = do
  m_reservedOp "::"
  t <- parseType
  return $ flip EAnno t
  <?> "type annotation"

-- parse "fold(e1, e2)" as (EFold e1 e2)
fold :: Parser Expr
fold = do
  m_reserved "fold"
  (e1,e2,e3) <- m_parens $ do
    e1 <- parseExpr
    _ <- m_comma
    e2 <- parseExpr
    _ <- m_comma
    e3 <- parseExpr
    return (e1,e2,e3)
  return $ EFold e1 e2 e3
  <?> "fold"

-- parse "apply(e1,e2)" as (EApply e1 e2)
apply :: Parser Expr
apply = do
  m_reserved "apply"
  (e1,e2) <- m_parens $ do
    e1 <- parseExpr
    _ <- m_comma
    e2 <- parseExpr
    return (e1,e2)
  return $ EApply e1 e2
  <?> "apply"

-- parse "@ i" as the postfix operator (\e -> EIApp e i)
iappOp :: Parser (Expr -> Expr)
iappOp = do
  m_reservedOp "@"
  i <- parseIndex
  return $ flip EIApp i
  <?> "index application"

-- parse "@i . e" as (EIAbs i e)
iabs :: Parser Expr
iabs = do
  m_reservedOp "@"
  i <- m_identifier
  m_reservedOp "."
  e <- parseExpr
  return $ EIAbs i e 
  <?> "universal quantification"

-- parse spaces as the infix operator EApp
appOp :: Parser (Expr -> Expr -> Expr)  
appOp = m_whiteSpace >> return EApp <?> "application"


-- parse a PQR unified expression
parseExpr :: Parser Expr
parseExpr = let
  operatorTable = [
    [Infix appOp AssocLeft],
    [Infix consOp AssocRight],
    [Postfix annOp, Postfix iappOp]
    ]
  simpleExpr 
    = try unitValue
    <|> try nil
    <|> try tuple
    <|> list
    <|> lambda
    <|> try iabs
    <|> try lift
    <|> try dest
    <|> try letIn
    <|> try box
    <|> try force
    <|> try apply
    <|> try fold
    <|> try constant
    <|> try variable
    <|> m_parens parseExpr
    <?> "simple expression"
  in buildExpressionParser operatorTable simpleExpr <?> "expression"

-- parse a PQR unified program
parseProgram :: Parser Expr
parseProgram = do
  m_whiteSpace
  e <- parseExpr
  eof
  return e
  <?> "program"