module Parsing.Language where

import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
    ( GenLanguageDef(reservedNames, identStart, identLetter, opStart,
                     opLetter, reservedOpNames),
      GenTokenParser(TokenParser, brackets, parens, identifier,
                     reservedOp, reserved, whiteSpace, natural, symbol, commaSep1),
      makeTokenParser )
import Text.Parsec.Language
import Text.Parsec (oneOf, alphaNum, lower, (<|>), try, sepBy1, (<?>), letter)

import AST.Language

--TokenParser{
--    parens = m_parens,
--    identifier = m_identifier,
--    reservedOp = m_reservedOp,
--    reserved = m_reserved,
--    whiteSpace = m_whiteSpace,
--    natural = m_natural,
--    symbol = m_symbol,
--    commaSep1 = m_commaSep1,
--    brackets = m_brackets
--} = makeTokenParser emptyDef {
--    identStart = letter,
--    identLetter = alphaNum,
--    opStart = oneOf ":λf-.",
--    opLetter = oneOf ":λfun->.",
--    reservedOpNames = [":", "λ", "fun", "→", "."],
--    reservedNames = ["*", "[]", "lift", "force", "fold"]
--}