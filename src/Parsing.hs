{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
module Parsing where
import Text.Parsec

data ParserState = ParserState {
    fvCounter :: Int
}

type Parser = Parsec String ()

--freeVariableName :: Parser String
--freeVariableName = do
--    ParserState{fvCounter = counter} <- getState
--    putState $ ParserState{fvCounter = counter + 1}
--    return $ "_x" ++ show counter