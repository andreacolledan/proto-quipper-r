module Main (main) where
import System.Environment
import System.Exit
import Control.Monad
import PrettyPrinter
import Parsing.Language
import Text.Parsec
import Parsing

main :: IO ()
main = do
        args <- getArgs
        when (null args) $ do
                putStrLn "Usage: pqr <file>"
                exitFailure
        let file = head args
        putStrLn $ "Parsing " ++ file ++ "..."
        contents <- readFile file
        let outcome = parse parseExpression "" contents
        case outcome of
            Left err -> print err
            Right ast -> putStrLn $ pretty ast
