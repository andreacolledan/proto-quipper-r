module Main (main) where
import PrettyPrinter
import Parsing.Language
import Text.Parsec
import System.Console.ArgParser
import Checking.Language
import AST.Language (simplifyType)
import AST.Index (simplify)

newtype CommandLineArguments = CommandLineArguments {
    filepath :: String
}

commandLineParser :: ParserSpec CommandLineArguments
commandLineParser = CommandLineArguments
    `parsedBy` reqPos "filepath" `Descr` "The file to parse"

main :: IO ()
main = withParseResult commandLineParser $ \args -> do
        let file = filepath args
        putStrLn $ "Parsing " ++ file ++ "..."
        contents <- readFile file
        let outcome = parse parseProgram "" contents
        case outcome of
            Left err -> print err
            Right ast -> do
                putStrLn $ "Parsed successfully as \n\t" ++ pretty ast
                putStrLn "Inferring type..."
                case ast of
                        (Left term) -> do
                                let inferred = runTermTypeInference emptyctx emptyctx term
                                case inferred of
                                    Left err -> putStrLn $ "Inference failed: " ++ show err
                                    Right inferred -> do
                                        putStrLn $ "Inferred type: " ++ pretty (simplifyType $ fst inferred)
                                        putStrLn $ "Inferred bound: " ++ pretty (simplify $ snd inferred)
                        (Right value) -> do
                                let inferred = runValueTypeInference emptyctx emptyctx value
                                case inferred of
                                    Left err -> putStrLn $ "Inference failed: " ++ show err
                                    Right inferred -> do
                                        putStrLn $ "Inferred type: " ++ pretty (simplifyType inferred)

