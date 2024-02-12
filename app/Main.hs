module Main (main) where
import PrettyPrinter
import Parsing.Language
import Text.Parsec
import System.Console.ArgParser
import System.TimeIt
import Checking.Language
import Semantics.Type (simplifyType)
import Semantics.Index
import Control.Monad (when)


data CommandLineArguments = CommandLineArguments {
    filepath :: String,
    verbose :: Bool
}

commandLineParser :: ParserSpec CommandLineArguments
commandLineParser = CommandLineArguments
    `parsedBy` reqPos "filepath" `Descr` "The file to parse"
    `andBy` boolFlag "verbose" `Descr` "Print verbose output (parser output)"

main :: IO ()
main = withParseResult commandLineParser $ \args -> do
        let CommandLineArguments {filepath = file, verbose = verb} = args
        when verb $ putStrLn $ "Parsing " ++ file ++ "..."
        contents <- readFile file
        outcome <- timeItIf verb $ return $ parse parseProgram "" contents
        case outcome of
            Left err -> print err
            Right ast -> do
                when verb $ do
                    putStrLn $ "Parsed successfully as \n\t" ++ pretty ast
                    putStrLn "Inferring type..."
                inferred <- timeItIf verb $ return $ runTermTypeInference emptyctx emptyctx ast
                case inferred of
                    Left err -> putStrLn $ "Inference failed: " ++ show err
                    Right inferred -> do
                        putStrLn $ "Inferred type: " ++ pretty (simplifyType $ fst inferred)
                        putStrLn $ "Inferred bound: " ++ pretty (simplifyIndex $ snd inferred)
        where
            timeItIf verb = if verb then timeIt else id

