module Main (main) where

import Control.Monad (when)
import Index.Semantics
import Lang.Paper.Infer as P
import qualified Lang.Paper.Parse as P
import Lang.Type.Semantics (simplifyType)
import Lang.Unified.Infer
import qualified Lang.Unified.Parse as U
import PrettyPrinter
import System.Console.ArgParser
import Text.Parsec
import System.IO (hPrint, stderr)

data CommandLineArguments = CommandLineArguments
  { filepath :: String,
    paper :: Bool,
    verbose :: Bool
  }

commandLineParser :: ParserSpec CommandLineArguments
commandLineParser =
  CommandLineArguments
    `parsedBy` reqPos "filepath"
    `Descr` "The file to parse"
    `andBy` boolFlag "paper"
    `Descr` "Use the original syntax from the paper"
    `andBy` boolFlag "verbose"
    `Descr` "Print verbose output (parser output)"

main :: IO ()
main = withParseResult commandLineParser $ \args -> do
  let CommandLineArguments {filepath = file, paper = p, verbose = verb} = args
  when verb $ putStrLn $ "Parsing " ++ file ++ "..."
  contents <- readFile file
  (if p then standardPipeline else unifiedPipeline) contents verb
  where
    standardPipeline contents verb = do
      case parse P.parseProgram "" contents of
        Left err -> print err
        Right ast -> do
          when verb $ do
            putStrLn $ "Parsed successfully as \n\t" ++ pretty ast
            putStrLn "Inferring type..."
          let outcome = runTermTypeInference P.emptyctx P.emptyctx ast
          case outcome of
            Left err -> putStrLn $ "Inference failed: " ++ show err
            Right inferred -> do
              putStrLn $ "Inferred type: " ++ pretty (simplifyType $ fst inferred)
              putStrLn $ "Inferred bound: " ++ pretty (simplifyIndex $ snd inferred)
    unifiedPipeline contents verb = do
      case parse U.parseProgram "" contents of
        Left err -> print err
        Right ast -> do
          when verb $ do
            putStrLn $ "Parsed successfully as \n\t" ++ pretty ast
            putStrLn "Inferring type..."
          let outcome = runTypeInference ast
          case outcome of
            Left err -> hPrint stderr err
            Right (t, i) -> do
              putStrLn $ "* Inferred type: " ++ pretty (simplifyType t)
              putStrLn $ "* Inferred bound: " ++ pretty (simplifyIndex i)