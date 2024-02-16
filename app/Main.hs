module Main (main) where

import Control.Monad (when)
import Index.AST
import Index.Semantics
import Lang.Paper.Infer
import qualified Lang.Paper.Parse as P
import Lang.Type.Semantics (simplifyType)
import Lang.Unified.Infer
import qualified Lang.Unified.Parse as U
import PrettyPrinter
import System.Console.ArgParser
import System.TimeIt
import Text.Parsec

data CommandLineArguments = CommandLineArguments
  { filepath :: String,
    unified :: Bool,
    verbose :: Bool
  }

commandLineParser :: ParserSpec CommandLineArguments
commandLineParser =
  CommandLineArguments
    `parsedBy` reqPos "filepath"
    `Descr` "The file to parse"
    `andBy` boolFlag "unified"
    `Descr` "Use the unified syntax for terms and values"
    `andBy` boolFlag "verbose"
    `Descr` "Print verbose output (parser output)"

main :: IO ()
main = withParseResult commandLineParser $ \args -> do
  let CommandLineArguments {filepath = file, unified = uni, verbose = verb} = args
  -- when verb $ putStrLn $ "Parsing " ++ file ++ "..."
  contents <- readFile file
  if uni then unifiedPipeline contents else standardPipeline contents
  where
    standardPipeline contents = do
      case parse P.parseProgram "" contents of
        Left err -> print err
        Right ast -> do
          {-when verb $ do
            putStrLn $ "Parsed successfully as \n\t" ++ pretty ast
            putStrLn "Inferring type..."-}
          let outcome = runTermTypeInference emptyctx emptyctx ast
          case outcome of
            Left err -> putStrLn $ "Inference failed: " ++ show err
            Right inferred -> do
              putStrLn $ "Inferred type: " ++ pretty (simplifyType $ fst inferred)
              putStrLn $ "Inferred bound: " ++ pretty (simplifyIndex $ snd inferred)
    unifiedPipeline contents = do
      case parse U.parseProgram "" contents of
        Left err -> print err
        Right ast -> do
          {-when verb $ do
            putStrLn $ "Parsed successfully as \n\t" ++ pretty ast
            putStrLn "Inferring type..."-}
          let outcome = runTypeInference ast
          case outcome of
            Left err -> putStrLn $ "Inference failed: " ++ show err
            Right (t, i) -> do
              putStrLn $ "Inferred type: " ++ pretty (simplifyType t)
              putStrLn $ "Inferred bound: " ++ pretty (simplifyIndex i)