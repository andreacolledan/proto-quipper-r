module Solving.CVC5 where


import Control.Exception
import Control.Monad
import Data.List (isPrefixOf)
import GHC.IO (unsafePerformIO)
import PrettyPrinter
import System.IO
import System.FilePath
import System.Process as Proc
import AST.Index 

-- Converts an index expression to and SMTLIB arithmetical expression
embedIndex :: Index -> String
embedIndex (IndexVariable id) = id
embedIndex (Number n) = show n
embedIndex (Plus i j) = "(+ " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Max i j) = "(max " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Mult i j) = "(* " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Minus i j) = "(- " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Maximum id i j) = "(maximum (lambda ((" ++ id ++ " Int)) " ++ embedIndex j ++ ") " ++ embedIndex i ++ ")"

-- Converts an index relation to the corresponding SMTLIB symbol
embedConstraint :: Constraint -> String
embedConstraint (Eq i j) = "(= " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedConstraint (Leq i j) = "(<= " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"

-- querySMTWithContext theta c queries the CVC5 solver to check if the index constraint
-- c holds for every natural value of the index variables in theta.
-- Returns true if the constraint holds, false otherwise or if the solver throws an error.
querySMTWithContext :: IndexContext -> Constraint -> Bool
querySMTWithContext theta c = unsafePerformIO $ do
    withFile queryFile WriteMode $ \handle -> do
        hPutStrLn handle $ "; " ++ pretty c
        when maximaInvolved $ do
            hPutStrLn handle "(set-logic HO_ALL)"
            hPutStrLn handle "(set-option :fmf-fun true)" --enable recursive functions
        hPutStrLn handle "(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))"  --define max(x,y)
        when maximaInvolved $ --only define maximum(f,j) if needed
            hPutStrLn handle "(define-fun-rec maximum ((f (-> Int Int)) (j Int)) Int (ite (= j 0) 0 (max (f j) (maximum f (- j 1)))))"
        forM_ theta $ \id -> do
            -- for each index variable, initialize an unknown natural variable
            hPutStrLn handle $ "(declare-const " ++ id ++ " Int)"
            hPutStrLn handle $ "(assert (>= " ++ id ++ " 0))"
        -- try to find a counterexample to the relation of the two indices
        hPutStrLn handle $ "(assert (not " ++ embedConstraint c ++ "))"
        hPutStrLn handle "(check-sat)"
    resp <- try $ readProcess "cvc5" [queryFile, "-q"] [] --run CVC5 and get its stdout
    -- append the response to the query file as a comment
    withFile queryFile AppendMode $ \handle -> do
        case resp of
            Left (SomeException e) -> do
                -- the solver threw an error
                hPutStrLn handle $ "; Error thrown: " ++ show e
                return False
            Right resp -> if "unsat" `isPrefixOf` resp then do
                    -- cannot find a counterexample ==> the constraint is valid
                    hPutStrLn handle "; founds unsat (valid)"
                    return True
                else if "sat" `isPrefixOf` resp then do
                    -- found a counterexample ==> the constraint is invalid
                    hPutStrLn handle "; found sat (invalid)"
                    return False
                else do
                    -- any other response is considered an error
                    hPutStrLn handle $ "; got response: " ++ resp
                    return False
    where
        -- query files are stored in the queries/ subdirectory
        queryFile :: FilePath
        queryFile = "queries" </> sanitize (pretty c) <.> "smt2"
        -- checks if the constraint involves the use of maxima
        maximaInvolved :: Bool
        maximaInvolved = case c of
            Eq i j -> containsMaximum i || containsMaximum j
            Leq i j -> containsMaximum i || containsMaximum j
        containsMaximum :: Index -> Bool
        containsMaximum (IndexVariable _) = False
        containsMaximum (Number _) = False
        containsMaximum (Plus i j) = containsMaximum i || containsMaximum j
        containsMaximum (Max i j) = containsMaximum i || containsMaximum j
        containsMaximum (Mult i j) = containsMaximum i || containsMaximum j
        containsMaximum (Minus i j) = containsMaximum i || containsMaximum j
        containsMaximum (Maximum {}) = True
        -- sanitize filename returns filename without forbidden file name characters
        sanitize :: String -> String
        sanitize [] = []
        sanitize (c1:c2:cs) | [c1,c2] == "<=" = "LEQ" ++ sanitize cs
        sanitize (c:cs) | c == ' ' = sanitize cs
        sanitize (c:cs) | c == '*' = "×" ++ sanitize cs
        sanitize (c:cs) | c == '<' = "LT" ++ sanitize cs
        sanitize (c:cs) = c : sanitize cs