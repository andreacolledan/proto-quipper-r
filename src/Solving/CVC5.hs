module Solving.CVC5 where


import Control.Exception
import Control.Monad
import Data.List (isPrefixOf)
import GHC.IO (unsafePerformIO)
import PrettyPrinter
import System.IO
import System.FilePath
import System.Process as Proc
import Index.AST

-- toSafeString i returns a representation of i that is safe to use as a valid filename
toSafeString :: Index -> String
toSafeString (IndexVariable id) = "" ++ id ++ ""
toSafeString (Number n) = "" ++ show n ++ ""
toSafeString (Plus i j) = "" ++ toSafeString i ++ "PLUS" ++ toSafeString j ++ ""
toSafeString (Max i j) = "MAX" ++ toSafeString i ++ "AND" ++ toSafeString j ++ ""
toSafeString (Mult i j) = "" ++ toSafeString i ++ "TIMES" ++ toSafeString j ++ ""
toSafeString (Minus i j) = "" ++ toSafeString i ++ "MINUS" ++ toSafeString j ++ ""
toSafeString (Maximum id i j) = "MAX" ++ id ++ "LT" ++ toSafeString i ++ "" ++ toSafeString j

makeMaximumName :: Index -> Index -> String
makeMaximumName i j = "max_" ++ toSafeString i ++ "_" ++ toSafeString j

makeArgMaximumName :: Index -> Index -> String
makeArgMaximumName i j = "arg" ++ makeMaximumName i j

-- Converts an index expression to and SMTLIB arithmetical expression
embedIndex :: Index -> String
embedIndex (IndexVariable id) = id
embedIndex (Number n) = show n
embedIndex (Plus i j) = "(+ " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Max i j) = "(max " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Mult i j) = "(* " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Minus i j) = "(- " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Maximum _ i j) = makeMaximumName i j

-- Converts an index relation to the corresponding SMTLIB symbol
embedConstraint :: IRel -> String
embedConstraint Eq = "="
embedConstraint Leq = "<="

defineMaxima :: Index -> String
defineMaxima (IndexVariable _) = ""
defineMaxima (Number _) = ""
defineMaxima (Plus i j) = defineMaxima i ++ defineMaxima j
defineMaxima (Max i j) = defineMaxima i ++ defineMaxima j
defineMaxima (Mult i j) = defineMaxima i ++ defineMaxima j
defineMaxima (Minus i j) = defineMaxima i ++ defineMaxima j
defineMaxima (Maximum id i j) = defineMaxima i ++ defineMaxima j ++ --define maxima bottom-up
    let maxName = makeMaximumName i j
        argMaxName = makeArgMaximumName i j
    in
        "(declare-const " ++ maxName ++ " Int)\n" ++
        "(declare-const " ++ argMaxName ++ " Int)\n" ++
        "(assert (=> (<= " ++ embedIndex i ++ " 0) (= " ++ maxName ++ " 0)))\n" ++
        "(assert (=> (> " ++ embedIndex i ++ " 0) (= " ++ maxName ++ " " ++ embedIndex (isub (IndexVariable argMaxName) id j) ++ ")))\n" ++
        "(assert (<= 0 " ++ argMaxName ++ "))\n" ++
        "(assert (< " ++ argMaxName ++ " " ++ embedIndex i ++ "))\n" ++
        "(assert (forall ((_w Int)) (=> (and (<= 0 _w) (< _w " ++ embedIndex i ++ ")) (<= " ++ embedIndex (isub (IndexVariable "_w") id j) ++ " " ++ embedIndex (isub (IndexVariable argMaxName) id j) ++"))))\n"

-- querySMTWithContext theta c queries the CVC5 solver to check if the index constraint
-- c holds for every natural value of the index variables in theta.
-- Returns true if the constraint holds, false otherwise or if the solver throws an error.
querySMTWithContext :: IndexContext -> Constraint -> Bool
querySMTWithContext theta c@(Constraint rel i j) = unsafePerformIO $ do
    withFile queryFile WriteMode $ \handle -> do
        hPutStrLn handle $ "; " ++ pretty c
        hPutStrLn handle "(set-logic HO_ALL)"
        hPutStrLn handle "(set-option :fmf-fun true)" --enable recursive functions
        hPutStrLn handle "(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))"  --define max(x,y)
        forM_ theta $ \id -> do
            -- for each index variable, initialize an unknown natural variable
            hPutStrLn handle $ "(declare-const " ++ id ++ " Int)"
            hPutStrLn handle $ "(assert (>= " ++ id ++ " 0))"
        hPutStr handle $ defineMaxima i
        hPutStr handle $ defineMaxima j
        -- try to find a counterexample to the relation of the two indices
        hPutStrLn handle $ "(assert (not (" ++ embedConstraint rel ++ " " ++ embedIndex i ++ " " ++ embedIndex j ++ ")))"
        hPutStrLn handle "(check-sat)"
    resp <- try $ readProcess "cvc5" [queryFile, "-q", "--tlimit=5000"] [] --run CVC5 and get its stdout
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
        queryFile = let filename = show rel ++ "(" ++ toSafeString i ++ "AND" ++ toSafeString j ++ ")"
            in "queries" </> filename <.> "smt2"
