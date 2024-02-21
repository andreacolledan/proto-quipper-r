module Solving.CVC5 (
  querySMTWithContext
) where


import Control.Monad
import Data.List (isPrefixOf)
import GHC.IO (unsafePerformIO)
import PrettyPrinter
import System.IO
import System.FilePath
import System.Process as Proc
import Index.AST
import Control.Monad.State (evalState, State, MonadState (..))
import qualified Data.Set as Set
import GHC.IO.Exception (ExitCode(ExitSuccess, ExitFailure))

-- toSafeString i returns a representation of i that is safe to use as a valid filename
toSafeString :: Index -> String
toSafeString (IndexVariable id) = id
toSafeString (Number n) = show n
toSafeString (Plus i j) = toSafeString i ++ "PLUS" ++ toSafeString j 
toSafeString (Max i j) = "MAX" ++ toSafeString i ++ "AND" ++ toSafeString j 
toSafeString (Mult i j) = toSafeString i ++ "TIMES" ++ toSafeString j 
toSafeString (Minus i j) = toSafeString i ++ "MINUS" ++ toSafeString j 
toSafeString (Maximum id i j) = "MAX" ++ id ++ "LT" ++ toSafeString i ++ " " ++ toSafeString j

-- Converts an index expression to and SMTLIB arithmetical expression
embedIndex :: Index -> String
embedIndex (IndexVariable id) = id
embedIndex (Number n) = show n
embedIndex (Plus i j) = "(+ " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Max i j) = "(max " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Mult i j) = "(* " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Minus i j) = "(- " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Maximum {}) = error "Internal: maximum expression should have been desugared"

-- Converts an index relation to the corresponding SMTLIB symbol
embedConstraint :: IRel -> String
embedConstraint Eq = "="
embedConstraint Leq = "<="

desugar :: Constraint -> (String, Constraint)
desugar (Constraint rel i j) = flip evalState 0 $ do
    (di, i') <- desugar' i
    (dj, j') <- desugar' j
    return (di ++ dj, Constraint rel i' j')
desugar' :: Index -> State Int (String, Index)
desugar' (IndexVariable id) = return ("", IndexVariable id)
desugar' (Number n) = return ("", Number n)
desugar' (Plus i j) = do
  (di, i') <- desugar' i
  (dj, j') <- desugar' j
  return (di ++ dj, Plus i' j')
desugar' (Max i j) = do
  (di, i') <- desugar' i
  (dj, j') <- desugar' j
  return (di ++ dj, Max i' j')
desugar' (Mult i j) = do
  (di, i') <- desugar' i
  (dj, j') <- desugar' j
  return (di ++ dj, Mult i' j')
desugar' (Minus i j) = do
  (di, i') <- desugar' i
  (dj, j') <- desugar' j
  return (di ++ dj, Minus i' j')
desugar' (Maximum id i j) = do
  count <- get
  put $ count+1
  let maxName = "_max" ++ show count
  let argMaxName = "_argmax" ++ show count
  (di, i') <- desugar' i
  (dj, j') <- desugar' (isub (IndexVariable argMaxName) id j)
  let d0 = "(declare-const " ++ maxName ++ " Int)\n"
        ++ "(assert (<= 0 " ++ maxName ++ "))\n"
        ++ "(declare-const " ++ argMaxName ++ " Int)\n"
        ++ "(assert (<= 0 " ++ argMaxName ++ "))\n"
  let d =  "; the following block ensures that " ++ maxName ++ " = " ++ pretty (Maximum id i j) ++ "\n"
        ++ "(assert (=> (<= " ++ embedIndex i' ++ " 0) (= " ++ maxName ++ " 0)))\n"
        ++ "(assert (=> (> " ++ embedIndex i' ++ " 0) (= " ++ maxName ++ " " ++ embedIndex j' ++ ")))\n"
        ++ "(assert (< " ++ argMaxName ++ " " ++ embedIndex i' ++ "))\n"
        ++ "(assert (forall ((_w Int)) (=> (and (<= 0 _w) (< _w " ++ embedIndex i' ++ ")) (<= " ++ embedIndex (isub (IndexVariable "_w") argMaxName j') ++ " " ++ embedIndex j' ++"))))\n"
  return (d0 ++ di ++ dj ++ d, IndexVariable maxName)

-- querySMTWithContext theta c queries the CVC5 solver to check if the index constraint
-- c holds for every natural value of the index variables in theta.
-- Returns true if the constraint holds, false otherwise or if the solver throws an error.
querySMTWithContext :: Constraint -> Bool
querySMTWithContext c@(Constraint rel i j) = unsafePerformIO $ do
    withFile queryFile WriteMode $ \handle -> do
        hPutStrLn handle $ "; PROVE " ++ pretty c
        hPutStrLn handle "(set-logic HO_ALL)"
        hPutStrLn handle "(set-option :fmf-fun true)" --enable recursive functions
        hPutStrLn handle "(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x)) ; max(x,y)"
        let (constraints, Constraint _ i' j') = desugar c
        forM_ (ifv i `Set.union` ifv j) $ \id -> do
            -- for each index variable, initialize an unknown natural variable
            hPutStrLn handle $ "(declare-const " ++ id ++ " Int)"
            hPutStrLn handle $ "(assert (<= 0 " ++ id ++ "))"
        hPutStr handle constraints
        -- try to find a counterexample to the relation of the two indices
        hPutStrLn handle $ "(assert (not (" ++ embedConstraint rel ++ " " ++ embedIndex i' ++ " " ++ embedIndex j' ++ ")))"
        hPutStrLn handle "(check-sat)"
    (ec, out, err) <- readProcessWithExitCode "cvc5" [queryFile, "-q", "--tlimit=5000"] [] --run CVC5 and get its stdout
    -- append the response to the query file as a comment
    withFile queryFile AppendMode $ \handle -> do
        case ec of
            ExitFailure _ -> do
                -- the solver threw an error
                hPutStrLn handle $ "; Error thrown: " ++ show out
                error $ "CVC5 error: " ++ show err
            ExitSuccess -> if "unsat" `isPrefixOf` out then do
                    -- cannot find a counterexample ==> the constraint is valid
                    hPutStrLn handle "; founds unsat (valid)"
                    return True
                else if "sat" `isPrefixOf` out then do
                    -- found a counterexample ==> the constraint is invalid
                    hPutStrLn handle "; found sat (invalid)"
                    return False
                else do
                    -- any other response is considered an error
                    hPutStrLn handle $ "; got response: " ++ out
                    error $ "CVC5 unknown response: " ++ out
    where
        -- query files are stored in the queries/ subdirectory
        queryFile :: FilePath
        queryFile = let filename = show rel ++ "(" ++ toSafeString i ++ "AND" ++ toSafeString j ++ ")"
            in "queries" </> filename <.> "smt2"
