module Solving.CVC5 (
  querySMTWithContext
  , withQueryFile
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
import GHC.IO.Handle.Types (Handle(..))

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
embedIndex (Minus i j) = "(minus " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Maximum {}) = error "Internal: maximum expression should have been desugared"

-- Converts an index relation to the corresponding SMTLIB symbol
embedConstraint :: IRel -> String
embedConstraint Eq = "="
embedConstraint Leq = "<="


-- desugar c desugars bounded maxima into fresh, appropriately constrained variables
-- it returns a pair (d, c') where d is a string containing the SMTLIB declarations and constraints
-- and c' is c where each occurrence of a bounded maximum is replaced by the appropriate variable
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
  -- the following declarations must occur before the constraints of the sub-terms
  let d0 = "; the following variables stand for the max value and argmax of " ++ pretty (Maximum id i j) ++ "\n"
        ++ "(declare-const " ++ maxName ++ " Int)\n"
        ++ "(assert (<= 0 " ++ maxName ++ "))\n"
        ++ "(declare-const " ++ argMaxName ++ " Int)\n"
        ++ "(assert (<= 0 " ++ argMaxName ++ "))\n"
  -- the following declrations must occur after the constraints of the sub-terms
  let d =  "; the following block ensures that " ++ maxName ++ " = " ++ pretty (Maximum id i j) ++ "\n"
        ++ "(assert (=> (<= " ++ embedIndex i' ++ " 0) (= " ++ maxName ++ " 0)))\n"
        ++ "(assert (=> (> " ++ embedIndex i' ++ " 0) (= " ++ maxName ++ " " ++ embedIndex j' ++ ")))\n"
        ++ "(assert (< " ++ argMaxName ++ " " ++ embedIndex i' ++ "))\n"
        ++ "(assert (forall ((_w Int)) (=> (and (<= 0 _w) (< _w " ++ embedIndex i' ++ ")) (<= " ++ embedIndex (isub (IndexVariable "_w") argMaxName j') ++ " " ++ embedIndex j' ++"))))\n"
  return (d0 ++ di ++ dj ++ d, IndexVariable maxName)

-- querySMTWithContext theta c queries the CVC5 solver to check if the index constraint
-- c holds for every possible assignment of its free variables
-- Returns true if the constraint holds, false otherwise
-- Throws an error if the solver does
querySMTWithContext :: Handle -> Constraint -> Bool
querySMTWithContext qfh c@(Constraint rel i j) = unsafePerformIO $ do
    hPutStrLn qfh $ "\n; PROVE " ++ pretty c
    hPutStrLn qfh "(push 1)"
    forM_ (ifv i `Set.union` ifv j) $ \id -> do
        -- for each free index variable in c, initialize an unknown natural variable:
        hPutStrLn qfh $ "(declare-const " ++ id ++ " Int)"
        hPutStrLn qfh $ "(assert (<= 0 " ++ id ++ "))"
    let (constraints, Constraint _ i' j') = desugar c
    hPutStr qfh constraints -- dump the constraints that desugar bounded maxima
    -- try to find a counterexample to c:
    hPutStrLn qfh "; assert the negation of the constraint to check if it is valid"
    hPutStrLn qfh $ "(assert (not (" ++ embedConstraint rel ++ " " ++ embedIndex i' ++ " " ++ embedIndex j' ++ ")))"
    hPutStrLn qfh "(check-sat)"
    hFlush qfh
    (ec, out, err) <- readProcessWithExitCode "cvc5" [handleName qfh, "-q", "--incremental", "--tlimit=5000"] [] --run CVC5 and get its stdout
    -- append the response to the query file as a comment:
    result <- case ec of
        ExitFailure _ -> do
            -- the solver threw an error
            hPutStrLn qfh $ "; Error thrown: " ++ show err
            error $ "CVC5 error: " ++ show err ++ " while solving " ++ pretty c
        ExitSuccess -> let response = last (words out) in
            if "unsat" `isPrefixOf` response then do
                -- cannot find a counterexample ==> the constraint is valid
                hPutStrLn qfh "; founds unsat (valid)"
                return True
            else if "sat" `isPrefixOf` response then do
                -- found a counterexample ==> the constraint is invalid
                hPutStrLn qfh "; found sat (invalid)"
                return False
            else do
                -- any other response is considered an error
                hPutStrLn qfh $ "; got response: " ++ response
                error $ "CVC5 unknown response: " ++ response ++ " while solving " ++ pretty c
    hPutStrLn qfh "(pop 1)"
    return result

withQueryFile :: FilePath -> (Handle -> IO r) -> IO r
withQueryFile filepath action = do
  let filename = takeFileName filepath
  let queryfilename = replaceExtension filename ".smt2"
  let queryfilepath = "queries" </> queryfilename
  withFile queryfilepath WriteMode $ \fh -> do
    hPutStrLn fh "(set-logic HO_ALL)" -- TODO this might be made less powerful, check
    hPutStrLn fh "(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x)) ; max(x,y)" -- define the max function
    hPutStrLn fh "(define-fun minus ((x Int) (y Int)) Int (ite (< x y) 0 (- x y))) ; minus(x,y)" -- define the minus function
    action fh

handleName :: Handle -> String
handleName (FileHandle file _ ) = file
handleName (DuplexHandle file _ _ ) = file
