module Solving.CVC5
  ( querySMTWithContext,
    withSolver,
    SolverHandle,
  )
where

import Control.Monad
import Control.Monad.State (MonadState (..), State, evalState)
import qualified Data.Set as Set
import GHC.IO.Handle.Types (Handle (..))
import Index.AST
import PrettyPrinter
import System.Process as Proc
import System.IO
import System.FilePath

--- SMT SOLVER (CVC5) MODULE ------------------------------------------------------------
---
--- This module contains the logic to communicate with the CVC5 SMT solver.
--- SMT queries from the same program are all written to the same file, which is then
--- passed to the solver. The solver's response is then read from the same file.
-----------------------------------------------------------------------------------------

-- | @toSafeString i@ returns a string representation of the index expression @i@ that is safe to use as a file name.
toSafeString :: Index -> String
toSafeString (IndexVariable id) = id
toSafeString (Number n) = show n
toSafeString (Plus i j) = toSafeString i ++ "PLUS" ++ toSafeString j
toSafeString (Max i j) = "MAX" ++ toSafeString i ++ "AND" ++ toSafeString j
toSafeString (Mult i j) = toSafeString i ++ "TIMES" ++ toSafeString j
toSafeString (Minus i j) = toSafeString i ++ "MINUS" ++ toSafeString j
toSafeString (Maximum id i j) = "MAX" ++ id ++ "LT" ++ toSafeString i ++ " " ++ toSafeString j

-- | @embedIndex i@ returns a string representing index expression @i@ in SMTLIB format.
embedIndex :: Index -> String
embedIndex (IndexVariable id) = id
embedIndex (Number n) = show n
embedIndex (Plus i j) = "(+ " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Max i j) = "(max " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Mult i j) = "(* " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Minus i j) = "(minus " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Maximum {}) = error "Internal: maximum expression should have been desugared"

-- | @embedConstraint rel@ returns a string representing the relation @rel@ in SMTLIB format.
--
-- >>> embedConstraint Eq
-- "="
--
-- >>> embedConstraint Leq
-- "<="
embedConstraint :: IRel -> String
embedConstraint Eq = "="
embedConstraint Leq = "<="

-- | @desugarMaxima c@ desugars all bounded maxima in the constraint @c@ into fresh, appropriately constrained variables.
-- It returns a pair @(d, c')@ where @d@ is a string containing the applicable SMTLIB declarations and constraints
-- that must precede the main query in the smtlib file and @c'@ is @c@ where each occurrence of a bounded maximum
-- is replaced by the corresponding newly introduced variable.
desugarMaxima :: Constraint -> (String, Constraint)
desugarMaxima (Constraint rel i j) = flip evalState 0 $ do
  (di, i') <- goDesugarMaxima i
  (dj, j') <- goDesugarMaxima j
  return (di ++ dj, Constraint rel i' j')

goDesugarMaxima :: Index -> State Int (String, Index)
goDesugarMaxima (IndexVariable id) = return ("", IndexVariable id)
goDesugarMaxima (Number n) = return ("", Number n)
goDesugarMaxima (Plus i j) = do
  (di, i') <- goDesugarMaxima i
  (dj, j') <- goDesugarMaxima j
  return (di ++ dj, Plus i' j')
goDesugarMaxima (Max i j) = do
  (di, i') <- goDesugarMaxima i
  (dj, j') <- goDesugarMaxima j
  return (di ++ dj, Max i' j')
goDesugarMaxima (Mult i j) = do
  (di, i') <- goDesugarMaxima i
  (dj, j') <- goDesugarMaxima j
  return (di ++ dj, Mult i' j')
goDesugarMaxima (Minus i j) = do
  (di, i') <- goDesugarMaxima i
  (dj, j') <- goDesugarMaxima j
  return (di ++ dj, Minus i' j')
goDesugarMaxima (Maximum id i j) = do
  count <- get
  put $ count + 1
  let maxName = "_max" ++ show count
  let argMaxName = "_argmax" ++ show count
  (di, i') <- goDesugarMaxima i
  (dj, j') <- goDesugarMaxima (isub (IndexVariable argMaxName) id j)
  -- the following declarations must occur before the constraints of the sub-terms
  let d0 =
        "; the following variables stand for the max value and argmax of " ++ pretty (Maximum id i j) ++ "\n"
          ++ "(declare-const " ++ maxName ++ " Int)\n"
          ++ "(assert (<= 0 " ++ maxName ++ "))\n"
          ++ "(declare-const " ++ argMaxName ++ " Int)\n"
          ++ "(assert (<= 0 " ++ argMaxName ++ "))\n"
  -- the following declrations must occur after the constraints of the sub-terms
  let d =
        "; the following block ensures that " ++ maxName ++ " = " ++ pretty (Maximum id i j) ++ "\n"
          ++ "(assert (=> (<= " ++ embedIndex i' ++ " 0) (= " ++ maxName ++ " 0)))\n"
          ++ "(assert (=> (> " ++ embedIndex i' ++ " 0) (= " ++ maxName ++ " " ++ embedIndex j' ++ ")))\n"
          ++ "(assert (< " ++ argMaxName ++ " " ++ embedIndex i' ++ "))\n"
          ++ "(assert (forall ((_w Int)) (=> "
            ++ "(and (<= 0 _w) (< _w " ++ embedIndex i' ++ "))"
            ++ "(<= " ++ embedIndex (isub (IndexVariable "_w") argMaxName j') ++ " " ++ embedIndex j' ++ "))))\n"
  return (d0 ++ di ++ dj ++ d, IndexVariable maxName)

-- | @querySMTWithContext qfh c@ queries the CVC5 solver to check if the constraint @c@ holds for every possible assignment of its free variables.
-- It returns @True@ if the constraint holds, @False@ otherwise or if an error occurs in the interaction with the solver.
-- The handle @qfh@ is used to communicate with the SMT solver.
querySMTWithContext :: SolverHandle -> Constraint -> IO Bool
querySMTWithContext (sin, sout) c@(Constraint rel i j) = do
  hPutStrLn sin $ "\n; PROVE " ++ pretty c
  hPutStrLn sin "(push 1)"
  forM_ (ifv i `Set.union` ifv j) $ \id -> do
    -- for each free index variable in c, initialize an unknown natural variable:
    hPutStrLn sin $ "(declare-const " ++ id ++ " Int)"
    hPutStrLn sin $ "(assert (<= 0 " ++ id ++ "))"
  let (constraints, Constraint _ i' j') = desugarMaxima c
  hPutStr sin constraints -- dump the constraints that desugar bounded maxima
  -- try to find a counterexample to c:
  hPutStrLn sin "; assert the negation of the constraint to check if it is valid"
  hPutStrLn sin $ "(assert (not (" ++ embedConstraint rel ++ " " ++ embedIndex i' ++ " " ++ embedIndex j' ++ ")))"
  hPutStrLn sin "(check-sat)"
  hFlush sin
  resp <- hGetLine sout
  -- append the response to the query file as a comment:
  result <- case resp of -- response is sat/unsat for each query so far
    "unsat" -> do
      -- cannot find a counterexample ==> the constraint is valid
      hPutStrLn sin "; founds unsat (valid)"
      return True
    "sat" -> do
      -- found a counterexample ==> the constraint is invalid
      hPutStrLn sin "; found sat (invalid)"
      return False
    [] -> do
      -- empty response is considered an error
      hPutStrLn sin "; got empty response"
      error $ "CVC5 empty response while solving " ++ pretty c
    other -> do
      -- any other response is considered an error
      hPutStrLn sin $ "; got response: " ++ other
      error $ "CVC5 unknown response: " ++ other ++ " while solving " ++ pretty c
  hPutStrLn sin "(pop 1)"
  return result

-- | @SolverHandle@ is a pair of handles to communicate with the SMT solver.
-- The first handle is used to send queries to the solver, the second handle is used to read the solver's responses.
type SolverHandle = (Handle, Handle)

-- | @withSolver filepath action@ initializes a new SMT solver process and runs the action @action@ with the solver handle.
-- The file @filepath@ is used to store the queries and responses of the solver.
withSolver :: FilePath -> (SolverHandle -> IO r) -> IO r
withSolver filepath action = do
  let filename = takeFileName filepath
  let queryfilename = replaceExtension filename ".smt2"
  let queryfilepath = "queries" </> queryfilename
  p@(Just sIn, Just sOut, _, _) <- createProcess $ (shell $ "tee " ++ queryfilepath ++ " | cvc5 -q --incremental --interactive"){
    std_in = CreatePipe,
    std_out = CreatePipe
  }
  hPutStrLn sIn "(set-logic HO_ALL)" -- TODO this might be made less powerful, check
  hPutStrLn sIn "(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x)) ; max(x,y)" -- define the max function
  hPutStrLn sIn "(define-fun minus ((x Int) (y Int)) Int (ite (< x y) 0 (- x y))) ; minus(x,y)" -- define the minus function
  outcome <- action (sIn, sOut)
  cleanupProcess p
  return outcome


-- | @handleName h@ returns the name of the file associated with the handle @h@.
handleName :: Handle -> String
handleName (FileHandle file _) = file
handleName (DuplexHandle file _ _) = file
  
