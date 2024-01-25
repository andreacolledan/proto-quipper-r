{-# LANGUAGE FlexibleInstances #-}
module Index(
    Index(..),
    IndexVariableId,
    IndexContext,
    Indexed(..),
    checkEq,
    checkLeq
) where
import Data.Set (Set)
import PrettyPrinter
import SMTLIB.Backends
import qualified SMTLIB.Backends.Process as Process
import qualified Data.ByteString.Lazy.Char8 as LBS
import Control.Monad
import Data.String (IsString(..))
import GHC.IO (unsafePerformIO)


type IndexVariableId = String

-- Syntax of indices: arithmetic expressions over natural numbers and index variables
-- (fig. 8)
data Index
    = IndexVariable IndexVariableId
    | Number Int
    | Plus Index Index
    | Max Index Index
    | Mult Index Index
    | Minus Index Index
    deriving (Show, Eq)

instance Pretty Index where
    pretty (IndexVariable id) = id
    pretty (Number n) = show n
    pretty (Plus i j) = "(" ++ pretty i ++ " + " ++ pretty j ++ ")"
    pretty (Max i j) = "max(" ++ pretty i ++ ", " ++ pretty j ++ ")"
    pretty (Mult i j) = "(" ++ pretty i ++ " * " ++ pretty j ++ ")"
    pretty (Minus i j) = "(" ++ pretty i ++ " - " ++ pretty j ++ ")"


-- Corresponds to Θ in the paper
type IndexContext = Set IndexVariableId

-- The class of datatypes that can be checked for well-formedness with respect to an index context
class Indexed a where
    wellFormed :: IndexContext -> a -> Bool

instance Indexed Index where
    wellFormed context (IndexVariable id) = id `elem` context
    wellFormed _ (Number _) = True
    wellFormed context (Plus i j) = wellFormed context i && wellFormed context j
    wellFormed context (Max i j) = wellFormed context i && wellFormed context j
    wellFormed context (Mult i j) = wellFormed context i && wellFormed context j
    wellFormed context (Minus i j) = wellFormed context i && wellFormed context j

-- Natural lifting of well-formedness to traversable data structures
instance (Traversable t, Indexed a) => Indexed (t a) where
    wellFormed context x = let wellFormednesses = wellFormed context <$> x in and wellFormednesses



--- CLOSED INDEX TERM CONSTRAINT CHECKING --------------------------------------------------------------------------

simplify :: Index -> Index
simplify (Number n) = Number n
simplify (Plus i j) = case (simplify i, simplify j) of
    (Number n, Number m) -> Number (n + m)
    (i',j') -> Plus i' j'
simplify (Max i j) = case (simplify i, simplify j) of
    (Number n, Number m) -> Number (max n m)
    (i',j') -> Max i' j'
simplify (Mult i j) = case (simplify i, simplify j) of
    (Number n, Number m) -> Number (n * m)
    (i',j') -> Mult i' j'   
simplify (Minus i j) = case (simplify i, simplify j) of
    (Number n, Number m) -> Number (n - m)
    (i',j') -> Minus i' j'
simplify (IndexVariable id) = IndexVariable id


--- SMT CONSTRAINT CHECKING (WIP) ---------------------------------------------------------------------------------


-- Allowed relations between indices
data IndexRel
    = Eq
    | Leq
    deriving Show

data SMTError
    = InvalidConstraint IndexRel Index Index
    | UnknownConstraint IndexRel Index Index
instance Show SMTError where
    show (InvalidConstraint rel i j) = show i ++ " " ++ show rel ++ " " ++ show j ++ " does not hold"
    show (UnknownConstraint rel i j) = "Could not prove " ++ show i ++ " " ++ show rel ++ " " ++ show j

-- Converts an index to the corresponding SMTLIB syntax
embedIndex :: Index -> String
embedIndex (IndexVariable id) = id
embedIndex (Number n) = show n
embedIndex (Plus i j) = "(+ " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Max i j) = "(max " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Mult i j) = "(* " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedIndex (Minus i j) = "(- " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"

-- Converts an index relation to the corresponding SMTLIB syntax
embedRel :: IndexRel -> String
embedRel Eq = "="
embedRel Leq = "<="

-- Queries the SMT solver to check whether the given relation holds between the two indices
-- Returns () if the relation is valid, throws an SMTError otherwise
querySMTWithContext :: IndexRel -> IndexContext -> Index -> Index -> Bool
querySMTWithContext rel theta i j = unsafePerformIO $ do
    Process.with Process.defaultConfig $ \handle -> do
        solver <- initSolver Queuing (Process.toBackend handle)
        command_ solver $ fromString "(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))"  --makes no sense to initialize this every time, find workaround
        -- for each index variable, initialize an unknown natural constant
        forM_ theta $ \id -> do
            command_ solver $ fromString $ "(declare-fun " ++ id ++ " () Int)"
            command_ solver $ fromString $ "(assert (>= " ++ id ++ " 0))"
        -- try to find a counterexample to the relation of the two indices
        command_ solver $ fromString $ "(assert (not (" ++ embedRel rel ++ " " ++ embedIndex i ++ " " ++ embedIndex j ++ ")))"
        resp <- command solver $ fromString "(check-sat)"
        case LBS.unpack resp of
            "unsat" -> return True  -- no counterexample found, so the constraint is valid
            "sat" -> return False   -- counterexample found, so the constraint is invalid
            _ -> return False       -- SMT solver failed to conclude anything
    
-- Θ ⊨ i = j (figs. 10,15)
checkEq :: IndexContext -> Index -> Index -> Bool
checkEq theta i j = case (simplify i,simplify j) of
    (Number n, Number m) -> n == m
    (i',j') -> querySMTWithContext Eq theta i' j'

-- Θ ⊨ i ≤ j (figs. 12,15)
checkLeq :: IndexContext -> Index -> Index -> Bool
checkLeq theta i j = case (simplify i,simplify j) of
    (Number n, Number m) -> n <= m
    (i',j') -> querySMTWithContext Leq theta i' j'