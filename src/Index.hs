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
    deriving Show

instance Pretty Index where
    pretty (IndexVariable id) = id
    pretty (Number n) = show n
    pretty (Plus i j) = "(" ++ pretty i ++ " + " ++ pretty j ++ ")"
    pretty (Max i j) = "max(" ++ pretty i ++ ", " ++ pretty j ++ ")"


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

-- Natural lifting of well-formedness to traversable data structures
instance (Traversable t, Indexed a) => Indexed (t a) where
    wellFormed context x = let wellFormednesses = wellFormed context <$> x in and wellFormednesses



--- CLOSED INDEX TERM CONSTRAINT CHECKING --------------------------------------------------------------------------


eval ::  Index -> Int
eval (Number n) = n
eval (Plus i j) = eval i + eval j
eval (Max i j) = max (eval i) (eval j)
eval _ = error "Cannot evaluate index variable"

instance Eq Index where
    i == j = eval i == eval j

instance Ord Index where
    i <= j = eval i <= eval j



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

-- Converts an index relation to the corresponding SMTLIB syntax
embedRel :: IndexRel -> String
embedRel Eq = "="
embedRel Leq = "<="

-- Queries the SMT solver to check whether the given relation holds between the two indices
-- Returns () if the relation is valid, throws an SMTError otherwise
querySMTWithContext :: IndexRel -> IndexContext -> Index -> Index -> Either SMTError ()
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
            "unsat" -> return $ Right ()                        -- no counterexample found, so the constraint is valid
            "sat" -> return $ Left $ InvalidConstraint rel i j  -- counterexample found, so the constraint is invalid
            _ -> return $ Left $ UnknownConstraint rel i j      -- SMT solver failed to conclude anything
    
-- Θ ⊨ i = j (figs. 10,15)
checkEq :: IndexContext -> Index -> Index -> Either SMTError ()
checkEq = querySMTWithContext Eq

-- Θ ⊨ i ≤ j (figs. 12,15)
checkLeq :: IndexContext -> Index -> Index -> Either SMTError ()
checkLeq = querySMTWithContext Leq