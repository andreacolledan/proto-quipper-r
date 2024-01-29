{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
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
import Control.Monad
import GHC.IO (unsafePerformIO)
import qualified Data.Set as Set
import System.IO
import System.Process as Proc
import Data.List (isPrefixOf)
import Control.Exception


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
    | Maximum IndexVariableId Index Index
    deriving (Show, Eq)

instance Pretty Index where
    pretty (IndexVariable id) = id
    pretty (Number n) = show n
    pretty (Plus i j) = "(" ++ pretty i ++ " + " ++ pretty j ++ ")"
    pretty (Max i j) = "max(" ++ pretty i ++ ", " ++ pretty j ++ ")"
    pretty (Mult i j) = "(" ++ pretty i ++ " * " ++ pretty j ++ ")"
    pretty (Minus i j) = "(" ++ pretty i ++ " - " ++ pretty j ++ ")"
    pretty (Maximum id i j) = "max[" ++ id ++ " < " ++ pretty i ++ "] " ++ pretty j


-- Corresponds to Θ in the paper
type IndexContext = Set IndexVariableId

-- The class of datatypes that bear indices. They can
--  - be checked for well-formedness with respect to an index context
--  - have an index variable within them replaced by an index
class Indexed a where
    freeVariables :: a -> Set IndexVariableId
    wellFormed :: IndexContext -> a -> Bool
    isub :: Index -> IndexVariableId -> a -> a

instance Indexed Index where
    freeVariables :: Index -> Set IndexVariableId
    freeVariables (IndexVariable id) = Set.singleton id
    freeVariables (Number _) = Set.empty
    freeVariables (Plus i j) = freeVariables i `Set.union` freeVariables j
    freeVariables (Max i j) = freeVariables i `Set.union` freeVariables j
    freeVariables (Mult i j) = freeVariables i `Set.union` freeVariables j
    freeVariables (Minus i j) = freeVariables i `Set.union` freeVariables j
    freeVariables (Maximum id i j) = Set.delete id (freeVariables i `Set.union` freeVariables j)
    wellFormed :: IndexContext -> Index -> Bool
    wellFormed context (IndexVariable id) = id `elem` context
    wellFormed _ (Number _) = True
    wellFormed context (Plus i j) = wellFormed context i && wellFormed context j
    wellFormed context (Max i j) = wellFormed context i && wellFormed context j
    wellFormed context (Mult i j) = wellFormed context i && wellFormed context j
    wellFormed context (Minus i j) = wellFormed context i && wellFormed context j
    wellFormed context (Maximum id i j) =
        notElem id context
        && wellFormed context i
        && wellFormed (Set.insert id context) j
    isub :: Index -> IndexVariableId -> Index -> Index
    isub _ _ (Number n) = Number n
    isub i id j@(IndexVariable id') = if id == id' then i else j
    isub i id (Plus j k) = Plus (isub i id j) (isub i id k)
    isub i id (Max j k) = Max (isub i id j) (isub i id k)
    isub i id (Mult j k) = Mult (isub i id j) (isub i id k)
    isub i id (Minus j k) = Minus (isub i id j) (isub i id k)
    isub i id (Maximum id' j k) = let j' = isub i id j in if id == id' then Maximum id' j' k else Maximum id' j' (isub i id k)

-- Natural lifting of well-formedness to traversable data structures
instance (Traversable t, Indexed a) => Indexed (t a) where
    freeVariables :: t a -> Set IndexVariableId
    freeVariables x = let freeVariableSets = freeVariables <$> x in foldr Set.union Set.empty freeVariableSets
    wellFormed :: IndexContext -> t a -> Bool
    wellFormed context x = let wellFormednesses = wellFormed context <$> x in and wellFormednesses
    isub :: Index -> IndexVariableId -> t a -> t a
    isub i id x = isub i id <$> x


--- SMT CONSTRAINT CHECKING (WIP) ---------------------------------------------------------------------------------

-- Simplifies an index expression, evaluating an expression until it is a number or a variable is encountered
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
simplify (Maximum id i j) = if id `notElem` freeVariables j then simplify j else
    case simplify i of
    Number 0 -> Number 0
    Number n -> let unrolling = foldr1 Max [isub (Number step) id j | step <- [1..n]] in simplify unrolling
    i' -> Maximum id i' j

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
embedIndex (Maximum id i j) = "(maximum (lambda ((" ++ id ++ " Int)) " ++ embedIndex j ++ ") " ++ embedIndex i ++ ")"

-- Converts an index relation to the corresponding SMTLIB syntax
embedRel :: IndexRel -> String
embedRel Eq = "="
embedRel Leq = "<="

-- Queries the SMT solver to check whether the given relation holds between the two indices
-- Returns () if the relation is valid, throws an SMTError otherwise
-- Queries are written to the file "query" and then run with the SMT solver cvc5
querySMTWithContext :: IndexRel -> IndexContext -> Index -> Index -> Bool
querySMTWithContext rel theta i j = unsafePerformIO $ do
    withFile "query" WriteMode $ \handle -> do
        hPutStrLn handle "(set-logic HO_ALL)" --higher order logic
        hPutStrLn handle "(set-option :fmf-fun true)" --enable recursive functions
        hPutStrLn handle "(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))"  --define max(x,y)
        hPutStrLn handle "(define-fun-rec maximum ((f (-> Int Int)) (j Int)) Int (ite (= j 0) 0 (max (f j) (maximum f (- j 1)))))" 
        forM_ theta $ \id -> do
            -- for each index variable, initialize an unknown natural variable
            hPutStrLn handle $ "(declare-const " ++ id ++ " Int)"
            hPutStrLn handle $ "(assert (>= " ++ id ++ " 0))"
        -- try to find a counterexample to the relation of the two indices
        hPutStrLn handle $ "(assert (not (" ++ embedRel rel ++ " " ++ embedIndex i ++ " " ++ embedIndex j ++ ")))"
        hPutStrLn handle "(check-sat)"
    -- run the SMT solver
    resp <- try $ readProcess "cvc5" ["./query"] []
    case resp of
        Left (SomeException _) -> return False
        Right resp -> if "unsat" `isPrefixOf` resp then return True else return False
    

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