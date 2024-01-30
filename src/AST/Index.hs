{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module AST.Index(
    Index(..),
    IndexVariableId,
    IndexContext,
    Indexed(..),
    checkEq,
    checkLeq
) where

import Control.Exception
import Control.Monad
import Data.List (isPrefixOf)
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.IO (unsafePerformIO)
import PrettyPrinter
import System.IO
import System.FilePath
import System.Process as Proc


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


--- SMT CONSTRAINT CHECKING ---------------------------------------------------------------------------------

nonDecreasingIn :: Index -> IndexVariableId -> Bool
nonDecreasingIn (IndexVariable _) _ = True
nonDecreasingIn (Number _) _ = True
nonDecreasingIn (Plus i j) id = i `nonDecreasingIn` id && j `nonDecreasingIn` id
nonDecreasingIn (Max i j) id = i `nonDecreasingIn` id && j `nonDecreasingIn` id
nonDecreasingIn (Mult i j) id = i `nonDecreasingIn` id && j `nonDecreasingIn` id
nonDecreasingIn (Minus i j) id = i `nonDecreasingIn` id && j `nonIncreasingIn` id
nonDecreasingIn (Maximum id' i j) id | id /= id' =
    i `nonDecreasingIn` id && j `nonDecreasingIn` id
    || i `nonDecreasingIn` id && j `nonDecreasingIn` id'
nonDecreasingIn _ _ = False

nonIncreasingIn :: Index -> IndexVariableId -> Bool
nonIncreasingIn (IndexVariable id') id = id /= id'
nonIncreasingIn (Number _) _ = True
nonIncreasingIn (Plus i j) id = i `nonIncreasingIn` id && j `nonIncreasingIn` id
nonIncreasingIn (Max i j) id = i `nonIncreasingIn` id && j `nonIncreasingIn` id
nonIncreasingIn (Mult i j) id = i `nonIncreasingIn` id && j `nonIncreasingIn` id
nonIncreasingIn (Minus i j) id = i `nonIncreasingIn` id && j `nonDecreasingIn` id
nonIncreasingIn (Maximum id' i j) id | id /= id' =
    i `nonIncreasingIn` id && j `nonIncreasingIn` id
    || i `nonIncreasingIn` id && j `nonDecreasingIn` id'
nonIncreasingIn _ _ = False

stableIn :: Index -> IndexVariableId -> Bool
stableIn i id = i `nonDecreasingIn` id && i `nonIncreasingIn` id


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
    (i',j') | i' == j' -> Number 0
    (i',j') -> Minus i' j'
simplify (IndexVariable id) = IndexVariable id
simplify (Maximum id i j) = case simplify i of
    -- if upper bound is 0, the range is empty and the maximum defaults to 0
    Number 0 -> Number 0
    -- if the upper bound is known, unroll the maximum into a sequence of binary maxima
    Number n -> let unrolling = foldr1 Max [isub (Number step) id j | step <- [0..n-1]] in simplify unrolling
    -- if the upper bound is unknown, simplify the body of the maximum and...
    i' -> let j' = simplify j in
        -- if the body of does not mention id, then just return the body
        if id `notElem` freeVariables j' then j'
        -- if the body does not increase in i, then return the body at id=0
        else if j' `nonIncreasingIn` id then simplify $ isub (Number 0) id j'
        -- if the body of the maximum does not decrease in i, then return the body at id=i-1
        else if j' `nonDecreasingIn` id then simplify $ isub (Minus i' (Number 1)) id j'
        --otherwise return the simplified term and pray that an SMT solver will figure it out (it won't)
        else Maximum id i' j'
    

-- Allowed relations between indices
data Constraint
    = Eq Index Index
    | Leq Index Index
    deriving Show

instance Pretty Constraint where
    pretty (Eq i j) = pretty i ++ " = " ++ pretty j
    pretty (Leq i j) = pretty i ++ " ≤ " ++ pretty j

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
embedConstraint :: Constraint -> String
embedConstraint (Eq i j) = "(= " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"
embedConstraint (Leq i j) = "(<= " ++ embedIndex i ++ " " ++ embedIndex j ++ ")"

-- Queries the SMT solver to check whether the given relation holds between the two indices
-- Returns () if the relation is valid, throws an SMTError otherwise
querySMTWithContext :: IndexContext -> Constraint -> Bool
querySMTWithContext theta c = unsafePerformIO $ do
    withFile queryFile WriteMode $ \handle -> do
        hPutStrLn handle $ "; " ++ pretty c
        when maximaInvolved $ do
            hPutStrLn handle "(set-logic HO_ALL)"
            hPutStrLn handle "(set-option :fmf-fun true)" --enable recursive functions
            hPutStrLn handle "(set-option :full-saturate-quant true)"
            hPutStrLn handle "(set-option :fmf-mbqi fmc)"
            hPutStrLn handle "(set-option :nl-cov true)"
            hPutStrLn handle "(set-option :nl-ext-tplanes-interleave true)"
        hPutStrLn handle "(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))"  --define max(x,y)
        when maximaInvolved $
            hPutStrLn handle "(define-fun-rec maximum ((f (-> Int Int)) (j Int)) Int (ite (= j 0) 0 (max (f j) (maximum f (- j 1)))))"
        forM_ theta $ \id -> do
            -- for each index variable, initialize an unknown natural variable
            hPutStrLn handle $ "(declare-const " ++ id ++ " Int)"
            hPutStrLn handle $ "(assert (>= " ++ id ++ " 0))"
        -- try to find a counterexample to the relation of the two indices
        hPutStrLn handle $ "(assert (not " ++ embedConstraint c ++ "))"
        hPutStrLn handle "(check-sat)"
    -- run the SMT solver
    resp <- try $ readProcess "cvc5" [queryFile, "-q"] []
    withFile queryFile AppendMode $ \handle -> do
        case resp of
            Left (SomeException e) -> do
                hPutStrLn handle $ "; Error thrown: " ++ show e
                return False
            Right resp -> if "unsat" `isPrefixOf` resp then do
                    hPutStrLn handle "; founds unsat (valid)"
                    return True
                else if "sat" `isPrefixOf` resp then do
                    hPutStrLn handle "; found sat (invalid)"
                    return False
                else do
                    hPutStrLn handle $ "; got response: " ++ resp
                    return False
    where
        queryFile :: FilePath
        queryFile = "queries" </> sanitize (pretty c) <.> "smt2"
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
        sanitize :: String -> String
        sanitize [] = []
        sanitize (c1:c2:cs) | [c1,c2] == "<=" = "LEQ" ++ sanitize cs
        sanitize (c:cs) | c == ' ' = sanitize cs
        sanitize (c:cs) | c == '*' = "×" ++ sanitize cs
        sanitize (c:cs) | c == '<' = "LT" ++ sanitize cs
        sanitize (c:cs) = c : sanitize cs

-- Θ ⊨ i = j (figs. 10,15)
checkEq :: IndexContext -> Index -> Index -> Bool
checkEq theta i j = case (simplify i,simplify j) of
    (Number n, Number m) -> n == m
    (i',j') -> querySMTWithContext theta $ Eq i' j'

-- Θ ⊨ i ≤ j (figs. 12,15)
checkLeq :: IndexContext -> Index -> Index -> Bool
checkLeq theta i j = case (simplify i,simplify j) of
    (Number n, Number m) -> n <= m
    (i',j') -> querySMTWithContext theta $ Leq i' j'


---- Queries the SMT solver to check whether the given relation holds between the two indices
---- Returns () if the relation is valid, throws an SMTError otherwise
--querySMTWithContext' :: IndexRel -> IndexContext -> Index -> Index -> Bool
--querySMTWithContext' rel theta i j = unsafePerformIO $ do
--    withFile queryFile WriteMode $ \handle -> do
--        hPutStrLn handle $ "; " ++ pretty i ++ " " ++ embedRel rel ++ " " ++ pretty j
--        when maximaInvolved $ do
--            hPutStrLn handle "(set-logic HO_ALL)"
--            hPutStrLn handle "(set-option :fmf-fun true)" --enable recursive functions
--            hPutStrLn handle "(set-option :full-saturate-quant true)"
--            hPutStrLn handle "(set-option :fmf-mbqi fmc)"
--            hPutStrLn handle "(set-option :cegqi-inf-int true)"
--            hPutStrLn handle "(set-option :nl-cov true)"
--            hPutStrLn handle "(set-option :cegqi true)"
--            hPutStrLn handle "(set-option :dt-stc-ind true)"
--            hPutStrLn handle "(set-option :conjecture-gen true)"
--            hPutStrLn handle "(set-option :cegis-sample trust)"
--            hPutStrLn handle "(set-option :quant-ind true)"
--            hPutStrLn handle "(set-option :nl-ext-tplanes-interleave true)"
--        hPutStrLn handle "(define-fun max ((x Int) (y Int)) Int (ite (< x y) y x))"  --define max(x,y)
--        when maximaInvolved $
--            hPutStrLn handle "(define-fun-rec maximum ((f (-> Int Int)) (j Int)) Int (ite (= j 0) 0 (max (f j) (maximum f (- j 1)))))"
--        -- try to find a counterexample to the relation of the two indices
--        hPutStrLn handle "(assert (forall ("
--        forM_ theta $ \id -> do
--            -- for each index variable, initialize an unknown natural variable
--            hPutStrLn handle $ "(" ++ id ++ " Int)"
--        hPutStrLn handle ") (=> (and "
--        forM_ theta $ \id -> do
--            -- for each index variable, initialize an unknown natural variable
--            hPutStrLn handle $ "(>= " ++ id ++ " 0)"
--        hPutStrLn handle $ ") (" ++ embedRel rel ++ " " ++ embedIndex i ++ " " ++ embedIndex j ++ "))))"
--        hPutStrLn handle "(check-sat)"
--    -- run the SMT solver
--    resp <- try $ readProcess "cvc5" [queryFile, "-q"] []
--    withFile queryFile AppendMode $ \handle -> do
--        case resp of
--            Left (SomeException e) -> do
--                hPutStrLn handle $ "; Error thrown: " ++ show e
--                return False
--            Right resp -> if "sat" `isPrefixOf` resp then do
--                    hPutStrLn handle "; founds sat (valid)"
--                    return True
--                else if "unsat" `isPrefixOf` resp then do
--                    hPutStrLn handle "; found unsat (invalid)"
--                    return False
--                else do
--                    hPutStrLn handle $ "; got response: " ++ resp
--                    return False
--    where
--        queryFile :: FilePath
--        queryFile = "queries" </> sanitize (pretty i ++ " " ++ embedRel rel ++ " " ++ pretty j) <.> "smt2"
--        maximaInvolved :: Bool
--        maximaInvolved = containsMaximum i || containsMaximum j
--        containsMaximum :: Index -> Bool
--        containsMaximum (IndexVariable _) = False
--        containsMaximum (Number _) = False
--        containsMaximum (Plus i j) = containsMaximum i || containsMaximum j
--        containsMaximum (Max i j) = containsMaximum i || containsMaximum j
--        containsMaximum (Mult i j) = containsMaximum i || containsMaximum j
--        containsMaximum (Minus i j) = containsMaximum i || containsMaximum j
--        containsMaximum (Maximum {}) = True
--        sanitize :: String -> String
--        sanitize [] = []
--        sanitize (c1:c2:cs) | [c1,c2] == "<=" = "LEQ" ++ sanitize cs
--        sanitize (c:cs) | c == ' ' = sanitize cs
--        sanitize (c:cs) | c == '*' = "×" ++ sanitize cs
--        sanitize (c:cs) | c == '<' = "LT" ++ sanitize cs
--        sanitize (c:cs) = c : sanitize cs