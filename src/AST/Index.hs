{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
module AST.Index(
    Index(..),
    IndexVariableId,
    IndexContext,
    Indexed(..),
    checkEq,
    checkLeq,
    simplify
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
import Data.Map (Map)
import qualified Data.Map as Map


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

--- NEW VERSION (WIP)  ---------------------------------------------------------------------------------

--type IndexSubstitution = Map IndexVariableId Index
--
--class HasIndexVariables a where
--    freeIndexVariables :: a -> Set IndexVariableId
--    applyIndexSubstitution :: IndexSubstitution -> a -> a
--    mostGeneralIndexUnifier :: a -> a -> Maybe IndexSubstitution
--    isIndexClosed :: a -> Bool
--    isIndexClosed = Set.null . freeIndexVariables

--instance HasIndexVariables Index where
--    freeIndexVariables :: Index -> Set IndexVariableId
--    freeIndexVariables (IndexVariable id) = Set.singleton id
--    freeIndexVariables (Number _) = Set.empty
--    freeIndexVariables (Plus i j) = freeIndexVariables i `Set.union` freeIndexVariables j
--    freeIndexVariables (Max i j) = freeIndexVariables i `Set.union` freeIndexVariables j
--    freeIndexVariables (Mult i j) = freeIndexVariables i `Set.union` freeIndexVariables j
--    freeIndexVariables (Minus i j) = freeIndexVariables i `Set.union` freeIndexVariables j
--    freeIndexVariables (Maximum id i j) = freeIndexVariables i `Set.union` Set.delete id (freeIndexVariables j)
--    applyIndexSubstitution :: IndexSubstitution -> Index -> Index
--    applyIndexSubstitution _ (Number n) = Number n
--    applyIndexSubstitution sub i@(IndexVariable id) = Map.findWithDefault i id sub
--    applyIndexSubstitution sub (Plus i j) = Plus (applyIndexSubstitution sub i) (applyIndexSubstitution sub j)
--    applyIndexSubstitution sub (Max i j) = Max (applyIndexSubstitution sub i) (applyIndexSubstitution sub j)
--    applyIndexSubstitution sub (Mult i j) = Mult (applyIndexSubstitution sub i) (applyIndexSubstitution sub j)
--    applyIndexSubstitution sub (Minus i j) = Minus (applyIndexSubstitution sub i) (applyIndexSubstitution sub j)
--    applyIndexSubstitution sub (Maximum id i j) = Maximum id (applyIndexSubstitution (Map.delete id sub) i) (applyIndexSubstitution sub j)
--    mostGeneralIndexUnifier :: Index -> Index -> Maybe IndexSubstitution
--    mostGeneralIndexUnifier (IndexVariable id) i = return $ Map.singleton id i
--    mostGeneralIndexUnifier i (IndexVariable id) = return $ Map.singleton id i
--    mostGeneralIndexUnifier (Number n) (Number m) | n == m = return Map.empty
--    mostGeneralIndexUnifier (Plus i j) (Plus i' j') = do
--        sub1 <- mostGeneralIndexUnifier i i'
--        sub2 <- mostGeneralIndexUnifier (applyIndexSubstitution sub1 j) (applyIndexSubstitution sub1 j')
--        return $ sub1 `compose` sub2
--    mostGeneralIndexUnifier (Max i j) (Max i' j') = do
--        sub1 <- mostGeneralIndexUnifier i i'
--        sub2 <- mostGeneralIndexUnifier (applyIndexSubstitution sub1 j) (applyIndexSubstitution sub1 j')
--        return $ sub1 `compose` sub2
--    mostGeneralIndexUnifier (Mult i j) (Mult i' j') = do
--        sub1 <- mostGeneralIndexUnifier i i'
--        sub2 <- mostGeneralIndexUnifier (applyIndexSubstitution sub1 j) (applyIndexSubstitution sub1 j')
--        return $ sub1 `compose` sub2
--    mostGeneralIndexUnifier (Minus i j) (Minus i' j') = do
--        sub1 <- mostGeneralIndexUnifier i i'
--        sub2 <- mostGeneralIndexUnifier (applyIndexSubstitution sub1 j) (applyIndexSubstitution sub1 j')
--        return $ sub1 `compose` sub2
--    --mostGeneralIndexUnifier (Maximum id i j) (Maximum id' i' j') | id == id' = do
--
--assignVar :: IndexVariableId -> Index -> Maybe IndexSubstitution
--assignVar id (IndexVariable id') | id == id' = return Map.empty
--assignVar id b | id `Set.member` freeIndexVariables b = Nothing
--assignVar id b = return $ Map.singleton id b
--
--
--
--
--compose :: IndexSubstitution -> IndexSubstitution -> IndexSubstitution
--compose sub1 sub2 = Map.union (Map.map (applyIndexSubstitution sub1) sub2) sub1

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
checkEq :: Index -> Index -> Bool
checkEq i j = case (simplify i,simplify j) of
    (Number n, Number m) -> n == m
    (i',j') -> let theta = freeVariables i' `Set.union` freeVariables j'
        in querySMTWithContext theta $ Eq i' j'

-- Θ ⊨ i ≤ j (figs. 12,15)
checkLeq :: Index -> Index -> Bool
checkLeq i j = case (simplify i,simplify j) of
    (Number n, Number m) -> n <= m
    (i',j') -> let theta = freeVariables i' `Set.union` freeVariables j'
        in querySMTWithContext theta $ Leq i' j'