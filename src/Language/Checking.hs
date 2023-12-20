module Language.Checking where
import Language.Syntax
import Data.Map (Map)
import qualified Data.Map as Map
import Circuit.Checking
import Wire.Checking
import Index
import Control.Monad.State.Lazy
import Control.Monad.Except
import Circuit.Syntax
import Control.Monad (when)

-- Corresponds to Γ in the paper
type TypingContext = Map VariableId Type

embed :: StateT LabelContext (Either String) a -> StateT (IndexContext, TypingContext, LabelContext) (Either String) a
embed comp = do
    (ic, tc, lc) <- get
    case runStateT comp lc of
        Left err -> throwError err
        Right (x,remainingLc) -> put (ic, tc, remainingLc) >> return x

checkValueType :: Value -> Type -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Bool
checkValueType (Bundle l) t = case t of 
    BundleType t -> embed $ checkBundleType l t
    _ -> throwError $ "Cannot give type " ++ show t ++ " to a bundle of wires"
checkValueType (BoxedCircuit l c k) t = case t of
    Circ i t u -> if Number (width c) <= i 
        then lift $ do
        (ql, qk) <- inferCircuitSignature c
        left <- evalStateT (checkBundleType l t) ql
        right <- evalStateT (checkBundleType k u) qk
        return $ left && right
        else throwError $ "Cannot conclude width (" ++ show c ++ ") <= " ++ show i
    _ -> throwError $ "Cannot give type " ++ show t ++ " to a boxed circuit"

inferValueType :: Value -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Type
inferValueType (Bundle l) = do
    t <- embed $ inferBundleType l
    return $ BundleType t
inferValueType (BoxedCircuit l c k) = lift $ do
        (ql, qk) <- inferCircuitSignature c
        t <- evalStateT (inferBundleType l) ql
        u <- evalStateT (inferBundleType k) qk
        return $ Circ (Number $ width c) t u

checkTermType :: Term -> Type -> Index -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Bool
checkTermType (Apply c l) ty i = case ty of
    BundleType u -> do
        cty <- inferValueType c
        case cty of
            Circ i' t u' -> do
                domainCheck <- checkValueType l (BundleType t)
                when (u /= u') (throwError "Type mismatch")
                when (i < i') (throwError "Circuit too wide")
                return domainCheck
            _ -> throwError  "First argument of apply is supposed to be a circuit"
    _ -> throwError $ "Cannot give type " ++ show ty ++ " to an apply statement"


        