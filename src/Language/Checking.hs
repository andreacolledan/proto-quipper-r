module Language.Checking where
import Language.Syntax
import Data.Map (Map)
import Circuit.Checking
import Wire.Checking
import Index
import Control.Monad.State.Lazy
import Control.Monad.Except
import Circuit.Syntax
import Control.Monad (when)

-- Corresponds to Γ in the paper
type TypingContext = Map VariableId Type

-- turns a bundle type derivation (which only has a label context)
-- into a typing derivation that does not use the index or typing context
embedBundleDerivation :: StateT LabelContext (Either String) a
                        -> StateT (IndexContext, TypingContext, LabelContext) (Either String) a
embedBundleDerivation comp = do
    (ic, tc, lc) <- get
    case runStateT comp lc of
        Left err -> throwError err
        Right (x,remainingLc) -> put (ic, tc, remainingLc) >> return x

-- Θ;Γ;Q ⊢ V <= A
-- return value is True iff the linear contexts are empty at the return site
checkValueType :: Value -> Type -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Bool
checkValueType (Bundle l) t = case t of 
    BundleType t -> embedBundleDerivation $ checkBundleType l t
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

-- Θ;Γ;Q ⊢ V => A
synthesizeValueType :: Value -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Type
synthesizeValueType (Bundle l) = do
    t <- embedBundleDerivation $ synthesizeBundleType l
    return $ BundleType t
synthesizeValueType (BoxedCircuit l c k) = lift $ do
        (ql, qk) <- inferCircuitSignature c
        t <- evalStateT (synthesizeBundleType l) ql
        u <- evalStateT (synthesizeBundleType k) qk
        return $ Circ (Number $ width c) t u

-- Θ;Γ;Q ⊢ M <= A ; I
-- return value is True iff the linear contexts are empty at the return site
checkTermType :: Term -> Type -> Index -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Bool
checkTermType (Apply v w) t i = case t of
    BundleType u -> do
        cty <- synthesizeValueType v
        case cty of
            Circ i' t u' -> do
                domainCheck <- checkValueType w (BundleType t)
                when (u /= u') (throwError "Type mismatch")
                when (i < i') (throwError "Circuit too wide")
                return domainCheck
            _ -> throwError  "First argument of apply is supposed to be a circuit"
    _ -> throwError $ "Cannot give type " ++ show t ++ " to an apply statement"


-- checkTermType t _ _ = throwError $ "Cannot check type of " ++ show t


        