module Language.Checking where
import Language.Syntax
import Data.Map (Map)
import Circuit.Checking
import WireBundle.Checking
import Index
import Control.Monad.State.Lazy
import Control.Monad.Except
import Circuit.Syntax
import Control.Monad (when)
import PrettyPrinter

-- Corresponds to Γ in the paper
type TypingContext = Map VariableId Type

-- turns a bundle type derivation (which only has a label context)
-- into a typing derivation that does not use the index or typing context
embedBundleDerivation :: StateT LabelContext (Either String) a
                        -> StateT (IndexContext, TypingContext, LabelContext) (Either String) a
embedBundleDerivation der = do
    (theta, gamma, q) <- get
    case runStateT der q of
        Left err -> throwError err
        Right (x,q') -> put (theta, gamma, q') >> return x

-- Θ;Γ;Q ⊢ V <= A
-- return value is True iff the linear contexts are empty at the return site
checkValueType :: Value -> Type -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Bool
checkValueType (Bundle b) typ = case typ of 
    BundleType btype -> embedBundleDerivation $ checkBundleType b btype
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to a bundle of wires"
checkValueType (BoxedCircuit inB circ outB) typ = case typ of
    Circ i inBtype outBtype -> if Number (width circ) <= i 
        then lift $ do
        (inQ, outQ) <- inferCircuitSignature circ
        inputCheck <- evalStateT (checkBundleType inB inBtype) inQ
        outputCheck <- evalStateT (checkBundleType outB outBtype) outQ
        return $ inputCheck && outputCheck
        else throwError $ "Cannot conclude width (" ++ pretty circ ++ ") <= " ++ pretty i
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to a boxed circuit"

-- Θ;Γ;Q ⊢ V => A
synthesizeValueType :: Value -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Type
synthesizeValueType (Bundle b) = do
    btype <- embedBundleDerivation $ synthesizeBundleType b
    return $ BundleType btype
synthesizeValueType (BoxedCircuit inB circ outB) = lift $ do
        (inQ, outQ) <- inferCircuitSignature circ
        inBtype <- evalStateT (synthesizeBundleType inB) inQ
        outBtype <- evalStateT (synthesizeBundleType outB) outQ
        return $ Circ (Number $ width circ) inBtype outBtype

-- Θ;Γ;Q ⊢ M <= A ; I
-- return value is True iff the linear contexts are empty at the return site
checkTermType :: Term -> Type -> Index -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Bool
checkTermType (Apply v w) typ i = case typ of
    BundleType btype -> do
        ctype <- synthesizeValueType v
        case ctype of
            Circ i' inBtype outBtype -> do
                inputCheck <- checkValueType w (BundleType inBtype)
                when (btype /= outBtype) (throwError "Type mismatch")
                when (i < i') (throwError "Circuit too wide")
                return inputCheck
            _ -> throwError  "First argument of apply is supposed to be a circuit"
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to an apply statement"


-- checkTermType t _ _ = throwError $ "Cannot check type of " ++ show t


        