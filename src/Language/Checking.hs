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
import qualified Data.Map as Map
import WireBundle.Syntax (Bundle, BundleType, Wide (wireCount))
import qualified WireBundle.Syntax as Bundle
import Control.Exception (throw)

-- Corresponds to Γ in the paper
type TypingContext = Map VariableId Type

typingContextLookup :: VariableId -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Type
typingContextLookup id = do
    (theta,gamma,q) <- get
    outcome <- maybe (throwError $ "Unbound variable " ++ id) return (Map.lookup id gamma)
    let gamma' = if isLinear outcome then Map.delete id gamma else gamma
    put (theta,gamma',q)
    return outcome

bindVariable :: VariableId -> Type -> StateT (IndexContext, TypingContext, LabelContext) (Either String) ()
bindVariable id typ = do
    (theta,gamma,q) <- get
    when (Map.member id gamma) $ throwError $ "Cannot shadow existing variable " ++ id
    let gamma' = Map.insert id typ gamma
    put (theta,gamma',q)

contextWireCount :: StateT (IndexContext, TypingContext, LabelContext) (Either String) Index
contextWireCount = do
    (_,gamma,q) <- get
    return $ Plus (wireCount gamma) (wireCount q)

containsLinearResource :: TypingContext -> Bool
containsLinearResource = any isLinear . Map.elems

linearContextsNonempty :: StateT (IndexContext, TypingContext, LabelContext) (Either String) Bool
linearContextsNonempty = do
    (_, gamma, q) <- get
    return $ containsLinearResource gamma || not (Map.null q)

-- Turns a wire bundle into an equivalent language-level value
embedWireBundle :: Bundle -> Value
embedWireBundle Bundle.UnitValue = UnitValue
embedWireBundle (Bundle.Label id) = Label id
embedWireBundle (Bundle.Pair b1 b2) = Pair (embedWireBundle b1) (embedWireBundle b2)

-- Turns a wire bundle type into an equivalent language-level type
embedBundleType :: BundleType -> Type
embedBundleType Bundle.UnitType = UnitType
embedBundleType (Bundle.WireType wtype) = WireType wtype
embedBundleType (Bundle.Tensor b1 b2) = Tensor (embedBundleType b1) (embedBundleType b2)

-- turns a bundle type derivation (which only has a label context)
-- into a typing derivation that does not use the index or typing context
embedBundleDerivation :: StateT LabelContext (Either String) a
                        -> StateT (IndexContext, TypingContext, LabelContext) (Either String) a
embedBundleDerivation der = do
    (theta, gamma, q) <- get
    case runStateT der q of
        Left err -> throwError err
        Right (x,q') -> put (theta, gamma, q') >> return x

-- Θ;Γ;Q ⊢ V <= A (Fig. 12)
-- returns True iff there are linear resources left in the typing contexts
checkValueType :: Value -> Type -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Bool
checkValueType UnitValue typ = case typ of
    UnitType -> linearContextsNonempty
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to unit value '*'"
checkValueType (Label id) typ = case typ of
    WireType wtype -> do
        wtype' <- embedBundleDerivation $ labelContextLookup id
        if wtype == wtype'
            then linearContextsNonempty
            else throwError $ "Label " ++ id ++ "has type " ++ pretty wtype' ++ " but is required to have type " ++ pretty wtype
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to label " ++ id
checkValueType (Variable id) typ = do
    typ' <- typingContextLookup id
    if typ == typ'
        then linearContextsNonempty
        else throwError $ "Variable " ++ id ++ " has type " ++ pretty typ' ++ " but is required to have type " ++ pretty typ
checkValueType (Pair v w) typ = case typ of
    Tensor typ1 typ2 -> do
        _ <- checkValueType v typ1
        checkValueType w typ2
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to pair " ++ pretty (Pair v w)
checkValueType (BoxedCircuit inB circ outB) typ = case typ of
    Circ i inBtype outBtype -> if Number (width circ) <= i 
        then lift $ do
        (inQ, outQ) <- inferCircuitSignature circ
        inputCheck <- evalStateT (checkBundleType inB inBtype) inQ
        outputCheck <- evalStateT (checkBundleType outB outBtype) outQ
        return $ inputCheck && outputCheck
        else throwError $ "Cannot conclude width (" ++ pretty circ ++ ") <= " ++ pretty i
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to a boxed circuit"
checkValueType (Abs x intyp m) typ = case typ of
    Arrow intyp' outtyp i j | intyp' == intyp -> do
        wireCountAnnotation <- contextWireCount
        when (j /= wireCountAnnotation) (throwError $ "Function captures " ++ pretty wireCountAnnotation ++ " wires but is required to capture " ++ pretty j)
        bindVariable x intyp
        checkTermType m outtyp i
    Arrow inTyp' _ _ _ -> throwError $ "Abstracted variable " ++ x ++ " is annotated with type " ++ pretty intyp ++ " but is required to have type " ++ pretty inTyp'
    _ -> throwError $ "Cannot give type " ++ pretty typ ++ " to a function"




-- Θ;Γ;Q ⊢ V => A (Fig. 12)
synthesizeValueType :: Value -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Type
synthesizeValueType UnitValue = return UnitType
synthesizeValueType (Label id) = do
    wtype <- embedBundleDerivation $ labelContextLookup id
    return $ WireType wtype
synthesizeValueType (Variable id) = typingContextLookup id
synthesizeValueType (Pair v w) = do
    typ1 <- synthesizeValueType v
    typ2 <- synthesizeValueType w
    return $ Tensor typ1 typ2
synthesizeValueType (BoxedCircuit inB circ outB) = lift $ do
        (inQ, outQ) <- inferCircuitSignature circ
        inBtype <- evalStateT (synthesizeBundleType inB) inQ
        outBtype <- evalStateT (synthesizeBundleType outB) outQ
        return $ Circ (Number $ width circ) inBtype outBtype
synthesizeValueType (Abs x intyp m) = do
    j <- contextWireCount
    bindVariable x intyp
    (outtyp, i) <- synthesizeTermType m
    return $ Arrow intyp outtyp i j

-- Θ;Γ;Q ⊢ M => A ; I (Fig. 12)
synthesizeTermType :: Term -> StateT (IndexContext, TypingContext, LabelContext) (Either String) (Type, Index)
synthesizeTermType (Apply v w) = do
    ctype <- synthesizeValueType v
    case ctype of
        Circ i inBtype outBtype -> do
            _ <- checkValueType w (embedBundleType inBtype)
            return $ (embedBundleType outBtype, i)
        _ -> throwError $ "First argument of apply: " ++ pretty v ++ " is supposed to be a circuit, instead has type " ++ pretty ctype
synthesizeTermType (Dest x y v m) = do
    ltyp <- synthesizeValueType v
    case ltyp of
        Tensor ltyp1 ltyp2 -> do
            bindVariable x ltyp1
            bindVariable y ltyp2
            synthesizeTermType m
        _ -> throwError $ "Left hand side of destructuring let: " ++ pretty v ++ " is supposed to have tensor type, instead has type " ++ pretty ltyp
synthesizeTermType (Return v) = do
    effectAnnotation <- contextWireCount
    vtyp <- synthesizeValueType v
    return (vtyp, effectAnnotation)
synthesizeTermType m = throwError $ "Cannot synthesize type of " ++ pretty m

-- Θ;Γ;Q ⊢ M <= A ; I (Fig. 12)
-- returns True iff there are linear resources left in the typing contexts
checkTermType :: Term -> Type -> Index -> StateT (IndexContext, TypingContext, LabelContext) (Either String) Bool
checkTermType (Apply v w) typ i = do
        ctype <- synthesizeValueType v
        case ctype of
            Circ i' inBtype outBtype -> do
                inputCheck <- checkValueType w (embedBundleType inBtype)
                when (embedBundleType outBtype /= typ) (throwError $
                    "Term " ++ pretty (Apply v w) ++ " has type " ++ pretty outBtype ++ " but is required to have type " ++ pretty typ)
                when (i < i') (throwError $ "Circuit has width " ++ pretty i' ++ " but is required to have width at most " ++ pretty i)
                return inputCheck
            _ -> throwError $ "First argument of apply: " ++ pretty v ++ " is supposed to be a circuit, instead has type " ++ pretty ctype
checkTermType (Dest x y v m) typ i = do
        ltyp <- synthesizeValueType v
        case ltyp of
            Tensor ltyp1 ltyp2 -> do
                bindVariable x ltyp1
                bindVariable y ltyp2
                checkTermType m typ i
            _ -> throwError $ "Left hand side of destructuring let: " ++ pretty v ++ " is supposed to have tensor type, instead has type " ++ pretty ltyp
checkTermType (Return v) typ i = do
        (_, gamma, q) <- get
        effectAnnotation <- contextWireCount
        vtyp <- synthesizeValueType v
        when (vtyp /= typ) (throwError $ "Return value " ++ pretty v ++ " has type " ++ pretty vtyp ++ " but is required to have type " ++ pretty typ)
        when (i /= effectAnnotation) (throwError $ "Return value has width " ++ pretty effectAnnotation ++ " but is required to have width " ++ pretty i)
        linearContextsNonempty
checkTermType (App v w) typ i = do
        ftyp <- synthesizeValueType v
        case ftyp of
            Arrow intyp outtyp i' j -> do
                argcheck <- checkValueType w intyp
                when (outtyp /= typ) (throwError $ "Term " ++ pretty (App v w) ++ " has type " ++ pretty outtyp ++ " but is required to have type " ++ pretty typ)
                when (i < i') (throwError $ "Function produces a circuit of width " ++ pretty i' ++ " but is required to produce a circuit of width at most " ++ pretty i)
                return argcheck
            _ -> throwError $ "First argument of apply: " ++ pretty v ++ " is supposed to be a function, instead has type " ++ pretty ftyp
-- checkTermType t _ _ = throwError $ "Cannot check type of " ++ show t


        