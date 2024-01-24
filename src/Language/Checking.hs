{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Language.Checking(
    checkValueType,
    synthesizeValueType,
    synthesizeTermType,
    checkTermType,
    TypingContext,
    TypingEnvironment(..),
    typingContextLookup,
    bindVariable,
    embedWireBundle,
    embedBundleType,
    embedBundleDerivation,
    envIsLinear,
    TypingError(..)
) where
import Circuit.Checking
import Circuit.Syntax
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Map (Map)
import Index
import Language.Syntax
import PrettyPrinter
import qualified Data.Map as Map
import WireBundle.Checking
import WireBundle.Syntax (Bundle, BundleType, Wide (wireCount))
import qualified WireBundle.Syntax as Bundle
import Control.Monad
import Data.Either.Extra (mapLeft)
import qualified WireBundle.Syntax as BundleType

-- Corresponds to Γ in the paper
type TypingContext = Map VariableId Type

-- The state of a typing derivation:
-- - the index context Θ (nonlinear)
-- - the typing context Γ (linear/nonlinear)
-- - the label context Q (linear)
data TypingEnvironment = TypingEnvironment {
    indexContext :: IndexContext,
    typingContext :: TypingContext,
    labelContext :: LabelContext
}
-- check if a typing environment contains any linear variable.
envIsLinear :: TypingEnvironment -> Bool
envIsLinear TypingEnvironment{typingContext = gamma, labelContext = q} = (any isLinear . Map.elems) gamma || Map.size q > 0

--- TYPING ERRORS ---------------------------------------------------------------


-- Typing errors
data TypingError
    = WireTypingError WireTypingError
    | UnboundVariable VariableId
    | UnusedLinearVariable VariableId
    | ShadowedLinearVariable VariableId
    | LinearResourcesInLiftedTerm
    | UnexpectedType (Either Term Value) Type Type
    | IncompatibleType (Either Term Value) Type
    | MismatchedCircuitInterface CircuitInterfaceType Circuit LabelContext Bundle
    | ExceedingCircuitWidth Circuit Index
    | UnexpectedWidthAnnotation Term Index Index
    | UnexpectedTypeConstructor (Either Term Value) Type Type
    | UnusedLinearResources TypingContext LabelContext
    | UnexpectedFormalParameterType Value Type Type
    | UnexpectedBoxingType Term Type BundleType
    | UnboxableType Value Type
    | IllFormedTypingContext IndexContext TypingContext
    deriving (Eq)

data CircuitInterfaceType = Input | Output deriving (Eq)
instance Show CircuitInterfaceType where
    show Input = "input"
    show Output = "output"

instance Show TypingError where
    show (WireTypingError err) = show err
    show (UnboundVariable id) = "Unbound variable " ++ id
    show (UnusedLinearVariable id) = "Unused linear variable " ++ id
    show (ShadowedLinearVariable id) = "Shadowed linear variable " ++ id
    show LinearResourcesInLiftedTerm = "Linear resources consumed in a lifted term"
    show (UnexpectedType exp typ1 typ2) =
        "Expected expression " ++ pretty exp ++ " to have type " ++ pretty typ1 ++ ", got " ++ pretty typ2 ++ " instead"
    show (IncompatibleType exp typ) = "Expression " ++ pretty exp ++ " cannot be given a type of the form " ++ pretty typ
    show (MismatchedCircuitInterface interfaceType circ q b) =
        "Bundle " ++ pretty b ++ " is not a valid " ++ show interfaceType ++ " interface for circuit " ++ pretty circ
        ++ ", whose " ++ show interfaceType ++ " labels are " ++ pretty q
    show (ExceedingCircuitWidth circ i) =
        "Circuit " ++ pretty circ ++ " has width " ++ pretty (width circ) ++ ", which cannot be proven to be bounded by " ++ pretty i
    show (UnexpectedWidthAnnotation m i j) =
        "Expected term " ++ pretty m ++ " to have width annotation " ++ pretty i ++ ", got " ++ pretty j ++ " instead"
    show (UnexpectedTypeConstructor exp typ1 typ2) =
        "Expected expression " ++ pretty exp ++ " to have " ++ printConstructor typ1 ++ ", got type " ++ pretty typ2 ++ " instead"
    show (UnusedLinearResources gamma q) = "Unused linear resources in typing contexts: " ++ pretty gamma ++ " ; " ++ pretty q
    show (UnexpectedFormalParameterType v typ1 typ2) =
        "Expected formal parameter of " ++ pretty v ++ " to have type " ++ pretty typ1 ++ ", got " ++ pretty typ2 ++ " instead"
    show (UnexpectedBoxingType m btype1 btype2) =
        "Expected input type of boxed circuit " ++ pretty m ++ " to be " ++ pretty btype1 ++ ", got " ++ pretty btype2 ++ " instead"
    show (UnboxableType v typ) =
        "Expression " ++ pretty v ++ " of type " ++ pretty typ ++ "cannot be boxed"
    show (IllFormedTypingContext theta gamma) =
        "Typing context " ++ pretty gamma ++ " is not well-formed with respect to index context " ++ pretty theta

-- Shows the name of the top level constructor of a type
printConstructor :: Type -> String
printConstructor UnitType = "unit type"
printConstructor (WireType _) = "wire type"
printConstructor (Tensor _ _) = "tensor type"
printConstructor (Circ {}) = "circuit type"
printConstructor (Arrow {}) = "arrow type"
printConstructor (Bang _) = "bang type"



--- TYPING CONTEXT OPERATIONS ---------------------------------------------------------------


-- lookup a variable in the typing context, remove it if it is linear
-- throws an error if the variable is not found
typingContextLookup :: VariableId -> StateT TypingEnvironment (Either TypingError) Type
typingContextLookup id = do
    env@TypingEnvironment{typingContext = gamma} <- get
    typ <- maybe (throwError $ UnboundVariable id) return (Map.lookup id gamma)
    when (isLinear typ) $ put env{typingContext = Map.delete id gamma}
    return typ

-- add a new binding to the typing context
-- throws an error if the variable is already bound (no shadowing allowed at the moment)
bindVariable :: VariableId -> Type -> StateT TypingEnvironment (Either TypingError) ()
bindVariable id typ = do
    env@TypingEnvironment{typingContext = gamma} <- get
    when (Map.member id gamma) $ throwError $ ShadowedLinearVariable id
    let gamma' = Map.insert id typ gamma
    put env{typingContext = gamma'}

-- remove a binding from the typing context
-- throws an error if the variable is linear
unbindVariable :: VariableId -> StateT TypingEnvironment (Either TypingError) ()
unbindVariable id = do
    env@TypingEnvironment{typingContext = gamma} <- get
    case Map.lookup id gamma of
        Nothing -> return ()
        Just t -> do
            when (isLinear t) (throwError $ UnusedLinearVariable id)
            put env{typingContext = Map.delete id gamma}

-- check if the current typing context is well formed with respect to the current index context
-- TODO: this check might be performed just once globally instead of at every leaf of the derivation tree
checkTypingContextWellFormed :: StateT TypingEnvironment (Either TypingError) ()
checkTypingContextWellFormed = do
    TypingEnvironment{indexContext = theta, typingContext = gamma} <- get
    unless (wellFormed theta gamma) $ throwError $ IllFormedTypingContext theta gamma



--- DERIVATION COMBINATORS ---------------------------------------------------------------


-- locally bind a variable in the scope of an existing derivation
withBoundVariable :: VariableId -> Type -> StateT TypingEnvironment (Either TypingError) a
                    -> StateT TypingEnvironment (Either TypingError) a
withBoundVariable x typ der = do
    bindVariable x typ
    outcome <- der
    unbindVariable x --this throws an error if x is linear and der does not consume it
    return outcome

-- make an existing derivation also return the amount of wires it consumes
withWireCount :: StateT TypingEnvironment (Either TypingError) a
                    -> StateT TypingEnvironment (Either TypingError) (a, Index)
withWireCount der = do
    TypingEnvironment{typingContext = gamma, labelContext = q} <- get
    outcome <- der
    TypingEnvironment{typingContext = gamma', labelContext = q'} <- get
    -- count how many linear resources have disappeared from the contexts
    let gammaDiff = Map.difference gamma gamma'
    let qDiff = Map.difference q q'
    let resourceCount = wireCount gammaDiff `Plus` wireCount qDiff
    return (outcome, resourceCount)

-- make an existing derivation fail if it consumes any linear resources from the pre-existing environment
withNonLinearContext :: StateT TypingEnvironment (Either TypingError) a
                        -> StateT TypingEnvironment (Either TypingError) a
withNonLinearContext der = do
    TypingEnvironment{typingContext = gamma, labelContext = q} <- get
    outcome <- der
    TypingEnvironment{typingContext = gamma', labelContext = q'} <- get
    let gammaDiff = Map.difference gamma gamma'
    let qDiff = Map.difference q q'
    when ((any isLinear . Map.elems) gammaDiff || Map.size qDiff > 0) $ throwError LinearResourcesInLiftedTerm
    return outcome



--- BUNDLE CHECKING WITHIN TYPE CHECKING ------------------------------------------------------------


-- Turns a wire bundle into an equivalent PQR value
embedWireBundle :: Bundle -> Value
embedWireBundle Bundle.UnitValue = UnitValue
embedWireBundle (Bundle.Label id) = Label id
embedWireBundle (Bundle.Pair b1 b2) = Pair (embedWireBundle b1) (embedWireBundle b2)

-- Turns a bundle type into an equivalent PQR type
embedBundleType :: BundleType -> Type
embedBundleType Bundle.UnitType = UnitType
embedBundleType (Bundle.WireType wtype) = WireType wtype
embedBundleType (Bundle.Tensor b1 b2) = Tensor (embedBundleType b1) (embedBundleType b2)

-- turns a bundle type derivation (which only has a label context)
-- into a typing derivation that does not use the index or typing context
embedBundleDerivation :: StateT LabelContext (Either WireTypingError) a
                        -> StateT TypingEnvironment (Either TypingError) a
embedBundleDerivation der = do
    env@TypingEnvironment{labelContext = q} <- get
    case runStateT der q of
        Left err -> throwError $ WireTypingError err
        Right (x,q') -> put env{labelContext=q'} >> return x



--- PQR TYPE CHECKING ---------------------------------------------------------------

-- Type checking for values, retuns () if successful
-- Θ;Γ;Q ⊢ V <== A (Fig. 12)
checkValueType :: Value -> Type -> StateT TypingEnvironment (Either TypingError) ()
checkValueType UnitValue UnitType = checkTypingContextWellFormed
checkValueType v@(Label id) typ@(WireType wtype) = do
    checkTypingContextWellFormed
    wtype' <- embedBundleDerivation $ labelContextLookup id
    when (wtype /= wtype') $ throwError $ UnexpectedType (Right v) typ (WireType wtype')
checkValueType v@(Variable id) typ = do
    checkTypingContextWellFormed
    typ' <- typingContextLookup id
    when (typ /= typ') $ throwError $ UnexpectedType (Right v) typ typ'
checkValueType (Pair v w) (Tensor typ1 typ2) = do
        _ <- checkValueType v typ1
        checkValueType w typ2
checkValueType (BoxedCircuit inB circ outB) (Circ i inBtype outBtype) = do
    checkTypingContextWellFormed   
    if Number (width circ) <= i
        then lift $ do
            (inQ, outQ) <- mapLeft WireTypingError $ inferCircuitSignature circ
            inQ' <- mapLeft WireTypingError $ execStateT (checkBundleType inB inBtype) inQ
            outQ' <- mapLeft WireTypingError $ execStateT (checkBundleType outB outBtype) outQ
            unless (Map.null inQ')  $ throwError $ MismatchedCircuitInterface Input circ inQ' inB
            unless (Map.null outQ') $ throwError $ MismatchedCircuitInterface Output circ outQ' outB
        else throwError $ ExceedingCircuitWidth circ i
checkValueType v@(Abs x intyp m) (Arrow intyp' outtyp i j) = do
    when (intyp' /= intyp) $ throwError $ UnexpectedFormalParameterType v intyp' intyp
    ((),resourceCount) <- withWireCount $ withBoundVariable x intyp $ checkTermType m outtyp i
    when (j /= resourceCount) $ throwError $ UnexpectedType (Right v) (Arrow intyp outtyp i j) (Arrow intyp outtyp i resourceCount)
checkValueType (Lift m) (Bang typ) = withNonLinearContext $ checkTermType m typ (Number 0)
--If typ is not of the right form for v (e.g. v is an abstraction and typ is a bang type), throw an IncompatibleType error
checkValueType v typ = throwError $ IncompatibleType (Right v) typ

-- Type checking for terms, returns () if successful
-- Θ;Γ;Q ⊢ M <== A ; I (Fig. 12)
checkTermType :: Term -> Type -> Index -> StateT TypingEnvironment (Either TypingError) ()
checkTermType m@(Apply v w) typ i = do
        ctype <- synthesizeValueType v
        case ctype of
            Circ i' inBtype outBtype -> do
                inputCheck <- checkValueType w (embedBundleType inBtype)
                when (embedBundleType outBtype /= typ) $ throwError $ UnexpectedType (Left m) typ (embedBundleType outBtype)
                when (i < i') $ throwError $ UnexpectedWidthAnnotation m i i'
                return inputCheck
            _ -> throwError $ UnexpectedTypeConstructor (Right v) (Circ (Number 0) BundleType.UnitType BundleType.UnitType) ctype
checkTermType (Dest x y v m) typ i = do
        ltyp <- synthesizeValueType v
        case ltyp of
            Tensor ltyp1 ltyp2 -> do
                withBoundVariable x ltyp1 $ withBoundVariable y ltyp2 $ checkTermType m typ i
            _ -> throwError $ UnexpectedTypeConstructor (Right v) (Tensor UnitType UnitType) ltyp
checkTermType m@(Return v) typ i = do
        (vtyp,resourceCount) <- withWireCount $ synthesizeValueType v
        when (vtyp /= typ) $ throwError $ UnexpectedType (Left m) typ vtyp
        when (i /= resourceCount) $ throwError $ UnexpectedWidthAnnotation m i resourceCount
checkTermType m@(App v w) typ i = do
        ftyp <- synthesizeValueType v
        case ftyp of
            Arrow intyp outtyp i' _ -> do
                checkValueType w intyp
                when (outtyp /= typ) $ throwError $ UnexpectedType (Left m) typ outtyp
                when (i < i') $ throwError $ UnexpectedWidthAnnotation m i i'
            _ -> throwError $ UnexpectedTypeConstructor (Right v) (Arrow UnitType UnitType (Number 0) (Number 0)) ftyp
checkTermType m@(Force v) typ i = do
        when (i /= Number 0) $ throwError $ UnexpectedWidthAnnotation m (Number 0) i
        --the check for the context to be non-linear is pushed down into the type check for the bang-typed value
        checkValueType v (Bang typ)
checkTermType (Let x m n) typ i = do
        (ltype, lwidth) <- synthesizeTermType m
        ((rtype,rwidth), rWireCount) <- withWireCount $ withBoundVariable x ltype $ synthesizeTermType n
        when (rtype /= typ) $ throwError $ UnexpectedType (Left (Let x m n)) typ rtype
        let overallWidth = Max (Plus lwidth rWireCount) rwidth
        when (i /= overallWidth) $ throwError $ UnexpectedWidthAnnotation (Let x m n) i overallWidth
checkTermType m@(Box inbtype v) (Circ i inbtype' outbtype) j = do
        when (inbtype' /= inbtype) $ throwError $ UnexpectedBoxingType m (embedBundleType inbtype') inbtype
        when (j /= Number 0) $ throwError $ UnexpectedWidthAnnotation m j (Number 0)
        --the check for the context to be non-linear is pushed down into the type check for the bang-typed value
        checkValueType v (Bang $ Arrow (embedBundleType inbtype) (embedBundleType outbtype) i (Number 0))
--If typ is not of the right form for v (e.g. v is an abstraction and typ is a bang type), throw an IncompatibleType error
checkTermType m typ _ = throwError $ IncompatibleType (Left m) typ



--- PQR TYPE SYNTHESIS ---------------------------------------------------------------


-- Type synthesis for values, returns the type of the value if successful, throws an error otherwise 
-- Θ;Γ;Q ⊢ V => A (Fig. 12)
synthesizeValueType :: Value -> StateT TypingEnvironment (Either TypingError) Type
synthesizeValueType UnitValue = do
    checkTypingContextWellFormed
    return UnitType
synthesizeValueType (Label id) = do
    checkTypingContextWellFormed
    wtype <- embedBundleDerivation $ labelContextLookup id
    return $ WireType wtype
synthesizeValueType (Variable id) = do
    checkTypingContextWellFormed
    typingContextLookup id
synthesizeValueType (Pair v w) = do
    typ1 <- synthesizeValueType v
    typ2 <- synthesizeValueType w
    return $ Tensor typ1 typ2
synthesizeValueType (BoxedCircuit inB circ outB) = do
        checkTypingContextWellFormed
        lift $ do
            (inQ, outQ) <- mapLeft WireTypingError $ inferCircuitSignature circ
            (inBtype, inQ') <- mapLeft WireTypingError $ runStateT (synthesizeBundleType inB) inQ
            (outBtype, outQ') <- mapLeft WireTypingError $ runStateT (synthesizeBundleType outB) outQ
            unless (Map.null inQ') $ throwError $ MismatchedCircuitInterface Input circ inQ' inB
            unless (Map.null outQ') $ throwError $ MismatchedCircuitInterface Output circ outQ' outB
            return $ Circ (Number $ width circ) inBtype outBtype
synthesizeValueType (Abs x intyp m) = do
    ((outtyp, i), j) <- withWireCount $ withBoundVariable x intyp $ synthesizeTermType m
    return $ Arrow intyp outtyp i j
synthesizeValueType (Lift m) = do
    (typ, i) <- withNonLinearContext $ synthesizeTermType m
    when (i /= Number 0) (throwError $ UnexpectedWidthAnnotation m (Number 0) i)
    return $ Bang typ

-- Type synthesis for terms, returns the type of the term and the width upper bound if successful, throws an error otherwise
-- Θ;Γ;Q ⊢ M => A ; I (Fig. 12)
synthesizeTermType :: Term -> StateT TypingEnvironment (Either TypingError) (Type, Index)
synthesizeTermType (Apply v w) = do
    ctype <- synthesizeValueType v
    case ctype of
        Circ i inBtype outBtype -> do
            _ <- checkValueType w (embedBundleType inBtype)
            return (embedBundleType outBtype, i)
        _ -> throwError $ UnexpectedTypeConstructor (Right v) (Circ (Number 0) BundleType.UnitType BundleType.UnitType) ctype
synthesizeTermType (Dest x y v m) = do
    ltyp <- synthesizeValueType v
    case ltyp of
        Tensor ltyp1 ltyp2 -> do
            withBoundVariable x ltyp1 $ withBoundVariable y ltyp2 $ synthesizeTermType m
        _ -> throwError $ UnexpectedTypeConstructor (Right v) (Tensor UnitType UnitType) ltyp
synthesizeTermType (Return v) = withWireCount $ synthesizeValueType v
synthesizeTermType (App v w) = do
    ftyp <- synthesizeValueType v
    case ftyp of
        Arrow intyp outtyp i _ -> do
            _ <- checkValueType w intyp
            return (outtyp, i)
        _ -> throwError $ UnexpectedTypeConstructor (Right v) (Arrow UnitType UnitType (Number 0) (Number 0)) ftyp
synthesizeTermType (Force v) = do
    --the check for the context to be non-linear is pushed down into the type synthesis for the bang-typed value
    vtyp <- synthesizeValueType v
    case vtyp of
        Bang typ -> return (typ, Number 0)
        _ -> throwError $ UnexpectedTypeConstructor (Right v) (Bang UnitType) vtyp
synthesizeTermType (Let x m n) = do
    (ltype, lwidth) <- synthesizeTermType m
    ((rtype,rwidth), rWireCount) <- withWireCount $ withBoundVariable x ltype $ synthesizeTermType n
    return (rtype, Max (Plus lwidth rWireCount) rwidth)
synthesizeTermType m@(Box inbtype v) = do
    --the check for the context to be non-linear is pushed down into the type synthesis for the bang-typed value
    fType <- synthesizeValueType v
    case fType of
        Bang (Arrow intyp outtyp i _) -> do
            inbtype' <- maybe (throwError $ UnboxableType v fType) return (toBundleType intyp)
            when (inbtype' /= inbtype) $ throwError $ UnexpectedBoxingType m intyp inbtype
            outbtype <- maybe (throwError $ UnboxableType v fType) return (toBundleType outtyp)
            return (Circ i inbtype outbtype, Number 0)
        _ -> throwError $ UnboxableType v fType