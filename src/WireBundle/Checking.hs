module WireBundle.Checking (
    LabelContext,
    synthesizeLabelContext,
    synthesizeBundleType,
    checkBundleType,
    labelContextLookup,
    WireTypingError(..)
) where
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.Map (Map)
import qualified Data.Map as Map
import PrettyPrinter
import WireBundle.Syntax
import Control.Monad (when)

-- Corresponds to Q in the paper
type LabelContext = Map LabelId WireType

-- Wire typing error
data WireTypingError
    = UnboundLabel LabelId
    | BundleTypeMismatch Bundle BundleType BundleType
    | ContextSynthesisMismatch Bundle BundleType
    | UnusedLabels LabelContext
    deriving (Eq)

instance Show WireTypingError where
    show (UnboundLabel id) = "Unbound label " ++ show id
    show (BundleTypeMismatch b btype1 btype2) = "Bundle " ++ pretty b ++ " has type " ++ pretty btype1 ++ " but is expected to have type " ++ pretty btype2
    show (ContextSynthesisMismatch b btype) = "Cannot match structure of bundle " ++ pretty b ++ " and bundle type " ++ pretty btype ++ " to produce a label context"
    show (UnusedLabels q) = "Unused labels in label context: " ++ pretty q

-- Lookup a label in the label context and remove it
labelContextLookup :: LabelId -> StateT LabelContext (Either WireTypingError) WireType
labelContextLookup id = do
    q <- get
    outcome <- maybe (throwError $ UnboundLabel id) return (Map.lookup id q)
    put $ Map.delete id q
    return outcome

-- Q ⊢ l => T (Fig. 10)
synthesizeBundleType :: Bundle -> StateT LabelContext (Either WireTypingError) BundleType
synthesizeBundleType UnitValue = return UnitType
synthesizeBundleType (Label id) = do
    btype <- labelContextLookup id
    return $ WireType btype
synthesizeBundleType (Pair b1 b2) = do
    btype1 <- synthesizeBundleType b1
    btype2 <- synthesizeBundleType b2
    return $ Tensor btype1 btype2

-- produces the unique label context that attributes a given bundle type to a given bundle
-- matching the structure of the bundle with the structure of the bundle type
synthesizeLabelContext :: Bundle -> BundleType -> Either WireTypingError LabelContext
synthesizeLabelContext UnitValue UnitType = Right Map.empty
synthesizeLabelContext (Label id) (WireType wtype) = Right $ Map.fromList [(id,wtype)]
synthesizeLabelContext (Pair b1 b2) (Tensor btype1 btype2) = do
    q1 <- synthesizeLabelContext b1 btype1
    q2 <- synthesizeLabelContext b2 btype2
    return $ Map.union q1 q2
synthesizeLabelContext b btype = throwError $ ContextSynthesisMismatch b btype

-- Q ⊢ l <= T (Fig. 10)
checkBundleType :: Bundle -> BundleType -> StateT LabelContext (Either WireTypingError) ()
checkBundleType b btype = do
    synthesizedBtype <- synthesizeBundleType b
    when (synthesizedBtype /= btype) $ throwError $ BundleTypeMismatch b synthesizedBtype btype