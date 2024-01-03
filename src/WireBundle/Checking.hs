module WireBundle.Checking (
    LabelContext,
    synthesizeLabelContext,
    synthesizeBundleType,
    checkBundleType,
    labelContextLookup
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

-- Lookup a label in the label context and remove it
labelContextLookup :: LabelId -> StateT LabelContext (Either String) WireType
labelContextLookup id = do
    q <- get
    outcome <- maybe (throwError $ "Unbound label " ++ id) return (Map.lookup id q)
    put $ Map.delete id q
    return outcome

-- Check that the label context is nonempty
labelContextNonempty :: StateT LabelContext (Either String) Bool
labelContextNonempty = do
    not . Map.null <$> get

-- Q ⊢ l => T (Fig. 10)
synthesizeBundleType :: Bundle -> StateT LabelContext (Either String) BundleType
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
synthesizeLabelContext :: Bundle -> BundleType -> Either String LabelContext
synthesizeLabelContext UnitValue UnitType = Right Map.empty
synthesizeLabelContext (Label id) (WireType wtype) = Right $ Map.fromList [(id,wtype)]
synthesizeLabelContext (Pair b1 b2) (Tensor btype1 btype2) = do
    q1 <- synthesizeLabelContext b1 btype1
    q2 <- synthesizeLabelContext b2 btype2
    return $ Map.union q1 q2
synthesizeLabelContext b btype = Left $ "Cannot match structure of " ++ pretty b ++ " with structure of " ++ pretty btype

-- Q ⊢ l <= T (Fig. 10)
checkBundleType :: Bundle -> BundleType -> StateT LabelContext (Either String) ()
checkBundleType b btype = do
    synthesizedBtype <- synthesizeBundleType b
    when (synthesizedBtype /= btype) $ throwError "Type mismatch"