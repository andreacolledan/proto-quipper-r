module WireBundle.Checking (
    LabelContext,
    synthesizeLabelContext,
    synthesizeBundleType,
    checkBundleType,
    labelContextLookup
) where
import Data.Map (Map)
import qualified Data.Map as Map
import WireBundle.Syntax
import Control.Monad.State.Lazy
import Control.Monad.Except
import PrettyPrinter

-- Corresponds to Q in the paper
type LabelContext = Map LabelId WireType

labelContextLookup :: LabelId -> StateT LabelContext (Either String) WireType
labelContextLookup id = do
    q <- get
    outcome <- maybe (throwError $ "Unbound label " ++ id) return (Map.lookup id q)
    put $ Map.delete id q
    return outcome

labelContextNonempty :: StateT LabelContext (Either String) Bool
labelContextNonempty = do
    not . Map.null <$> get

-- Q ⊢ l => T
synthesizeBundleType :: Bundle -> StateT LabelContext (Either String) BundleType
synthesizeBundleType UnitValue = return UnitType
synthesizeBundleType (Label id) = do
    btype <- labelContextLookup id
    return $ WireType btype


synthesizeLabelContext :: Bundle -> BundleType -> Either String LabelContext
synthesizeLabelContext UnitValue UnitType = Right Map.empty
synthesizeLabelContext (Label id) (WireType wtype) = Right $ Map.fromList [(id,wtype)]
synthesizeLabelContext b btype = Left $ "Cannot match structure of " ++ pretty b ++ " with structure of " ++ pretty btype

-- Q ⊢ l <= T (Fig 10)
-- returns True iff there are linear resources left in the label context
checkBundleType :: Bundle -> BundleType -> StateT LabelContext (Either String) Bool
checkBundleType b btype = do
    synthesizedBtype <- synthesizeBundleType b
    if synthesizedBtype == btype
        then labelContextNonempty
        else throwError "Type mismatch"