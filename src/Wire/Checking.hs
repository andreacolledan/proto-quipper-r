module Wire.Checking (
    LabelContext,
    synthesizeLabelContext,
    synthesizeBundleType,
    checkBundleType
) where
import Data.Map (Map)
import qualified Data.Map as Map
import Wire.Syntax
import Control.Monad.State.Lazy
import Control.Monad.Except

-- Corresponds to Q in the paper
type LabelContext = Map LabelId WireType

labelContextLookup :: LabelId -> StateT LabelContext (Either String) WireType
labelContextLookup id = do
    labelContext <- get
    result <- maybe (throwError $ "Unbound " ++ id) return (Map.lookup id labelContext)
    let labelContext' = Map.delete id labelContext
    put labelContext'
    return result

-- Q ⊢ l => T
synthesizeBundleType :: Bundle -> StateT LabelContext (Either String) BundleType
synthesizeBundleType UnitValue = return UnitType
synthesizeBundleType (Label id) = do
    ty <- labelContextLookup id
    return $ WireType ty

synthesizeLabelContext :: Bundle -> BundleType -> Either String LabelContext
synthesizeLabelContext UnitValue UnitType = Right Map.empty
synthesizeLabelContext (Label id) (WireType w) = Right $ Map.fromList [(id,w)]
synthesizeLabelContext _ _ = Left "Bundle and type do not match"

-- Q ⊢ l <= T (Fig 10)
-- return value is True iff the linear contexts are empty at the return site
checkBundleType :: Bundle -> BundleType -> StateT LabelContext (Either String) Bool
checkBundleType l t = do
    t' <- synthesizeBundleType l
    lc <- get
    if t == t'
        then return (Map.null lc)
        else throwError "Type mismatch"