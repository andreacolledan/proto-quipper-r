module Wire.Checking where
import Data.Map (Map)
import qualified Data.Map as Map
import Wire.Syntax
import Control.Monad.State.Lazy
import Control.Monad.Except
import Index

-- Corresponds to Q in the paper
type LabelContext = Map LabelId WireType

labelContextLookup :: LabelId -> StateT LabelContext (Either String) WireType
labelContextLookup id = do
    labelContext <- get
    result <- maybe (throwError $ "Unbound " ++ id) return (Map.lookup id labelContext)
    let labelContext' = Map.delete id labelContext
    put labelContext'
    return result

inferBundleType :: Bundle -> StateT LabelContext (Either String) BundleType
inferBundleType UnitValue = return UnitType
inferBundleType (Label id) = do
    ty <- labelContextLookup id
    return $ WireType ty

inferLabelContext :: Bundle -> BundleType -> Either String LabelContext
inferLabelContext UnitValue UnitType = Right Map.empty
inferLabelContext (Label id) (WireType w) = Right $ Map.fromList [(id,w)]
inferLabelContext _ _ = Left "Bundle and type do not match"

checkBundleType :: Bundle -> BundleType -> StateT LabelContext (Either String) Bool
checkBundleType l t = do
    t' <- inferBundleType l
    lc <- get
    if t == t'
        then return (Map.null lc)
        else throwError "Type mismatch"