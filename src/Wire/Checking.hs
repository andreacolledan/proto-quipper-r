module Wire.Checking where
import Data.Map (Map)
import qualified Data.Map as Map
import Wire.Syntax
import Control.Monad.State.Lazy
import Control.Monad.Except

type LabelContext = Map LabelId WireType

data BundleTypeError
    = UnboundLabel LabelId
    | OtherBundleTypeError String

labelContextLookup :: LabelId -> StateT LabelContext (Either BundleTypeError) WireType
labelContextLookup id = do
    labelContext <- get
    result <- maybe (throwError $ UnboundLabel id) return (Map.lookup id labelContext)
    let labelContext' = Map.delete id labelContext
    put labelContext'
    return result


inferBundleType :: Bundle -> StateT LabelContext (Either BundleTypeError) BundleType
inferBundleType UnitValue = return UnitType
inferBundleType (Label id) = do
    ty <- labelContextLookup id
    return $ WireType ty

inferLabelContext :: Bundle -> BundleType -> Either BundleTypeError LabelContext
inferLabelContext UnitValue UnitType = Right Map.empty
inferLabelContext (Label id) (WireType w) = Right $ Map.fromList [(id,w)]
inferLabelContext _ _ = Left $ OtherBundleTypeError "Bundle and type do not match"

checkBundleType :: LabelContext -> Bundle -> BundleType -> Bool
checkBundleType q l t = case runStateT (inferBundleType l) q of
    Left _ -> False
    Right (t',remainingContext) -> Map.null remainingContext && t == t'