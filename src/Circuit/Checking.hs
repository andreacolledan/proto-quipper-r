module Circuit.Checking where
import Circuit.Syntax
import WireBundle.Checking
import WireBundle.Syntax
import qualified Data.Map as Map
import Control.Monad.State.Lazy

-- C => Q -> L (Fig. 10) 
inferCircuitSignature :: Circuit -> Either String (LabelContext, LabelContext)
inferCircuitSignature (Id q) = Right (q, q)
inferCircuitSignature (Seq circ op bin bout) = do 
    (qin, qmid) <- inferCircuitSignature circ
    let (btype1, btype2) = sig op
    qout1 <- execStateT (checkBundleType bin btype1) qmid
    qout2 <- synthesizeLabelContext bout btype2
    return (qin, Map.union qout1 qout2)
    

