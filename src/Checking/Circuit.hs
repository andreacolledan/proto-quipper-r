module Checking.Circuit
  ( inferCircuitSignature,
  )
where

import AST.Circuit
import Checking.Bundle
import qualified Data.Map as Map

-- C => Q -> L (Fig. 10)
-- inferCircuitSignature c infers the circuit signature of c
-- If succesful, it returns a pair of the input and output labels of c, respectively
-- Otherwise, it returns a WireTypingError
inferCircuitSignature :: Circuit -> Either WireTypingError (LabelContext, LabelContext)
inferCircuitSignature (Id q) = Right (q, q)
inferCircuitSignature (Seq circ op bin bout) = do
  (qin, qmid) <- inferCircuitSignature circ
  let (btype1, btype2) = sig op
  qout1 <- runBundleTypeCheckingWithRemaining qmid bin btype1
  qout2 <- synthesizeLabelContext bout btype2
  return (qin, Map.union qout1 qout2)
