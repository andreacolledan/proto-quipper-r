module Lang.Unified.Infer
  ( runTypeInference,
    runTypeInferenceWith,
  )
where

import Bundle.AST hiding (compose)
import Bundle.Infer
import Circuit (inferCircuitSignature, width)
import Control.Monad
import Control.Monad.Error.Class
import Data.Either.Extra (mapLeft)
import qualified Data.HashMap.Strict as Map
import Index.AST
import Lang.Type.AST
import Lang.Unified.AST
import Lang.Unified.Constant
import Lang.Unified.Derivation
import Lang.Unified.Pre
import Control.Monad.Except
import Solving.CVC5 (SolverHandle)

--- TYPE SYNTHESIS MODULE ---------------------------------------------------------------
---
--- This module contains the main logic to synthesize the full type of a PQR expression
--- after it has been preprocessed. Type synthesis assumes that the structure of a type
--- is already correct and focuses instead on the indices that annotate types.
--- At this stage, there should be no type variables left.
-----------------------------------------------------------------------------------------

-- | @inferWithIndices qfh e@ infers the indexed type and width upper-bound of expression @e@.
-- If successful, it returns a pair @(t, i)@, where @t@ is the inferred type of @e@ 
-- and @i@ is the upper bound on the width of the circuit built by @e@.
-- Otherwise, it throws a 'TypeError'.
-- The handle @qfh@ is used to communicate with the SMT solver.
inferWithIndices :: SolverHandle -> Expr -> TypeDerivation (Type, Index)
-- UNIT
inferWithIndices _ EUnit = withScope EUnit $ return (TUnit, Number 0)
-- LABEL
inferWithIndices _ e@(ELabel id) = withScope e $ do
  btype <- labelContextLookup id
  return (TWire btype, Number 1)
-- VARIABLE
inferWithIndices _ e@(EVar id) = withScope e $ do
  typ <- typingContextLookup id
  return (typ, wireCount typ)
-- PAIR
inferWithIndices qfh e@(EPair e1 e2) = withScope e $ do
  (typ1, i1) <- inferWithIndices qfh e1
  ((typ2, i2), wc) <- withWireCount $ inferWithIndices qfh e2
  -- max(i1 + wires in e2, i2 + #(typ1), #(typ1) + #(typ2)):
  let k = Max (Plus i1 wc) (Max (Plus i2 (wireCount typ1)) (Plus (wireCount typ1) (wireCount typ2)))
  return (TPair typ1 typ2, k)
-- NIL
inferWithIndices _ e@(ENil anno) = withScope e $ case anno of
  Just (TVar _) -> throwLocalError $ CannotSynthesizeType e
  Just typ -> do
    checkWellFormedness typ
    return (TList (Number 0) typ, Number 0)
  Nothing -> error "Internal error: nil without type annotation"
-- ABSTRACTION
inferWithIndices qfh e@(EAbs x annotyp e1) = withScope e $ do
  checkWellFormedness annotyp
  ((typ, i), wc) <- withWireCount $ withBoundVariable x annotyp $ inferWithIndices qfh e1
  return (TArrow annotyp typ i wc, wc)
-- LIFT
inferWithIndices qfh e@(ELift e1) = withScope e $ do
  (typ, i) <- withNonLinearContext $ inferWithIndices qfh e1
  unlessEq qfh i (Number 0) $ throwLocalError $ UnexpectedWidthAnnotation e1 (Number 0) i
  return (TBang typ, Number 0)
-- CONS
inferWithIndices qfh e@(ECons e1 e2) = withScope e $ do
  (typ1, i1) <- inferWithIndices qfh e1
  ((TList j typ1', i2), wc) <- withWireCount $ inferWithIndices qfh e2
  unlessSubtype qfh (TList j typ1') (TList j typ1) $ throwLocalError $ UnexpectedType e2 (TList j typ1) (TList j typ1')
  -- max (i1 + wires in e2, i2 + #(typ1), (j+1) * #(typ1)):
  let k = Max (Plus i1 wc) (Max (Plus i2 (wireCount typ1)) (Mult (Plus j (Number 1)) (wireCount typ1)))
  return (TList (Plus j (Number 1)) typ1, k)
-- FOLD
inferWithIndices qfh e@(EFold e1 e2 e3) = withScope e $ do
  -- naming conventions are not satisfied here because the rule is HARD to parse
  (steptyp@(TBang (TIForall id (TArrow (TPair acctyp elemtyp) acctyp' stepwidth o1) o2 o3)), i1) <- inferWithIndices qfh e1
  unlessZero qfh o1 $ throwLocalError $ UnexpectedIndex (Number 0) o1
  unlessZero qfh o2 $ throwLocalError $ UnexpectedIndex (Number 0) o2
  unlessZero qfh o3 $ throwLocalError $ UnexpectedIndex (Number 0) o3
  unlessSubtype qfh acctyp' (isub (Plus (IndexVariable id) (Number 1)) id acctyp) $ throwLocalError $ UnfoldableStepfunction e1 steptyp
  ((acctyp'', i2), wc1) <- withWireCount $ inferWithIndices qfh e2
  unlessSubtype qfh acctyp'' (isub (Number 0) id acctyp) $ throwLocalError $ UnfoldableAccumulator e2 acctyp''
  ((argtyp@(TList arglen elemtyp'), i3), wc2) <- withWireCount $ inferWithIndices qfh e3
  unlessSubtype qfh elemtyp' elemtyp $ throwLocalError $ UnfoldableArg e3 argtyp
  -- width upper bound of ONLY fold execution: max(#(acctyp{0/i},maximum[i<arglen] stepwidth + (arglen-(i+1))*#(elemtyp)))
  let k1 = Max (wireCount (isub (Number 0) id acctyp)) (Maximum id arglen (Plus stepwidth (Mult (Minus arglen (Plus (IndexVariable id) (Number 1))) (wireCount elemtyp))))
  -- the total upper bound takes into consideration the evaluation of e1, e2, e3 and the fold execution
  -- max(i1 + wires in e2 and e3, i2 + wires in e3, i3 + wires in the result of e2, k1):
  let k2 = Max (Plus i1 (Plus wc1 wc2)) (Max (Plus i2 wc2) (Max (Plus i3 (wireCount (isub (Number 0) id acctyp))) k1))
  return (isub arglen id acctyp, k2)
-- BOXED CIRCUIT
inferWithIndices _ e@(ECirc b1 c b2) = withScope e $ do
  (inbt, inrem, outbt, outrem) <-  liftEither $ mapLeft WireTypingError $ do
    (inlabels, outlabels) <- inferCircuitSignature c
    (inbt, inrem) <- runBundleTypeInferenceWithRemaining inlabels b1
    (outbt, outrem) <- runBundleTypeInferenceWithRemaining outlabels b2
    return (inbt, inrem, outbt, outrem)
  unless (null inrem) $ throwLocalError $ MismatchedInputInterface c inrem b1
  unless (null outrem) $ throwLocalError $ MismatchedOutputInterface c outrem b2
  return (TCirc (Number (width c)) inbt outbt, Number 0)
-- APPLICATION (FUNCTIONS)
inferWithIndices qfh e@(EApp e1 e2) = withScope e $ do
  (TArrow annotyp typ3 j1 j2, i1) <- inferWithIndices qfh e1
  ((typ2, i2), wc) <- withWireCount $ inferWithIndices qfh e2
  unlessSubtype qfh typ2 annotyp $ throwLocalError $ UnexpectedType e2 annotyp typ2
  -- max(i1 + wires in e2, i2 + j2, j1):
  let k = Max (Plus i1 wc) (Max (Plus i2 j2) j1)
  return (typ3, k)
-- APPLY (CIRCUITS)
inferWithIndices qfh e@(EApply e1 e2) = withScope e $ do
  (TCirc j inbt outbt, i1) <- inferWithIndices qfh e1
  ((typ2, i2), wc) <- withWireCount $ inferWithIndices qfh e2
  let intyp = fromBundleType inbt
  let outtyp = fromBundleType outbt
  unlessSubtype qfh typ2 intyp $ throwLocalError $ UnexpectedType e2 (fromBundleType inbt) typ2
  -- max(i1 + wires in e2, i2, j):
  let k = Max (Plus i1 wc) (Max i2 j)
  return (outtyp, k)
-- BOX
inferWithIndices qfh e@(EBox bt e1) = withScope e $ do
  (typ1@(TBang (TArrow typ2 typ3 j1 _)), i) <- inferWithIndices qfh e1
  let annotyp = fromBundleType bt
  unlessSubtype qfh annotyp typ2 $ throwLocalError $ UnboxableType e1 typ1
  case toBundleType typ3 of
    Just outbt -> return (TCirc j1 bt outbt, i)
    _ -> throwLocalError $ UnboxableType e1 typ1
-- LET-IN
inferWithIndices qfh e@(ELet x e1 e2) = withScope e $ do
  (typ1, i1) <- inferWithIndices qfh e1
  ((typ2, i2), wc) <- withWireCount $ withBoundVariable x typ1 $ inferWithIndices qfh e2
  -- max(i1 + wires in e2, i2):
  let k = Max (Plus i1 wc) i2
  return (typ2, k)
-- DESTRUCTURING LET-IN
inferWithIndices qfh e@(EDest x y e1 e2) = withScope e $ do
  (TPair typ2 typ3, i1) <- inferWithIndices qfh e1
  ((typ4, i2), wc) <- withWireCount $ withBoundVariable x typ2 $ withBoundVariable y typ3 $ inferWithIndices qfh e2
  let k = Max (Plus i1 wc) i2
  return (typ4, k)
-- ANNOTATION
inferWithIndices qfh e@(EAnno e1 annotyp) = withScope e $ do
  checkWellFormedness annotyp
  (typ, i) <- inferWithIndices qfh e1
  unlessSubtype qfh typ annotyp $ throwLocalError $ UnexpectedType e1 annotyp typ
  return (annotyp, i)
-- FORCE
inferWithIndices qfh e@(EForce e1) = withScope e $ do
  (TBang typ', i) <- inferWithIndices qfh e1
  return (typ', i)
-- INDEX ABSTRACTION
inferWithIndices qfh e@(EIAbs id e1) = withScope e $ do
  ((typ, i), wc) <- withWireCount $ withBoundIndexVariable id $ inferWithIndices qfh e1
  return (TIForall id typ i wc, i)
-- INDEX APPLICATION
inferWithIndices qfh e@(EIApp e1 g) = withScope e $ do
  (TIForall id typ2 j1 _, i) <- inferWithIndices qfh e1
  checkWellFormedness g
  return (isub g id typ2, Max i (isub g id j1))
-- CONSTANTS
inferWithIndices _ e@(EConst c) = withScope e $ return (typeOf c, Number 0)
-- LET-CONS
inferWithIndices qfh e@(ELetCons x y e1 e2) = withScope e $ do
  (typ1@(TList j typ2), i1) <- inferWithIndices qfh e1
  unlessLeq qfh (Number 1) j $ throwLocalError $ UnexpectedEmptyList e1 typ1
  ((typ3, i2), wc) <- withWireCount $ withBoundVariable x typ2 $ withBoundVariable y (TList (Minus j (Number 1)) typ2) $ inferWithIndices qfh e2
  let k = Max (Plus i1 wc) i2
  return (typ3, k)

--- EXPORTED WRAPPER FUNCTIONS ---------------------------------------------------------------

-- | @runTypeInferenceWith env e qfh@ runs the whole type inference pipeline on expression @e@,
-- using the typing environment @env@ and the handle @qfh@ to communicate with the SMT solver.
runTypeInferenceWith :: TypingEnvironment -> Expr -> SolverHandle -> IO (Either TypeError (Type, Index))
runTypeInferenceWith env e qfh = runExceptT $ do
  e' <- annotateNil env e
  ((typ, i), remaining) <- runTypeDerivation (inferWithIndices qfh e') env
  when (envIsLinear remaining) $ do
    let remainingNames = [id | (id, bs) <- Map.toList (typingContext remaining), any mustBeUsed bs] ++ Map.keys (labelContext remaining)
    throwError $ UnusedLinearVariable (head remainingNames) [e]
  return (typ, i)

-- | @runTypeInference e qfh@ runs the whole type inference pipeline on expression @e@,
-- using the handle @qfh@ to communicate with the SMT solver.
runTypeInference :: Expr -> SolverHandle -> IO (Either TypeError (Type, Index))
runTypeInference = runTypeInferenceWith emptyEnv