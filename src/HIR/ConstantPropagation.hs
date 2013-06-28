{-# OPTIONS_GHC -Wall -Werror -i..  #-}
{-# LANGUAGE GADTs, RankNTypes #-}

module HIR.ConstantPropagation(constantPropagationPass,
                               runConstantPropagation) where

import Compiler.Hoopl
import qualified Control.Monad as Mon
import qualified Data.Map as M

import HIR.HIR
import Source.Ast
import Utils.Common

type ConstantFact = M.Map SSAVar (WithTop Lit)

constantLattice :: DataflowLattice ConstantFact
constantLattice = DataflowLattice {
  fact_name = "Constant Variables",
  fact_bot = M.empty,
  fact_join = joinMaps (extendJoinDomain constantFactJoin)
  } where
  constantFactJoin _ (OldFact old) (NewFact new)
    | new == old = (NoChange, PElem new)
    | otherwise = (SomeChange, Top)

transferConstants :: FwdTransfer HNode ConstantFact
transferConstants = mkFTransfer3 closeOpen openOpen openClose
  where
    closeOpen :: HNode C O -> ConstantFact -> ConstantFact
    closeOpen LabelHN{} = id

    openOpen :: HNode O O -> ConstantFact -> ConstantFact
    openOpen (LoadArgHN _ var) = hasTop var
    openOpen (LoadLitHN value var) = hasConst var value
    openOpen (BinOpHN _ _ _ var) = hasTop var
    openOpen (PushHN _ _ var) = hasTop var
    openOpen (ForceHN _ var) = hasTop var
    openOpen (Phi2HN _ _ var) = hasTop var
    openOpen (CopyValueHN _ var) = hasTop var

    hasTop var = M.insert var Top
    hasConst var value = M.insert var $ PElem value

    openClose :: HNode O C -> ConstantFact -> FactBase ConstantFact
    openClose (IfThenElseHN (VarR var) tLbl fLbl) f =
      mkFactBase constantLattice $ map (
        \(lbl, value) -> (lbl, M.insert var (PElem $ BoolL value) f))
      [(tLbl, True), (fLbl, False)]

    openClose (IfThenElseHN (LitR condition) tLbl fLbl) f =
      mapSingleton (if condition then tLbl else fLbl) f
    openClose (JumpHN lbl) f = mapSingleton lbl f
    openClose (ReturnHN _) _ = mapEmpty

propagateConstants :: forall m. FuelMonad m => FwdRewrite m HNode ConstantFact
propagateConstants = mkFRewrite3 closeOpen openOpen openClose
  where
    closeOpen _ _ = return Nothing

    lookupI f v = case M.lookup v f of
      Just (PElem (IntL i)) -> Just i
      _ -> Nothing

    lookupB f v = case M.lookup v f of
      Just (PElem (BoolL b)) -> Just b
      _ -> Nothing

    lookupC f v = case M.lookup v f of
      Just (PElem (ClsrL c)) -> Just c
      _ -> Nothing

    lookupL f v = case M.lookup v f of
      Just (PElem lit) -> Just lit
      _ -> Nothing

    openOpen :: FuelMonad m => HNode O O -> ConstantFact -> m (Maybe (Graph HNode O O))
    openOpen LoadArgHN{} _ = return Nothing
    openOpen LoadLitHN{} _ = return Nothing
    openOpen (BinOpHN op left right result) f =
      let rS = ratorSubstitute $ lookupI f
      in return $ Just $ mkMiddle $ BinOpHN op (rS left) (rS right) result
    openOpen (PushHN clsr val result) f =
      let rSL = ratorSubstitute $ lookupL f
          rSC = ratorSubstitute $ lookupC f
      in return $ Just $ mkMiddle $ PushHN (rSC clsr) (rSL val) result
    openOpen (ForceHN clsr result) f =
      return $ Just $ mkMiddle $ ForceHN (ratorSubstitute (lookupL f) clsr) result
    openOpen (Phi2HN (vA, lA) (vB, lB) result) f =
      let rSL = ratorSubstitute (lookupL f)
      in return $ Just $ mkMiddle $ Phi2HN (rSL vA, lA) (rSL vB, lB) result
    openOpen (CopyValueHN val result) f =
      return $ Just $ mkMiddle $ CopyValueHN (ratorSubstitute (lookupL f) val) result

    openClose :: FuelMonad m => HNode O C -> ConstantFact -> m (Maybe (Graph HNode O C))
    openClose (IfThenElseHN c tL fL) f =
      return $ Just $ mkLast $ IfThenElseHN (ratorSubstitute (lookupB f) c) tL fL
    openClose JumpHN{} _ = return Nothing
    openClose (ReturnHN val) f =
      return $ Just $ mkLast $ ReturnHN (ratorSubstitute (lookupL f) val)

evaluateNode :: (SSAVar -> Maybe (WithTop Lit)) -> HNode e x -> Maybe (HNode e x)
evaluateNode _ (BinOpHN op (LitR x) (LitR y) result) =
  Mon.liftM (`LoadLitHN` result) (functionFor op x y)
  where functionFor :: BinOp -> Int -> Int -> Maybe Lit
        functionFor PlusOp = liftNativeI (+)
        functionFor MinusOp = liftNativeI (-)
        functionFor MultOp = liftNativeI (*)
        functionFor DivOp =
          \dividend divisor -> if divisor == 0 then Nothing
                               else liftNativeI div divisor dividend
        functionFor LtOp = liftNativeB (<)
        functionFor EqOp = liftNativeB (==)

        liftNativeI fn l r = Just $ IntL $ fn l r
        liftNativeB fn l r = Just $ BoolL $ fn l r

evaluateNode _ (Phi2HN (LitR litA, _) (LitR litB, _) result) =
  if litA == litB then Just $ LoadLitHN litA result
  else Nothing

evaluateNode _ (IfThenElseHN (LitR condition) tLbl fLbl) =
  if condition then Just $ JumpHN $ if condition then tLbl else fLbl
  else Nothing -- TODO: make use of the fact that if the condition
               -- folds to anything other than a BoolL, we *know* that
               -- the program has a type error.

evaluateNode _ (ForceHN (LitR lit) result) = Just $ LoadLitHN lit result
evaluateNode _ (CopyValueHN (LitR lit) result) = Just $ LoadLitHN lit result

evaluateNode _ _ = Nothing

foldConstants :: forall m. FuelMonad m => FwdRewrite m HNode ConstantFact
foldConstants = mkFRewrite3 closeOpen openOpen openClose
  where
    closeOpen _ _ = return Nothing -- Nothing we can do for labels.

    openOpen node facts =
      return $ Mon.liftM mkMiddle $ evaluateNode (`M.lookup` facts) node

    openClose node facts =
      return $ Mon.liftM mkLast $ evaluateNode (`M.lookup` facts) node

constantPropagationPass :: FuelMonad m => FwdPass m HNode ConstantFact
constantPropagationPass = FwdPass {
  fp_lattice = constantLattice,
  fp_transfer = transferConstants,
  fp_rewrite = propagateConstants `thenFwdRw` foldConstants
  }

runConstantPropagation :: HFunction -> M HFunction
runConstantPropagation hFunc = do
  (body, _, _) <- analyzeAndRewriteFwd constantPropagationPass
                  (JustC [hFnEntry hFunc]) (hFnBody hFunc) $
                  mapSingleton (hFnEntry hFunc) M.empty
  return hFunc{hFnBody = body}
