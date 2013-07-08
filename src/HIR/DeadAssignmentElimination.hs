{-# OPTIONS_GHC -Wall -Werror -i..  #-}
{-# LANGUAGE GADTs, RankNTypes #-}
module HIR.DeadAssignmentElimination(deadAssignmentEliminationPass,
                                     runDeadAssignmentElimination) where

import Compiler.Hoopl
import qualified Data.Maybe as Mby
import qualified Data.List as L
import qualified Data.Set as S

import HIR.HIR
import Utils.Common

type DAEFact = S.Set SSAVar

daeLattice :: DataflowLattice DAEFact
daeLattice = DataflowLattice {
  fact_name = "Dead Code Elimination",
  fact_bot = S.empty,
  fact_join = optimizedUnion
  } where
  optimizedUnion _ (OldFact old) (NewFact new)
    | S.null new = (NoChange, old)
    | otherwise = (SomeChange, old `S.union` new)

transferDAE :: BwdTransfer HNode DAEFact
transferDAE = mkBTransfer3 closeOpen openOpen openClose
  where
    closeOpen _ = id

    openOpen node f =
      let rVars = getHVarsRead node
          wVars = getHVarsWritten node
          clearDefinedVars = L.foldl (flip S.delete) f wVars
      in L.foldl (flip S.insert) clearDefinedVars rVars

    openClose :: HNode O C -> FactBase DAEFact -> DAEFact
    openClose node fBase =
      let rVars = getHVarsRead node
          wVars = getHVarsWritten node
          totalFacts = S.unions $ map getFact $ successors node
          clearDefinedVars = L.foldl (flip S.delete) totalFacts wVars
      in L.foldl (flip S.insert) clearDefinedVars rVars
      where getFact lbl = Mby.fromMaybe S.empty $ mapLookup lbl fBase

eliminateDeadAssignments :: forall m. FuelMonad m => BwdRewrite m HNode DAEFact
eliminateDeadAssignments = mkBRewrite3 closeOpen openOpen openClose
  where
    closeOpen _ _ = return Nothing
    openClose _ _ = return Nothing

    openOpen node facts = if any (`S.member` facts) (getHVarsWritten node)
                          then return Nothing
                          else return $ Just emptyGraph

deadAssignmentEliminationPass :: FuelMonad m => BwdPass m HNode DAEFact
deadAssignmentEliminationPass = BwdPass {
  bp_lattice = daeLattice,
  bp_transfer = transferDAE,
  bp_rewrite = eliminateDeadAssignments
  }

runDeadAssignmentElimination :: HFunction -> M HFunction
runDeadAssignmentElimination hFunc = do
  (body, _, _) <- analyzeAndRewriteBwd deadAssignmentEliminationPass
                  (JustC [hFnEntry hFunc]) (hFnBody hFunc) $
                  mapSingleton (hFnEntry hFunc) S.empty
  return hFunc{hFnBody = body}
