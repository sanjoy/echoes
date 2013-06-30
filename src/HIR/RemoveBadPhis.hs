{-# OPTIONS_GHC -Wall -Werror -i.. #-}
{-# LANGUAGE GADTs, RankNTypes #-}

module HIR.RemoveBadPhis(runRemoveBadPhis) where

import Compiler.Hoopl

import HIR.HIR
import Utils.Common
import Utils.Graph

runRemoveBadPhis :: HFunction -> M HFunction
runRemoveBadPhis hFn =
  do
    let reacheableLabels = labelsUsed $ hFnBody hFn
    newGraph <-
        mapConcatGraph (closeOpenDummy, removePhiIfBad reacheableLabels,
                        openCloseDummy) (hFnBody hFn)
        -- We need not have used mapConcatGraph here since there are
        -- more specific functions in Compiler.Hoopl for things like
        -- this.  OTOH, this is a decent sanity check for
        -- mapConcatGraph
    return hFn{hFnBody = newGraph}
  where
    removePhiIfBad :: LabelSet -> HNode O O -> M (Graph HNode O O)
    removePhiIfBad rLbls whole@(Phi2HN (iA, lA) (iB, lB) result)
      | lA `notMember` rLbls = return $ mkMiddle $ CopyValueHN iB result
      | lB `notMember` rLbls = return $ mkMiddle $ CopyValueHN iA result
      | otherwise = return $ mkMiddle whole
    removePhiIfBad _ node = return $ mkMiddle node

    closeOpenDummy node = return $ mkFirst node
    openCloseDummy node = return $ mkLast node

    notMember a b = not (setMember a b)
