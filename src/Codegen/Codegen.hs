{-# OPTIONS_GHC -Wall -Werror -fno-warn-warnings-deprecations #-}
{-# LANGUAGE GADTs, ScopedTypeVariables, FlexibleInstances #-}

module Codegen.Codegen(lirToMachineCode, lirDebugCodegen, lirCodegen)
       where

import Compiler.Hoopl
import Control.Monad
import qualified Data.Map as M
import qualified Data.Maybe as Mby

import Codegen.RegAlloc
import Codegen.X86
import LIR.LIR
import Utils.Common
import Utils.Graph

eliminatePhi :: Graph LNode C C -> M (Graph LNode C C)
eliminatePhi graph@(GMany NothingO lMap NothingO) =
  let copiesToInsert = foldGraphNodes gatherCopies graph []
      graphWithCopies = foldl insertCopies lMap copiesToInsert
  in mapConcatGraph (doNothingCO, removePhis, doNothingOC)
     (GMany NothingO graphWithCopies NothingO)
     where gatherCopies (Phi2LN (inA, lblA) (inB, lblB) result) =
             (++) [(lblA, inA, result), (lblB, inB, result)]
           gatherCopies _ = id

           insertCopies :: LabelMap (Block LNode C C) ->
                           (Label, Rator Constant, SSAVar) ->
                           LabelMap (Block LNode C C)
           insertCopies lblMap (lbl, rator, result) =
             let (front, list, back) =
                   blockToNodeList $ Mby.fromJust $ mapLookup lbl lblMap
                 copyNode = CopyWordLN rator result
                 newBlock = blockOfNodeList (front, list ++ [copyNode], back)
             in mapInsert lbl newBlock lblMap

           removePhis Phi2LN{} = return emptyGraph
           removePhis node = return $ mkMiddle node

           doNothingCO = return . mkFirst
           doNothingOC = return . mkLast

lirToMachineCode :: (ClsrId -> Int) -> LFunction SSAVar -> M [String]
lirToMachineCode argCounts (LFunction _ _ entry graph) = do
  graphWithoutPhis <- eliminatePhi graph
  (GMany NothingO lMap NothingO, stackSize) <- nullRegAlloc graphWithoutPhis
  let blockList = postorder_dfs_from lMap entry
  eachBlock <- mapM showBlock blockList
  return $ prologue stackSize ++ concat eachBlock
  where
    prologue stackSize = map show $ machinePrologue stackSize
    mConcatMap f list = liftM concat $ mapM f list
    showBlock :: Block (RegInfNode RgLNode) C C -> M [String]
    showBlock block =
      let (JustC lbl :: MaybeC C ((RegInfNode RgLNode) C O),
           inner,
           JustC jmp :: MaybeC C ((RegInfNode RgLNode) O C))
            = blockToNodeList block
      in do
        loweredInsts <- rNodeToMI argCounts lbl `mApp`
                        mConcatMap (rNodeToMI argCounts) inner `mApp`
                        rNodeToMI argCounts jmp
        return $ map show loweredInsts
      where rNodeToMI aC (RegInfNode rI node) = lirNodeToMachineInst aC rI node

lirCodegen :: [LFunction SSAVar] -> M String
lirCodegen fnList =
  let fnInfoMap = M.fromList $ map (\(LFunction n aC _ _) -> (n, aC)) fnList
      fnInfo = Mby.fromJust . flip M.lookup fnInfoMap
  in liftM ((asmHeader ++). unlines . concat) $
     mapM (toMachineCode fnInfo) fnList
  where toMachineCode fnInfo lFn = do
          code <- lirToMachineCode fnInfo lFn
          return $ ("closure_body_" ++ show (lFnName lFn) ++ ":"):code ++ [""]

lirDebugCodegen :: M [LFunction SSAVar] -> String
lirDebugCodegen mFnList =
  runSimpleUniqueMonad $ runWithFuel maxBound (mFnList >>= lirCodegen)
