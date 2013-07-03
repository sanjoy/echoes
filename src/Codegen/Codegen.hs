{-# OPTIONS_GHC -Wall -Werror -fno-warn-warnings-deprecations #-}
{-# LANGUAGE GADTs, ScopedTypeVariables, FlexibleInstances #-}

module Codegen.Codegen(lirToMachineCode, lirDebugCodegen) where

import Compiler.Hoopl
import qualified Data.Map as M
import qualified Data.Maybe as Mby
import qualified Data.Set as S

import Codegen.Common
import Codegen.X86
import Utils.Common
import LIR.LIR

type RgLNode = GenLNode Reg
data RegInfNode a e x = RegInfNode (RegInfo Reg) (a e x)

instance NonLocal (RegInfNode (GenLNode r)) where
  entryLabel (RegInfNode _ (LabelLN label)) = label
  successors (RegInfNode _ PanicLN{}) = []
  successors (RegInfNode _ (CJumpLN _ lblA lblB)) = [lblA, lblB]
  successors (RegInfNode _ (JumpLN lbl)) = [lbl]
  successors (RegInfNode _ (ReturnLN _)) = []

dummyRegalloc :: Graph LNode C C -> Graph (RegInfNode RgLNode) C C
dummyRegalloc graph = graphMapBlocks mapBlocks graph
  where mapBlocks = blockMapNodes nodeMap
        nodeMap = RegInfNode ri . (mapGenLNodeRegs (\_ -> someReg))
        ri = freeReg `riAddFreeReg` (gcReg `riAddGCReg` riNewRegInfo)
        [someReg, gcReg, freeReg] = S.toList generalRegSet

lirToMachineCode :: (ClsrId -> Int) -> LFunction SSAVar -> [String]
lirToMachineCode argCounts (LFunction _ _ entry graph) =
  let (GMany NothingO lMap NothingO) = dummyRegalloc graph
      blockList = postorder_dfs_from lMap entry
  in concatMap showBlock blockList
  where
    showBlock :: Block (RegInfNode RgLNode) C C -> [String]
    showBlock block =
          let (JustC lbl :: MaybeC C ((RegInfNode RgLNode) C O),
               inner,
               JustC jmp :: MaybeC C ((RegInfNode RgLNode) O C))
                = blockToNodeList block
              loweredInsts =
                rNodeToMI argCounts lbl ++
                concatMap (rNodeToMI argCounts) inner ++
                rNodeToMI argCounts jmp
          in map show loweredInsts
      where rNodeToMI aC (RegInfNode rI node) = lirNodeToMachineInst aC rI node

lirDebugCodegen :: M [LFunction SSAVar] -> String
lirDebugCodegen fn =
  let functionList = runSimpleUniqueMonad $ runWithFuel maxBound fn
      fnInfoMap =
        M.fromList $ map (\(LFunction n aC _ _) -> (n, aC)) functionList
      fnToMCode = unlines . lirToMachineCode (Mby.fromJust .
                                              flip M.lookup fnInfoMap)
  in unlines $ map fnToMCode functionList
