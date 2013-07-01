{-# OPTIONS_GHC -Wall -Werror -fno-warn-warnings-deprecations #-}
{-# LANGUAGE GADTs, ScopedTypeVariables #-}

module Codegen.Codegen(lirToMachineCode, lirDebugCodegen) where

import Compiler.Hoopl
import qualified Data.Set as S

import Codegen.X86
import Utils.Common
import LIR.LIR

type RgLNode = GenLNode Reg

dummyRegalloc :: Graph LNode C C -> Graph RgLNode C C
dummyRegalloc = graphMapBlocks mapBlocks
  where mapBlocks = blockMapNodes (mapGenLNodeRegs (\_ -> someReg))
        someReg = head $ S.toList $ generalRegSet

lirToMachineCode :: LFunction SSAVar -> [String]
lirToMachineCode (LFunction _ _ entry graph) =
  let (GMany NothingO lMap NothingO) = dummyRegalloc graph
      blockList = postorder_dfs_from lMap entry
  in concatMap showBlock blockList
  where
    showBlock :: Block RgLNode C C -> [String]
    showBlock block =
          let (JustC lbl :: MaybeC C (RgLNode C O),
               inner,
               JustC jmp :: MaybeC C (RgLNode O C)) = blockToNodeList block
              loweredInsts = lirNodeToMachineInst lbl ++
                             concatMap lirNodeToMachineInst inner ++
                             lirNodeToMachineInst jmp
          in map show loweredInsts

lirDebugCodegen :: M [LFunction SSAVar] -> String
lirDebugCodegen fn =
  let functionList = runSimpleUniqueMonad $ runWithFuel maxBound fn
  in unlines $ map (unlines . lirToMachineCode) functionList
