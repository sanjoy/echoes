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
import Utils.Common
import LIR.LIR

lirToMachineCode :: (ClsrId -> Int) -> LFunction SSAVar -> M [String]
lirToMachineCode argCounts (LFunction _ _ entry graph) = do
  (GMany NothingO lMap NothingO, stackSize) <- nullRegAlloc graph
  let blockList = postorder_dfs_from lMap entry
  eachBlock <- mapM (showBlock stackSize) blockList
  return $ concat eachBlock
  where
    mConcatMap f list = liftM concat $ mapM f list
    showBlock :: Int -> Block (RegInfNode RgLNode) C C -> M [String]
    showBlock stackSize block =
      let (JustC lbl :: MaybeC C ((RegInfNode RgLNode) C O),
           inner,
           JustC jmp :: MaybeC C ((RegInfNode RgLNode) O C))
            = blockToNodeList block
      in do
        loweredInsts <- rNodeToMI argCounts lbl `mApp`
                        mConcatMap (rNodeToMI argCounts) inner `mApp`
                        rNodeToMI argCounts jmp
        return $ map show (machinePrologue stackSize ++ loweredInsts)
      where rNodeToMI aC (RegInfNode rI node) = lirNodeToMachineInst aC rI node

lirCodegen :: [LFunction SSAVar] -> M String
lirCodegen fnList =
  let fnInfoMap = M.fromList $ map (\(LFunction n aC _ _) -> (n, aC)) fnList
      fnInfo = Mby.fromJust . flip M.lookup fnInfoMap
  in liftM (unlines . concat) $ mapM (toMachineCode fnInfo) fnList
  where toMachineCode fnInfo lFn = do
          code <- lirToMachineCode fnInfo lFn
          return $ ("closure_body_" ++ show (lFnName lFn) ++ ":"):code ++ [""]

lirDebugCodegen :: M [LFunction SSAVar] -> String
lirDebugCodegen mFnList =
  runSimpleUniqueMonad $ runWithFuel maxBound (mFnList >>= lirCodegen)
