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
eliminatePhi graph =
  let (varMap, constMap) = foldGraphNodes gatherCopies graph (M.empty, [])
  in do
    (GMany NothingO withVarCopies NothingO) <-
      mapConcatGraph (doNothingCO, copyVars varMap, doNothingOC) graph
    let withConstCopies = foldl copyOneConstant withVarCopies constMap
    return $ GMany NothingO withConstCopies NothingO
    where
      gatherCopies (Phi2LN a b result) =
        let f (VarR v, _) (vM, cM) = (M.insert v result vM, cM)
            f (LitR l, lbl) (vM, cM) = (vM, (lbl, l, result):cM)
        in f a . f b
      gatherCopies _ = id

      copyVars _ Phi2LN{} = return emptyGraph
      copyVars copyM node =
        let nothingDone = return $ mkMiddle node
        in case getLVarsWritten node of
          [] -> nothingDone
          [var] -> Mby.fromMaybe nothingDone $ do
            result <- var `M.lookup` copyM
            return $ return $ mkMiddles [node, CopyWordLN (VarR var) result]
          _ -> error "can't handle multiple writes!"

      copyOneConstant lMap (lbl, lit, result) =
        maybe lMap (insertCopy lMap lbl lit result) $ mapLookup lbl lMap
      insertCopy lMap lbl lit result block =
        let (JustC front, middles, JustC end) = blockToNodeList block
            newBlock =
              blockOfNodeList (JustC front, middles ++ [copyInst], JustC end)
            copyInst = CopyWordLN (LitR lit) result
        in mapInsert lbl newBlock lMap

      doNothingCO = return . mkFirst
      doNothingOC = return . mkLast

lirToMachineCode :: EchoesOptions -> (ClsrId -> Int) -> LFunction SSAVar ->
                    M [String]
lirToMachineCode opts argCounts (LFunction _ _ entry graph) = do
  graphWithoutPhis <- eliminatePhi graph
  (GMany NothingO lMap NothingO, stackSize) <- nullRegAlloc graphWithoutPhis
  let blockList = postorder_dfs_from lMap entry
  allCode <- mapM showBlock blockList
  let flatCode = concat allCode
  return $ prologue stackSize ++ (map show $ peepholeOpt flatCode)
  where
    prologue stackSize = map show $ machinePrologue stackSize
    mConcatMap f list = liftM concat $ mapM f list
    showBlock :: Block (RegInfNode RgLNode) C C -> M [MachineInst]
    showBlock block =
      let (JustC lbl :: MaybeC C ((RegInfNode RgLNode) C O),
           inner,
           JustC jmp :: MaybeC C ((RegInfNode RgLNode) O C))
            = blockToNodeList block
      in rNodeToMI argCounts lbl `mApp`
         mConcatMap (rNodeToMI argCounts) inner `mApp` rNodeToMI argCounts jmp
      where
        rNodeToMI :: (ClsrId -> Int) -> RegInfNode RgLNode e x ->
                     M [MachineInst]
        rNodeToMI aC (RegInfNode rI node) = lirNodeToMachineInst opts aC rI node

lirCodegen :: EchoesOptions -> [LFunction SSAVar] -> M String
lirCodegen opts fnList =
  let fnInfoMap = M.fromList $ map (\(LFunction n aC _ _) -> (n, aC)) fnList
      fnInfo = Mby.fromJust . flip M.lookup fnInfoMap
  in liftM ((asmHeader ++). unlines . concat) $
     mapM (toMachineCode fnInfo) fnList
  where toMachineCode fnInfo lFn = do
          code <- lirToMachineCode opts fnInfo lFn
          return $ ("closure_body_" ++ show (lFnName lFn) ++ ":"):code ++ [""]

lirDebugCodegen :: EchoesOptions -> M [LFunction SSAVar] -> String
lirDebugCodegen opts mFnList =
  runSimpleUniqueMonad $ runWithFuel maxBound (mFnList >>= lirCodegen opts)
