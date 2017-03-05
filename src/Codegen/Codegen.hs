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

type PHIInfo = (M.Map SSAVar SSAVar, [(Label, Constant, SSAVar)])

eliminatePhi :: Graph LNode C C -> M (Graph LNode C C)
eliminatePhi graph =
  let (varMap, constMap) = foldGraphNodes gatherCopies graph (M.empty, [])
  in do
    (GMany NothingO withVarCopies NothingO) <-
      mapConcatGraph (doNothingCO, copyVars varMap, doNothingOC) graph
    let withConstCopies = foldl copyOneConstant withVarCopies constMap
    return $ GMany NothingO withConstCopies NothingO
    where
      gatherCopies :: forall e x. LNode e x -> PHIInfo -> PHIInfo
      gatherCopies (Phi2LN a b result) =
        let f (VarR v, _) (varMap, constMap) = (M.insert v result varMap, constMap)
            f (LitR l, lbl) (varMap, constMap) = (varMap, (lbl, l, result):constMap)
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
      insertCopy ::
          LabelMap (Block LNode C C) -> Label -> Constant -> SSAVar -> Block LNode C C -> LabelMap (Block LNode C C)
      insertCopy lMap lbl lit result (BlockCC front middles back) =
        let newBlockMiddle = blockFromList $ (blockToList middles) ++ [copyInst]
            copyInst = CopyWordLN (LitR lit) result
        in mapInsert lbl (BlockCC front newBlockMiddle back) lMap

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
      let BlockCC lbl innerBlock jmp = block
          innerNodes = blockToList innerBlock
      in rNodeToMI argCounts lbl `mApp`
         mConcatMap (rNodeToMI argCounts) innerNodes `mApp` rNodeToMI argCounts jmp
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
