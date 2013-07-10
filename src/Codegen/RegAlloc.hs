{-# OPTIONS_GHC -Wall -Werror -i.. #-}
{-# LANGUAGE FlexibleInstances, GADTs, TupleSections, RankNTypes #-}

module Codegen.RegAlloc(RgLNode, RegInfNode(..), nullRegAlloc) where

import Compiler.Hoopl
import Control.Monad
import qualified Data.Map as M
import qualified Data.Maybe as Mby
import qualified Data.Set as S

import Codegen.Common
import Codegen.X86
import LIR.LIR
import Utils.Common
import Utils.Graph

type RgLNode = GenLNode Reg
data RegInfNode a e x = RegInfNode (RegInfo Reg) (a e x)

instance NonLocal (RegInfNode (GenLNode r)) where
  entryLabel (RegInfNode _ (LabelLN label)) = label
  successors (RegInfNode _ PanicLN{}) = []
  successors (RegInfNode _ (CJumpLN _ lblA lblB)) = [lblA, lblB]
  successors (RegInfNode _ (JumpLN lbl)) = [lbl]
  successors (RegInfNode _ (ReturnLN _)) = []

nullRegAlloc :: Graph LNode C C -> M (Graph (RegInfNode RgLNode) C C, Int)
nullRegAlloc graph =
  let (frameSize, varMaps) = foldGraphNodes accSSAVar graph (0, M.empty)
  in liftM (, frameSize) $
     mapConcatGraph (spillCO, spillOO varMaps, spillOC varMaps) graph
  where
    accSSAVar :: forall e x. LNode e x -> (Int, M.Map SSAVar Int) ->
                 (Int, M.Map SSAVar Int)
    accSSAVar node (maxIndex, slots) =
      let insVarIfNeeded (curIdx, varToIdx) v =
            if v `M.member` varToIdx then (curIdx, varToIdx)
            else (curIdx + 1, M.insert v curIdx varToIdx)
      in foldl insVarIfNeeded (maxIndex, slots) (getLVarsWritten node)

    -- In this "null" register allocator, we simply spill *all* the
    -- SSAVars to the stack; and emit code to load / store these on
    -- every instruction.  This is pretty much the worst we can do but
    -- also the easiest thing that can possibly work.

    spillCO :: LNode C O -> M (Graph (RegInfNode RgLNode) C O)
    spillCO (LabelLN lbl) =
      return $ mkFirst $ RegInfNode allRegsFree (LabelLN lbl)

    spillOO :: M.Map SSAVar Int -> LNode O O ->
               M (Graph (RegInfNode RgLNode) O O)
    spillOO slots node =
      let [varsRead, varsWritten] =
            map (\f -> f node) [getLVarsRead, getLVarsWritten]
          varsTouched = varsRead ++ varsWritten
          assignRegs = M.fromList $ zip varsTouched $ S.toList generalRegSet

          -- Loads from the stack
          (freeRegsAfterLoads, loadInsts) =
            foldl (genLoadInst assignRegs slots) (allRegsFree, []) varsRead

          (_, storeInsts) =
            let regsWritten = map (`directLookup` assignRegs) varsRead
            in foldl genStoreInst
               (regsWritten `riRemoveFreeRegL` allRegsFree, [])
               varsWritten
          genStoreInst :: (RegInfo Reg, [RegInfNode RgLNode O O]) -> SSAVar ->
                          (RegInfo Reg, [RegInfNode RgLNode O O])
          genStoreInst (freeRegsTillNow, stores) ssaVar =
            let reg = ssaVar `directLookup` assignRegs
                offset = ssaVar `directLookup` slots
            in (reg `riRemoveFreeReg` freeRegsTillNow,
                RegInfNode freeRegsTillNow (
                  StoreWordLN (StackOffset offset) (VarR reg)):stores)

          newNode =
            RegInfNode freeRegsAfterLoads $ mapGenLNodeRegs
            (`directLookup` assignRegs) node

      in return $ mkMiddles $ loadInsts ++ [newNode] ++ storeInsts

    spillOC :: M.Map SSAVar Int -> LNode O C ->
               M (Graph (RegInfNode RgLNode) O C)
    spillOC slots node =
      let varsRead = getLVarsRead node
          assignRegs = M.fromList $ zip varsRead $ S.toList generalRegSet

          -- Loads from the stack
          (freeRegsAfterLoads, loadInsts) =
            foldl (genLoadInst assignRegs slots) (allRegsFree, []) varsRead

          newNode =
            RegInfNode freeRegsAfterLoads $ mapGenLNodeRegs
            (`directLookup` assignRegs) node

      in return $ mkMiddles loadInsts <*> mkLast newNode

    genLoadInst :: M.Map SSAVar Reg -> M.Map SSAVar Int ->
                   (RegInfo Reg, [RegInfNode RgLNode O O]) -> SSAVar ->
                   (RegInfo Reg, [RegInfNode RgLNode O O])
    genLoadInst assignRegs slots (freeRegsTillNow, loads) ssaVar =
      let reg = ssaVar `directLookup` assignRegs
          offset = ssaVar `directLookup` slots
      in (reg `riRemoveFreeReg` freeRegsTillNow,
          RegInfNode freeRegsTillNow (
            LoadWordLN (StackOffset offset) reg):loads)

    allRegsFree = riAddFreeReg' generalRegSet riNewRegInfo
    directLookup k m = Mby.fromMaybe crash (M.lookup k m)
      where crash = error $ "directLookup: " ++ show k ++ " not in " ++ show m
    riRemoveFreeRegL = flip (foldl (flip riRemoveFreeReg))
