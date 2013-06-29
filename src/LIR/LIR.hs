{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -i..  #-}
{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving #-}

module LIR.LIR where

import Compiler.Hoopl
import qualified Data.Bits as B
import qualified Data.Map as M

import Source.Ast
import HIR.HIR
import Utils.Common
import Utils.Graph

-- Tags
--
--  * Integers -              00
--  * ClosureNodes -          01
--  * ClosureBase -           11
--  * Booleans -              10

-- "Symbolic" addresses.  We haven't lowered these into concrete
-- calculations yet.
data LSymAddress = ArgsPtrLSA Int
                 | VarPlusSymL SSAVar Offset
                 | VarPlusVarL SSAVar SSAVar
                 deriving(Show, Eq, Ord)

data Offset = AppsLeftO | NextPtrO | NodeValueO | CodePtrO
            deriving(Show, Eq, Ord)

data RuntimeFn = AllocStructFn StructId deriving(Show, Eq, Ord)
data StructId = ClsrST ClsrId | ClsrAppNodeST deriving(Show, Eq, Ord)
data JCondition = JE | JL | JG | Unconditional deriving(Show, Eq, Ord)
data Constant = WordC Int | ClsrSizeC ClsrId | ClsrAppLimitC ClsrId
              | ClsrCodePtrC ClsrId | ClsrBaseTagC | ClsrNodeTagC
              | ClsrTagC | IntTagC | BoolTagC | BoolTrueC | BoolFalseC
              deriving(Show, Eq, Ord)

data LBinOp = BitAndLOp | BitOrLOp | BitXorLOp | AddLOp | SubLOp | MultLOp
            | DivLOp | LShiftLOp | RShiftLOp
            deriving(Show, Eq, Ord)

data LNode e x where
  LabelLN :: Label -> LNode C O

  LoadLitWordLN :: Int -> SSAVar -> LNode O O
  LoadWordLN :: LSymAddress -> SSAVar -> LNode O O
  StoreWordLN :: LSymAddress -> Rator Constant -> LNode O O
  CmpWordLN :: Rator Constant -> Rator Constant -> LNode O O
  CondMove :: JCondition -> Rator Constant -> Rator Constant -> SSAVar ->
              LNode O O
  BinOpLN :: LBinOp -> Rator Constant -> Rator Constant -> SSAVar -> LNode O O
  Phi2LN :: (Rator Constant, Label) -> (Rator Constant, Label) -> SSAVar ->
            LNode O O
  CallLN :: Rator ClsrId -> [Rator Constant] -> LNode O O
  CopyValueLN :: Rator Constant -> SSAVar -> LNode O O
  CallRuntimeLN :: RuntimeFn -> SSAVar -> LNode O O

  PanicLN :: String -> LNode O C
  CJumpLN :: JCondition -> Label {- True -} -> Label {- Fallthrough -} ->
             LNode O C
  JumpLN :: Label -> LNode O C
  ReturnLN :: Rator Constant -> LNode O C
deriving instance Show(LNode e x)

instance NonLocal LNode where
  entryLabel (LabelLN label) = label
  successors PanicLN{} = []
  successors (CJumpLN _ lblA lblB) = [lblA, lblB]
  successors (JumpLN lbl) = [lbl]
  successors (ReturnLN _) = []

data LFunction = LFunction { lFnName :: ClsrId, lFnArgCount :: Int,
                             lFnEntry :: Label, lFnBody :: Graph LNode C C }

type PanicMap = (M.Map String (Label, Graph LNode C C))

hirToLIR :: SSAVar -> Graph HNode C C -> M (Graph LNode C C)
hirToLIR oldLimit hGraph = do
  (lGraph, _, _) <- runIRMonad (mapConcatGraph (nodeMapFn, nodeMapFn, nodeMapFn)
                                hGraph)
                   oldLimit M.empty
  return lGraph
  where
    nodeMapFn :: HNode e x -> IRMonad PanicMap (Graph LNode e x)

    nodeMapFn (LabelHN lbl) = return $ mkFirst $ LabelLN lbl

    nodeMapFn (LoadArgHN hInp out) =
      return $ mkMiddle $ LoadWordLN (ArgsPtrLSA hInp) out

    nodeMapFn (LoadLitHN (ClsrL clsrId) out) = genCreateClosure clsrId out

    nodeMapFn (LoadLitHN lit out) =
      return $ mkMiddle $ LoadLitWordLN (litToWord lit) out

    nodeMapFn (BinOpHN op inA inB out) = do
      assertLeft <- genAssertTag inA IntTagC
      assertRight <- genAssertTag inB IntTagC
      let [inA', inB'] = map ratorIntToConstant [inA, inB]
      actualOp <- case op of
        DivOp -> genDivison inA' inB' out
        MultOp -> genMultiplication inA' inB' out
        LtOp -> genCmp LtOp inA' inB' out
        EqOp -> genCmp EqOp inA' inB' out
        _ -> genAddSubOp op inA' inB' out
      return $ assertLeft <*> assertRight <*> actualOp

    nodeMapFn (Phi2HN (inA, lblA) (inB, lblB) out) =
      let [inA', inB'] = map ratorLitToConstant [inA, inB]
      in return $ mkMiddle $ Phi2LN (inA', lblA) (inB', lblB) out

    nodeMapFn (PushHN (VarR clsrVar) value out) = do
      assertT <- genAssertTag clsrVar ClsrTagC
      actualPush <- genPush clsrVar (ratorLitToConstant value) out
      return $ assertT <*> actualPush

    nodeMapFn (PushHN (LitR clsrLit) value out) = do
      clsrVar <- freshVarName
      creationCode <- genCreateClosure clsrLit clsrVar
      actualPush <- genPush clsrVar (ratorLitToConstant value) out
      return $ creationCode <*> actualPush

    nodeMapFn ForceHN{} = undefined

    nodeMapFn (CopyValueHN value result) =
      return $ mkMiddle $ CopyValueLN (ratorLitToConstant value) result

    nodeMapFn (IfThenElseHN condition tLbl fLbl) =
      let cmp = CmpWordLN (ratorBoolToConstant condition) (LitR BoolTrueC)
          jmp = CJumpLN JE tLbl fLbl
      in return $ mkMiddle cmp <*> mkLast jmp

    nodeMapFn (JumpHN lbl) = return $ mkLast $ JumpLN lbl

    nodeMapFn (ReturnHN value) =
      return $ mkLast $ ReturnLN $ ratorLitToConstant value

    genPush clsrVar value newNode = do
      (validityCheck, appsLeft) <- checkPushValid clsrVar
      appsLeft' <- freshVarName
      taggedNext <- freshVarName
      return $ validityCheck <*>
        mkMiddles [
          BinOpLN SubLOp (VarR appsLeft) (LitR (WordC 1)) appsLeft',
          CallRuntimeLN (AllocStructFn ClsrAppNodeST) newNode,
          StoreWordLN (VarPlusSymL newNode AppsLeftO) (VarR appsLeft'),
          BinOpLN BitOrLOp (VarR clsrVar) (LitR ClsrNodeTagC) taggedNext,
          StoreWordLN (VarPlusSymL newNode NextPtrO) (VarR taggedNext),
          StoreWordLN (VarPlusSymL newNode NodeValueO) value
          ]

    checkPushValid = undefined

    genCmp op inA inB out = return $ mkMiddles [
      CmpWordLN inA inB,
      CondMove (opToJC op) (LitR BoolTrueC) (LitR BoolFalseC) out ]

    opToJC LtOp = JL
    opToJC EqOp = JE
    opToJC _ = error "logic error"

    genMultiplication inA inB out = do
      aRShifted <- freshVarName
      return $ mkMiddles [
        BinOpLN RShiftLOp inA (LitR (WordC 2)) aRShifted,
        BinOpLN MultLOp inB (VarR aRShifted) out
        ]

    genDivison inA inB out = do
      leftIsZero <- getPanicLabel "division by zero!"
      leftIsNotZero <- freshLabel
      let zeroCheck = mkMiddle (CmpWordLN inB (LitR (WordC 0))) <*>
                      mkLast (CJumpLN JE leftIsZero leftIsNotZero)
      return $ zeroCheck |*><*|
        mkFirst (LabelLN leftIsNotZero) <*>
        mkMiddle (BinOpLN DivLOp inA inB out)

    genAddSubOp op inA inB out =
      return $ mkMiddle $ BinOpLN (hOpToLOp op) inA inB out

    genCreateClosure :: ClsrId -> SSAVar -> IRMonad PanicMap (Graph LNode O O)
    genCreateClosure clsrId ssaVar = do
      taggedClsr <- freshVarName
      return $ mkMiddles [
        CallRuntimeLN (AllocStructFn (ClsrST clsrId)) ssaVar,
        StoreWordLN (VarPlusSymL ssaVar AppsLeftO) (LitR (ClsrAppLimitC clsrId)),
        BinOpLN BitOrLOp (LitR ClsrBaseTagC) (VarR ssaVar) taggedClsr,
        StoreWordLN (VarPlusSymL ssaVar CodePtrO) (VarR taggedClsr) ]

    genAssertTag = undefined
    getPanicLabel = undefined

    ratorIntToConstant (VarR v) = VarR v
    ratorIntToConstant (LitR w) = LitR (WordC w)

    ratorBoolToConstant (VarR v) = VarR v
    ratorBoolToConstant (LitR b) = LitR (if b then BoolTrueC else BoolFalseC)

    ratorLitToConstant (VarR v) = VarR v
    ratorLitToConstant (LitR lit) = LitR $ WordC $ litToWord lit

    litToWord (BoolL b) = ((if b then 1 else 0) `B.shift` 2) `B.setBit` 1
    litToWord (IntL i) = i `B.shift` 2
    litToWord (ClsrL _) = error "logic error"

    hOpToLOp PlusOp = AddLOp
    hOpToLOp MinusOp = SubLOp
    hOpToLOp MultOp = MultLOp
    hOpToLOp DivOp = DivLOp
    hOpToLOp _ = error "logic error"
