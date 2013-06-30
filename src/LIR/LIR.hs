{-# OPTIONS_GHC -Wall -Werror -i.. #-}
{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving #-}

module LIR.LIR(hirToLIR, Offset(..), RuntimeFn(..), StructId(..),
               JCondition(..), Constant(..), LBinOp(..), LNode(..),
               LFunction(..), PanicMap, lirDebugShowGraph)
       where

import Compiler.Hoopl
import qualified Data.Bits as B
import qualified Data.Map as M

import Source.Ast
import HIR.HIR
import Utils.Common
import Utils.Graph

-- Tags
--

--- Object layout

--  Pointers to objects are always tagged, using the two least
--  significant bits.  The tag values are
--
--   * Integers -              00
--   * Booleans -              10
--   * ClosureNode -           01
--   * ClosureBase -           11
--
--  ClosureNodes and ClosureBases are tagged pointers to heap
--  allocated objects.  For integers, the higher 30 / 62 bits first
--  word holds a fixed-width integer and for booleans the value is
--  held by the third lowest bit.
--
--   * Closures: closures are represented by a linked list of objects.
--   The last node of the linked list has the type ClosureBase; and
--   has the layout
--
--        ++++++++++++++++++++++++++++++++++
--        |               |                |
--        | Code Pointer  | Argument count |
--        |               |                |
--        ++++++++++++++++++++++++++++++++++
--
--     Other nodes of this linked list have the layout
--
--        +++++++++++++++++++++++++++++++++++++++++++++++++
--        |              |                |               |
--        | Next Pointer | Arguments left | This argument |
--        |              |                |               |
--        +++++++++++++++++++++++++++++++++++++++++++++++++

-- "Symbolic" addresses.  We haven't lowered these into concrete
-- calculations yet.
data LSymAddress = ArgsPtrLSA Int
                 | VarPlusSymL SSAVar Offset
                 | VarPlusVarL SSAVar SSAVar
                 deriving(Show, Eq, Ord)

data Offset = AppsLeftO | NextPtrO | NodeValueO | CodePtrO
            deriving(Show, Eq, Ord)

data RuntimeFn = AllocStructFn StructId | ForceFn (Rator Constant)
               deriving(Show, Eq, Ord)
data StructId = ClsrST ClsrId | ClsrAppNodeST deriving(Show, Eq, Ord)
data JCondition = JE | JL | JG | JNE deriving(Show, Eq, Ord)
data Constant = WordC Int | ClsrSizeC ClsrId | ClsrAppLimitC ClsrId
              | ClsrCodePtrC ClsrId | ClsrBaseTagC | ClsrNodeTagC
              | ClsrTagC | IntTagC | BoolTagC | BoolTrueC | BoolFalseC
              | ClearTagBitsC deriving(Show, Eq, Ord)

data LBinOp = BitAndLOp | BitOrLOp | BitXorLOp | AddLOp | SubLOp | MultLOp
            | DivLOp | LShiftLOp | RShiftLOp
            deriving(Show, Eq, Ord)

data LNode e x where
  LabelLN :: Label -> LNode C O

  CopyWordLN :: Rator Constant -> SSAVar -> LNode O O
  LoadWordLN :: LSymAddress -> SSAVar -> LNode O O
  StoreWordLN :: LSymAddress -> Rator Constant -> LNode O O
  CmpWordLN :: Rator Constant -> Rator Constant -> LNode O O
  CondMove :: JCondition -> Rator Constant -> Rator Constant -> SSAVar ->
              LNode O O
  BinOpLN :: LBinOp -> Rator Constant -> Rator Constant -> SSAVar -> LNode O O
  Phi2LN :: (Rator Constant, Label) -> (Rator Constant, Label) -> SSAVar ->
            LNode O O
  CallLN :: Rator ClsrId -> [Rator Constant] -> LNode O O
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

hirToLIR :: HFunction -> M LFunction
hirToLIR hFn = do
  let hGraph = hFnBody hFn
      oldSSALimit = hFnLastSSAVar hFn
  (lGraph, _, panicLbls) <- runIRMonad (mapConcatGraph (nodeMapFn, nodeMapFn, nodeMapFn)
                                        hGraph)
                   oldSSALimit M.empty
  let finalGraph = foldl (|*><*|) lGraph $ map snd $ M.elems panicLbls
  return LFunction{lFnName = hFnName hFn, lFnArgCount = hFnArgCount hFn,
                   lFnEntry = hFnEntry hFn, lFnBody = finalGraph}
  where
    nodeMapFn :: HNode e x -> IRMonad PanicMap (Graph LNode e x)

    nodeMapFn (LabelHN lbl) = return $ mkFirst $ LabelLN lbl

    nodeMapFn (LoadArgHN hInp out) =
      return $ mkMiddle $ LoadWordLN (ArgsPtrLSA hInp) out

    nodeMapFn (LoadLitHN (ClsrL clsrId) out) = genCreateClosure clsrId out

    nodeMapFn (LoadLitHN lit out) = do
      (code, value) <- litToConstant lit
      return $ code <*> mkMiddle (CopyWordLN value out)

    nodeMapFn (BinOpHN op inA inB out) =
      let genAssertTagI (VarR var) = genAssertTag (VarR var) IntTagC
          genAssertTagI (LitR _) = return emptyGraph
          [inA', inB'] = map ratorIntToConstant [inA, inB]
      in do
        assertLeft <- genAssertTagI inA
        assertRight <- genAssertTagI inB
        actualOp <- case op of
          DivOp -> genDivison inA' inB' out
          MultOp -> genMultiplication inA' inB' out
          LtOp -> genCmp LtOp inA' inB' out
          EqOp -> genCmp EqOp inA' inB' out
          _ -> genAddSubOp op inA' inB' out
        return $ assertLeft <*> assertRight <*> actualOp

    nodeMapFn (Phi2HN (inA, lblA) (inB, lblB) out) = do
      [(codeA', inA'), (codeB', inB')] <- mapM ratorLitToConstant [inA, inB]
      return $ codeA' <*> codeB' <*>
        mkMiddle (Phi2LN (inA', lblA) (inB', lblB) out)

    nodeMapFn (PushHN (VarR clsrVar) value out) = do
      assertT <- genAssertTag (VarR clsrVar) ClsrTagC
      (code', value') <- ratorLitToConstant value
      actualPush <- genPush clsrVar value' out
      return $ assertT <*> code' <*> actualPush

    nodeMapFn (PushHN (LitR clsrLit) value out) = do
      clsrVar <- freshVarName
      creationCode <- genCreateClosure clsrLit clsrVar
      (code', value') <- ratorLitToConstant value
      actualPush <- genPush clsrVar value' out
      return $ creationCode <*> code' <*> actualPush

    nodeMapFn (ForceHN (VarR value) result) = do
      tag <- freshVarName
      notNeeded <- freshLabel
      isClosure <- freshLabel
      let checkIfClosure = mkMiddles [
            BinOpLN BitAndLOp (VarR value) (LitR ClsrTagC) tag,
            CmpWordLN (VarR tag) (LitR ClsrTagC) ] <*>
                           mkLast (CJumpLN JNE notNeeded isClosure)
      appsLeft <- freshVarName
      tagCleared <- freshVarName
      forcingNeeded <- freshLabel
      let checkIfSaturated =
            mkFirst (LabelLN isClosure) <*>
            mkMiddles [
              BinOpLN BitAndLOp (LitR ClearTagBitsC) (VarR value) tagCleared,
              LoadWordLN (VarPlusSymL tagCleared AppsLeftO) appsLeft,
              CmpWordLN (VarR appsLeft) (LitR (WordC 0)) ] <*>
            mkLast (CJumpLN JNE notNeeded forcingNeeded)
      allDone <- freshLabel
      let doForce =
            mkFirst (LabelLN forcingNeeded) <*>
            mkMiddle (CallRuntimeLN (ForceFn (VarR tagCleared)) result) <*>
            mkLast (JumpLN allDone)
      let finalBlock = mkFirst (LabelLN allDone)
      return $ checkIfClosure |*><*| checkIfSaturated |*><*| doForce |*><*|
        finalBlock

    nodeMapFn (ForceHN lit result) = do
      (valCode, valConst) <- ratorLitToConstant lit
      return $ valCode <*> mkMiddle (CopyWordLN valConst result)

    nodeMapFn (CopyValueHN value result) = do
      (valCode, valConst) <- ratorLitToConstant value
      return $ valCode <*> mkMiddle (CopyWordLN valConst result)

    nodeMapFn (IfThenElseHN condition tLbl fLbl) =
      let cmp = CmpWordLN (ratorBoolToConstant condition) (LitR BoolTrueC)
          jmp = CJumpLN JE tLbl fLbl
      in return $ mkMiddle cmp <*> mkLast jmp

    nodeMapFn (JumpHN lbl) = return $ mkLast $ JumpLN lbl

    nodeMapFn (ReturnHN value) = do
      (valCode, valConst) <- ratorLitToConstant value
      return $ valCode <*> mkLast (ReturnLN valConst)

    genPush :: SSAVar -> Rator Constant -> SSAVar -> IRMonad PanicMap (Graph LNode O O)
    genPush clsrVar value newNode = do
      (validityCheck, appsLeft) <- checkPushValid (VarR clsrVar)
      appsLeft' <- freshVarName
      freshNode <- freshVarName
      return $ validityCheck <*>
        mkMiddles [
          BinOpLN SubLOp (VarR appsLeft) (LitR (WordC 1)) appsLeft',
          CallRuntimeLN (AllocStructFn ClsrAppNodeST) freshNode,
          StoreWordLN (VarPlusSymL freshNode AppsLeftO) (VarR appsLeft'),
          StoreWordLN (VarPlusSymL freshNode NextPtrO) (VarR clsrVar),
          StoreWordLN (VarPlusSymL freshNode NodeValueO) value,
          BinOpLN BitOrLOp (LitR ClsrNodeTagC) (VarR freshNode) newNode ]

    checkPushValid var = do
      panicLbl <- getPanicLabel "too many pushes!"
      appsLeft <- freshVarName
      pushOkay <- freshLabel
      untaggedVar <- freshVarName
      return (mkMiddles [
                 BinOpLN BitAndLOp (LitR ClearTagBitsC) var untaggedVar,
                 LoadWordLN (VarPlusSymL untaggedVar AppsLeftO) appsLeft,
                 CmpWordLN (VarR appsLeft) (LitR (WordC 0)) ] <*>
              mkLast (CJumpLN JE panicLbl pushOkay) |*><*|
              mkFirst (LabelLN pushOkay), appsLeft)

    genCmp op inA inB out = return $ mkMiddles [
      CmpWordLN inA inB,
      CondMove (opToJC op) (LitR BoolTrueC) (LitR BoolFalseC) out ]

    opToJC LtOp = JL
    opToJC EqOp = JE
    opToJC op =
      error $ "logic error: opToJC called incorrectly with " ++ show op

    genMultiplication inA inB result = do
      aRShifted <- freshVarName
      return $ mkMiddles [
        BinOpLN RShiftLOp inA (LitR (WordC 2)) aRShifted,
        BinOpLN MultLOp inB (VarR aRShifted) result ]

    genDivison inA inB result = do
      leftIsZero <- getPanicLabel "division by zero!"
      leftIsNotZero <- freshLabel
      resultUnshifted <- freshVarName
      let zeroCheck = mkMiddle (CmpWordLN inB (LitR (WordC 0))) <*>
                      mkLast (CJumpLN JE leftIsZero leftIsNotZero)
      return $ zeroCheck |*><*|
        mkFirst (LabelLN leftIsNotZero) <*>
        mkMiddles [ BinOpLN DivLOp inA inB resultUnshifted,
                    BinOpLN RShiftLOp (VarR resultUnshifted) (LitR (WordC 2))
                    result ]

    genAddSubOp op inA inB result =
      return $ mkMiddle $ BinOpLN (hOpToLOp op) inA inB result

    genCreateClosure :: ClsrId -> SSAVar -> IRMonad PanicMap (Graph LNode O O)
    genCreateClosure clsrId result = do
      untaggedClsr <- freshVarName
      return $ mkMiddles [
        CallRuntimeLN (AllocStructFn (ClsrST clsrId)) untaggedClsr,
        StoreWordLN (VarPlusSymL untaggedClsr AppsLeftO) (LitR (ClsrAppLimitC clsrId)),
        StoreWordLN (VarPlusSymL untaggedClsr CodePtrO) (LitR (ClsrCodePtrC clsrId)),
        BinOpLN BitOrLOp (LitR ClsrBaseTagC) (VarR untaggedClsr) result ]

    genAssertTag :: Rator Lit -> Constant -> IRMonad PanicMap (Graph LNode O O)
    genAssertTag (VarR var) tag = do
      header <- freshVarName
      extractedTag <- freshVarName
       -- TODO: make the panic message more
      panicLbl <- getPanicLabel "invalid type"
      checkPassed <- freshLabel
      return $ mkMiddles [
        LoadWordLN (VarPlusSymL var CodePtrO) header,
        BinOpLN BitAndLOp (VarR header) (LitR (WordC 3)) extractedTag,
        CmpWordLN (VarR extractedTag) (LitR tag) ] <*>
        mkLast (CJumpLN JE checkPassed panicLbl) |*><*|
        mkFirst (LabelLN checkPassed)

    genAssertTag (LitR (BoolL _)) BoolTagC = return emptyGraph
    genAssertTag (LitR (IntL _)) IntTagC = return emptyGraph
    genAssertTag (LitR (ClsrL _)) ClsrBaseTagC = return emptyGraph
    genAssertTag _ _ = do
      -- FIXME: this should fail at compile time
      panicLbl <- getPanicLabel "invalid type"
      unreachable <- freshLabel
      return $ mkLast (JumpLN panicLbl) |*><*| mkFirst (LabelLN unreachable)

    getPanicLabel error_str = do
      lblMap <- irGetCustom
      case error_str `M.lookup` lblMap of
        Just (lbl, _) -> return lbl
        Nothing -> do
          panicLbl <- freshLabel
          let panicBlock = mkFirst (LabelLN panicLbl) <*>
                           mkLast (PanicLN error_str)
          irPutCustom $ M.insert error_str (panicLbl, panicBlock) lblMap
          return panicLbl

    ratorIntToConstant (VarR v) = VarR v
    ratorIntToConstant (LitR w) = LitR (WordC w)

    ratorBoolToConstant (VarR v) = VarR v
    ratorBoolToConstant (LitR b) = LitR (if b then BoolTrueC else BoolFalseC)

    litToConstant :: Lit -> IRMonad PanicMap (Graph LNode O O, Rator Constant)
    litToConstant (ClsrL clsr) = do
      clsrVar <- freshVarName
      clsrCode <- genCreateClosure clsr clsrVar
      return (clsrCode, VarR clsrVar)
    litToConstant (BoolL b) =
      return (emptyGraph,
              LitR $ WordC $ ((if b then 1 else 0) `B.shift` 2) `B.setBit` 1)
    litToConstant (IntL i) = return (emptyGraph, LitR $ WordC $ i `B.shift` 2)

    ratorLitToConstant :: Rator Lit -> IRMonad PanicMap (Graph LNode O O,
                                                         Rator Constant)
    ratorLitToConstant (VarR v) = return (emptyGraph, VarR v)
    ratorLitToConstant (LitR lit) = litToConstant lit

    hOpToLOp PlusOp = AddLOp
    hOpToLOp MinusOp = SubLOp
    hOpToLOp MultOp = MultLOp
    hOpToLOp DivOp = DivLOp
    hOpToLOp op =
      error $ "logic error: hOpToLOp called incorrectly with " ++ show op


lirDebugShowGraph :: M [LFunction] -> String
lirDebugShowGraph fn =
  let functionList = runSimpleUniqueMonad $ runWithFuel maxBound fn
  in unlines $ map showLFunction functionList
  where
    showLFunction :: LFunction -> String
    showLFunction (LFunction name argC entry body) =
      let functionGraph = showGraph ((++ " ") . show) body
      in unlines ["ClsrId = " ++ show name, "ArgCount = " ++ show argC,
                  "EntryLabel = " ++ show entry, "Body = {",
                  functionGraph ++ "}"]
