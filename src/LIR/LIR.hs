{-# OPTIONS_GHC -Wall -Werror -i.. #-}
{-# LANGUAGE GADTs, RankNTypes, StandaloneDeriving, TypeSynonymInstances,
    FlexibleInstances, DeriveFunctor #-}

module LIR.LIR(hirToLIR, Offset(..), RuntimeFn(..), StructId(..),
               SymAddress(..), JCondition(..), Constant(..), LBinOp(..), LNode,
               GenLNode(..), LFunction(..), PanicMap, mapGenLNodeRegs,
               getLVarsWritten, getLVarsRead, lirDebugShowGraph)
       where

import Compiler.Hoopl
import qualified Data.Bits as B
import qualified Data.Map as M

import Source.Ast
import HIR.HIR
import Utils.Common
import Utils.Graph

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
data SymAddress r = ArgsPtrSA Int | StackOffsetSA Int | VarPlusSymSA r Offset
                  | VarPlusVarSA r r
                  deriving(Show, Eq, Ord)

deriving instance Functor(SymAddress)

data Offset = AppsLeftO | NextPtrO | NodeValueO | CodePtrO
            deriving(Show, Eq, Ord)

data RuntimeFn reg = AllocStructFn StructId | ForceFn reg
                   deriving(Show, Eq, Ord)
data StructId = ClsrST ClsrId | ClsrAppNodeST deriving(Show, Eq, Ord)
data JCondition = JE | JL | JG | JNE deriving(Show, Eq, Ord)
data Constant = WordC Int | ClsrAppLimitC ClsrId | ClsrCodePtrC ClsrId
              | ClsrBaseTagC | ClsrNodeTagC | ClsrTagC | IntTagC | BoolTagC
              | BoolTrueC | BoolFalseC | ClearTagBitsC
              deriving(Show, Eq, Ord)

data LBinOp = BitAndLOp | BitOrLOp | BitXorLOp | AddLOp | SubLOp | MultLOp
            | DivLOp | LShiftLOp | RShiftLOp
            deriving(Show, Eq, Ord)

data GenLNode r e x where
  LabelLN :: Label -> GenLNode r C O

  CopyWordLN :: GenRator r Constant -> r -> GenLNode r O O
  LoadWordLN :: SymAddress r -> r -> GenLNode r O O
  StoreWordLN :: SymAddress r -> GenRator r Constant -> GenLNode r O O
  CmpWordLN :: GenRator r Constant -> r -> GenLNode r O O
  BinOpLN :: LBinOp -> GenRator r Constant -> GenRator r Constant -> r ->
             GenLNode r O O
  Phi2LN :: (GenRator r Constant, Label) -> (GenRator r Constant, Label) ->
            r -> GenLNode r O O
  CallRuntimeLN :: RuntimeFn r -> r -> GenLNode r O O

  PanicLN :: String -> GenLNode r O C
  CJumpLN :: JCondition -> Label {- True -} -> Label {- Fallthrough -} ->
             GenLNode r O C
  JumpLN :: Label -> GenLNode r O C
  ReturnLN :: GenRator r Constant -> GenLNode r O C

type LNode = GenLNode SSAVar
deriving instance Show(LNode e x)

mapGenLNodeRegs :: (r -> s) -> GenLNode r e x -> GenLNode s e x
mapGenLNodeRegs _ (LabelLN lbl) = LabelLN lbl
mapGenLNodeRegs f (CopyWordLN g r) = CopyWordLN (mapGenRator f g) (f r)
mapGenLNodeRegs f (LoadWordLN addr r) = LoadWordLN (fmap f addr) (f r)
mapGenLNodeRegs f (StoreWordLN addr g) =
  StoreWordLN (fmap f addr) (mapGenRator f g)
mapGenLNodeRegs f (CmpWordLN g1 g2) = CmpWordLN (mapGenRator f g1) (f g2)
mapGenLNodeRegs f (BinOpLN op g1 g2 r) =
  BinOpLN op (mapGenRator f g1) (mapGenRator f g2) (f r)
mapGenLNodeRegs f (Phi2LN (g1, l1) (g2, l2) r) =
  Phi2LN (mapGenRator f g1, l1) (mapGenRator f g2, l2) (f r)
mapGenLNodeRegs f (CallRuntimeLN fn r) = CallRuntimeLN (mapRTRegs f fn) (f r)
mapGenLNodeRegs _ (PanicLN s) = PanicLN s
mapGenLNodeRegs _ (CJumpLN cc l1 l2) = CJumpLN cc l1 l2
mapGenLNodeRegs _ (JumpLN l) = JumpLN l
mapGenLNodeRegs f (ReturnLN g) = ReturnLN (mapGenRator f g)

mapRTRegs :: (r -> s) -> RuntimeFn r -> RuntimeFn s
mapRTRegs _ (AllocStructFn structId) = AllocStructFn structId
mapRTRegs f (ForceFn reg) = ForceFn $ f reg

getLVarsRead :: forall r e x. GenLNode r e x -> [r]
getLVarsRead = fst . getVRW

getLVarsWritten :: forall r e x. GenLNode r e x -> [r]
getLVarsWritten = snd . getVRW

getVRW :: forall r e x. GenLNode r e x -> ([r], [r])
getVRW node =  case node of
  (CopyWordLN g r) -> (ratorToReg [g], [r])
  (LoadWordLN sAddr r) -> (symAddrToReg sAddr, [r])
  (StoreWordLN sAddr g) -> (ratorToReg [g] ++ symAddrToReg sAddr, [])
  (CmpWordLN g r) -> (r:ratorToReg [g], [])
  (BinOpLN _ g1 g2 r) -> (ratorToReg [g1, g2], [r])
  (Phi2LN (g1, _) (g2, _) r) -> (ratorToReg [g1, g2], [r])
  (CallRuntimeLN (ForceFn reg) r) -> ([reg], [r])
  (CallRuntimeLN (AllocStructFn _) r) -> ([], [r])
  (ReturnLN g) -> (ratorToReg [g], [])
  _ -> ([], [])
  where ratorToReg = concatMap (\rator -> case rator of
                                   (VarR reg) -> [reg]
                                   _ -> [])
        symAddrToReg (VarPlusVarSA r1 r2) = [r1, r2]
        symAddrToReg (VarPlusSymSA r _) = [r]
        symAddrToReg _ = []

instance NonLocal (GenLNode r) where
  entryLabel (LabelLN label) = label
  successors PanicLN{} = []
  successors (CJumpLN _ lblA lblB) = [lblA, lblB]
  successors (JumpLN lbl) = [lbl]
  successors (ReturnLN _) = []

data LFunction r = LFunction { lFnName :: ClsrId, lFnArgCount :: Int,
                               lFnEntry :: Label, lFnBody :: Graph (GenLNode r) C C }

type PanicMap = (M.Map String (Label, Graph LNode C C))

hirToLIR :: HFunction -> M (LFunction SSAVar)
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
      return $ mkMiddle $ LoadWordLN (ArgsPtrSA hInp) out

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
          DivOp -> genDivision inA' inB' out
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
      (checkClosureL, forcingNotNeededL) <- twice freshLabel
      (incomingL, checkSaturatedL) <- twice freshLabel
      (forcingNeededL, theEndL) <- twice freshLabel

      (tag, forcedResult, v) <- thrice freshVarName
      (appsLeft, tagCleared) <- twice freshVarName

      let theBeginB = mkLast (JumpLN incomingL)
      let incomingB =
            mkFirst (LabelLN incomingL) <*> mkLast (JumpLN checkClosureL)
      let checkClosureB =
            mkFirst (LabelLN checkClosureL) <*>
            mkMiddles [
              Phi2LN (VarR value, incomingL) (VarR forcedResult, forcingNeededL) v,
              BinOpLN BitAndLOp (VarR v) (LitR ClsrTagC) tag,
              CmpWordLN (LitR ClsrTagC) tag ] <*>
            mkLast (CJumpLN JNE forcingNotNeededL checkSaturatedL)
      let checkSaturatedB =
            mkFirst (LabelLN checkSaturatedL) <*>
            mkMiddles [
              BinOpLN BitAndLOp (LitR ClearTagBitsC) (VarR v) tagCleared,
              LoadWordLN (VarPlusSymSA tagCleared AppsLeftO) appsLeft,
              CmpWordLN (LitR (WordC 0)) appsLeft ] <*>
            mkLast (CJumpLN JNE forcingNotNeededL forcingNeededL)
      let forcingNeededB =
            mkFirst (LabelLN forcingNeededL) <*>
            mkMiddles [
              CallRuntimeLN (ForceFn tagCleared) forcedResult ] <*>
            mkLast (JumpLN checkClosureL)
      let forcingNotNeededB =
            mkFirst (LabelLN forcingNotNeededL) <*>
            mkMiddle (CopyWordLN (VarR v) result) <*>
            mkLast (JumpLN theEndL)
      let theEndB = mkFirst (LabelLN theEndL)

      return $ theBeginB |*><*| incomingB |*><*| checkClosureB |*><*|
        checkSaturatedB |*><*| forcingNeededB |*><*| forcingNotNeededB |*><*|
        theEndB

    nodeMapFn (ForceHN lit result) = do
      (valCode, valConst) <- ratorLitToConstant lit
      return $ valCode <*> mkMiddle (CopyWordLN valConst result)

    nodeMapFn (CopyValueHN value result) = do
      (valCode, valConst) <- ratorLitToConstant value
      return $ valCode <*> mkMiddle (CopyWordLN valConst result)

    nodeMapFn (IfThenElseHN (LitR condition) tLbl fLbl) =
      return $ mkLast $ JumpLN $ if condition then tLbl else fLbl

    nodeMapFn (IfThenElseHN (VarR condition) tLbl fLbl) =
      let cmp = CmpWordLN (LitR BoolTrueC) condition
          jmp = CJumpLN JE tLbl fLbl
      in return $ mkMiddle cmp <*> mkLast jmp

    nodeMapFn (JumpHN lbl) = return $ mkLast $ JumpLN lbl

    nodeMapFn (ReturnHN value) = do
      (valCode, valConst) <- ratorLitToConstant value
      return $ valCode <*> mkLast (ReturnLN valConst)

    genPush :: SSAVar -> Rator Constant -> SSAVar -> IRMonad PanicMap (Graph LNode O O)
    genPush clsrVar value newNode = do
      (validityCheck, appsLeft) <- checkPushValid (VarR clsrVar)
      (appsLeft', freshNode) <- twice freshVarName
      return $ validityCheck <*>
        mkMiddles [
          BinOpLN SubLOp (VarR appsLeft) (LitR (WordC 1)) appsLeft',
          CallRuntimeLN (AllocStructFn ClsrAppNodeST) freshNode,
          StoreWordLN (VarPlusSymSA freshNode AppsLeftO) (VarR appsLeft'),
          StoreWordLN (VarPlusSymSA freshNode NextPtrO) (VarR clsrVar),
          StoreWordLN (VarPlusSymSA freshNode NodeValueO) value,
          BinOpLN BitOrLOp (LitR ClsrNodeTagC) (VarR freshNode) newNode ]

    checkPushValid var = do
      panicLbl <- getPanicLabel "too many pushes"
      (appsLeft, untaggedVar) <- twice freshVarName
      pushOkay <- freshLabel
      return (mkMiddles [
                 BinOpLN BitAndLOp (LitR ClearTagBitsC) var untaggedVar,
                 LoadWordLN (VarPlusSymSA untaggedVar AppsLeftO) appsLeft,
                 CmpWordLN (LitR (WordC 0)) appsLeft ] <*>
              mkLast (CJumpLN JE panicLbl pushOkay) |*><*|
              mkFirst (LabelLN pushOkay), appsLeft)

    genCmp op (LitR inA) (LitR inB) out = do
      tmpB <- freshVarName
      compareOp <- genCmp op (LitR inA) (VarR tmpB) out
      return $
        mkMiddle (CopyWordLN (LitR inB) tmpB) <*> compareOp

    genCmp op (VarR inA) (LitR inB) out =
      genCmp' (CmpWordLN (LitR inB) inA) (opToJC op) (LitR BoolTrueC)
      (LitR BoolFalseC) out

    genCmp op inA (VarR inB) out =
      genCmp' (CmpWordLN inA inB) (opToJC op) (LitR BoolFalseC) (LitR BoolTrueC)
      out

    genCmp' compareOp jmpCond jumpTakenVal jumpNotTakenVal out = do
      (jumpTakenLbl, jumpNotTakenLbl) <- twice freshLabel
      end <- freshLabel
      let jumpTakenBody = mkFirst (LabelLN jumpTakenLbl) <*>
                          mkMiddle (CopyWordLN jumpTakenVal out) <*>
                          mkLast (JumpLN end)
          jumpNotTakenBody = mkFirst (LabelLN jumpNotTakenLbl) <*>
                             mkMiddle (CopyWordLN jumpNotTakenVal out) <*>
                             mkLast (JumpLN end)
      return $ mkMiddle compareOp <*>
        mkLast (CJumpLN jmpCond jumpTakenLbl jumpNotTakenLbl) |*><*|
        jumpTakenBody |*><*| jumpNotTakenBody |*><*|
        mkFirst (LabelLN end)

    opToJC LtOp = JG
    opToJC EqOp = JE
    opToJC op =
      error $ "logic error: opToJC called incorrectly with " ++ show op

    genMultiplication inA inB result = do
      aRShifted <- freshVarName
      return $ mkMiddles [
        BinOpLN RShiftLOp inA (LitR (WordC 2)) aRShifted,
        BinOpLN MultLOp inB (VarR aRShifted) result ]

    genDivision :: Rator Constant -> Rator Constant -> SSAVar ->
                   IRMonad PanicMap (Graph LNode O O)
    genDivision _ (LitR (WordC 0)) _ = do
      divisorIsZero <- getPanicLabel "encountered division by zero"
      neverReached <- freshLabel
      return $ mkLast (JumpLN divisorIsZero) |*><*|
        mkFirst (LabelLN neverReached)

    genDivision inA (LitR inB) result = do
      tmpB <- freshVarName
      divOp <- genDivision inA (VarR tmpB) result
      return $ mkMiddle (CopyWordLN (LitR inB) tmpB) <*> divOp

    genDivision inA (VarR inB) result = do
      divisorIsZero <- getPanicLabel "encountered division by zero"
      divisorIsNotZero <- freshLabel
      resultUnshifted <- freshVarName
      let zeroCheck = mkMiddle (CmpWordLN (LitR (WordC 0)) inB) <*>
                      mkLast (CJumpLN JE divisorIsZero divisorIsNotZero)
      return $ zeroCheck |*><*|
        mkFirst (LabelLN divisorIsNotZero) <*>
        mkMiddles [ BinOpLN DivLOp inA (VarR inB) resultUnshifted,
                    BinOpLN RShiftLOp (VarR resultUnshifted) (LitR (WordC 2))
                    result ]

    genAddSubOp op inA inB result =
      return $ mkMiddle $ BinOpLN (hOpToLOp op) inA inB result

    genCreateClosure :: ClsrId -> SSAVar -> IRMonad PanicMap (Graph LNode O O)
    genCreateClosure clsrId result = do
      untaggedClsr <- freshVarName
      return $ mkMiddles [
        CallRuntimeLN (AllocStructFn (ClsrST clsrId)) untaggedClsr,
        StoreWordLN (VarPlusSymSA untaggedClsr AppsLeftO) (LitR (ClsrAppLimitC clsrId)),
        StoreWordLN (VarPlusSymSA untaggedClsr CodePtrO) (LitR (ClsrCodePtrC clsrId)),
        BinOpLN BitOrLOp (LitR ClsrBaseTagC) (VarR untaggedClsr) result ]

    genAssertTag :: Rator Lit -> Constant -> IRMonad PanicMap (Graph LNode O O)
    genAssertTag (VarR var) tag =
      -- ClsrTagC is a pseudo-tag that allows us to check for two
      -- things in one go.
      let mask = if tag == ClsrTagC then 1 else 3
      in do
        extractedTag <- freshVarName
        -- TODO: make the panic message more
        let tagToType ClsrTagC = "closure"
            tagToType ClsrBaseTagC = "closure base node"
            tagToType ClsrNodeTagC = "closure app node"
            tagToType IntTagC = "integer"
            tagToType BoolTagC = "boolean"
            tagToType t = error $ "tag " ++ show t ++ " unexpected"
        panicLbl <- getPanicLabel $ "invalid type, expected `" ++
                    tagToType tag ++ "`"
        checkPassed <- freshLabel
        return $ mkMiddles [
          BinOpLN BitAndLOp (VarR var) (LitR (WordC mask)) extractedTag,
          CmpWordLN (LitR tag) extractedTag ] <*>
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
    ratorIntToConstant (LitR w) = LitR (WordC (w `B.shift` 2))

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

    twice :: IRMonad PanicMap a -> IRMonad PanicMap (a, a)
    twice m = sequence [m, m] >>= (\[x, y] -> return (x, y))

    thrice :: IRMonad PanicMap a -> IRMonad PanicMap (a, a, a)
    thrice m = sequence [m, m, m] >>= (\[x, y, z] -> return (x, y, z))

lirDebugShowGraph :: M [LFunction SSAVar] -> String
lirDebugShowGraph fn =
  let functionList = runSimpleUniqueMonad $ runWithFuel maxBound fn
  in unlines $ map showLFunction functionList
  where
    showLFunction :: LFunction SSAVar -> String
    showLFunction (LFunction name argC entry body) =
      let functionGraph = showGraph ((++ " ") . show) body
      in unlines ["ClsrId = " ++ show name, "ArgCount = " ++ show argC,
                  "EntryLabel = " ++ show entry, "Body = {",
                  functionGraph ++ "}"]
