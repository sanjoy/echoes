{-# OPTIONS_GHC -Wall -Werror -i.. #-}
{-# LANGUAGE GADTs, StandaloneDeriving, FlexibleInstances #-}

module Codegen.X86(Reg, regStackPtr, regBasePtr, generalRegSet,
                   MachineInst, lirNodeToMachineInst, machinePrologue)
       where

import qualified Compiler.Hoopl as Hoopl
import qualified Data.Bits as B
import qualified Data.Set as S
import qualified Numeric as N

import Codegen.Common
import LIR.LIR
import Utils.Common

data Reg = Reg_RAX | Reg_RBX | Reg_RCX | Reg_RDX | Reg_RSI | Reg_RDI
         | Reg_RBP | Reg_RSP
         | Reg_R8 | Reg_R9 | Reg_R10 | Reg_R11 | Reg_R12 | Reg_R13
         | Reg_R14 | Reg_R15
         deriving(Eq, Ord, Enum)

regStackPtr :: Reg
regStackPtr = Reg_RSP

regBasePtr :: Reg
regBasePtr = Reg_RBP

vmGlobalsReg :: Reg
vmGlobalsReg = Reg_R15

vmGCLoc :: Int
vmGCLoc = 8

vmGCLim :: Int
vmGCLim = 16

generalRegSet :: S.Set Reg
generalRegSet = S.fromList [
  Reg_RAX, Reg_RBX, Reg_RCX, Reg_RDX, Reg_RSI, Reg_RDI, Reg_R8, Reg_R9, Reg_R10,
  Reg_R11, Reg_R12, Reg_R13, Reg_R14 ]

getLiveCallerSavedRegs :: RegInfo Reg -> [Reg]
getLiveCallerSavedRegs rI = riNonFreeRegsIn rI calleeSavedList
  where calleeSavedList =
          [ Reg_RAX, Reg_RCX, Reg_RDX, Reg_RSI, Reg_RSI, Reg_RDI,
            Reg_R8, Reg_R9, Reg_R10, Reg_R11 ]

lowerConstant :: (ClsrId -> Int) -> Constant -> Op
lowerConstant appLimits = LitWordOp . constToString appLimits

constToString :: (ClsrId -> Int) -> Constant -> String
constToString _ (WordC w) = show w
constToString appLimits (ClsrAppLimitC clsrId) =
  N.showHex (appLimits clsrId) ""
constToString _ (ClsrCodePtrC clsrId) = "closure_body_" ++ show clsrId
constToString _ ClsrTagC = "0x1"
constToString _ ClsrBaseTagC = "0x1"
constToString _ ClsrNodeTagC = "0x3"
constToString _ IntTagC = "0x0"
constToString _ BoolTagC = "0x2"
constToString _ BoolFalseC = "0x2"
constToString _ BoolTrueC = "0x6"
constToString _ ClearTagBitsC = N.showHex (B.complement 3 :: Int) ""

lowerOffset :: Offset -> String
lowerOffset AppsLeftO = "0x8"
lowerOffset NextPtrO = "0x0"
lowerOffset NodeValueO = "0x10"
lowerOffset CodePtrO = "0x0"

lowerSymAddress :: SymAddress Reg -> Op
lowerSymAddress (ArgsPtrLSA offset) = LitWordOp $ show offset ++ "(rsi)"
lowerSymAddress (StackOffset offset) = LitWordOp $ show offset ++ "(rbp)"
lowerSymAddress (VarPlusSymL r offset) =
  LitWordOp $ lowerOffset  offset ++ "(" ++ show r ++ ")"
lowerSymAddress (VarPlusVarL r1 r2) =
  LitWordOp $ show r2 ++ "(" ++ show r1 ++ ")"

structSize :: StructId -> String
structSize (ClsrST _) = "0x10"
structSize ClsrAppNodeST = "0x16"

data Op = MemOp1 Reg | MemOp2 Reg Int | LitWordOp String
        deriving(Eq, Ord)

data C = E | G | L | NE deriving(Eq, Ord)

newtype Str = Str String deriving(Eq, Ord)
instance Show Str where show (Str s) = s

data MachineInst =
  LabelMI String
  | MovMI_RR Reg Reg | MovMI_OR Op Reg | MovMI_RO Reg Op | MovMI_IO Str Op
  | CmpMI_RR Reg Reg | CmpMI_OR Op Reg | CmpMI_RO Reg Op
  | CMovMI_RR C Reg Reg | CMovMI_OR C Op Reg | CMovMI_RO C Reg Op
  | CMovMI_IO C Int Op
  | AddMI_RR Reg Reg | AddMI_OR Op Reg | SubMI_RR Reg Reg | SubMI_OR Op Reg
  | MulMI_RR Reg Reg | MulMI_OR Op Reg | DivMI_R Reg      | DivMI_O Op
  | AndMI_RR Reg Reg | AndMI_OR Op Reg | OrMI_RR  Reg Reg | OrMI_OR  Op Reg
  | XorMI_RR Reg Reg | XorMI_OR Op Reg | LShMI_RR Reg Reg | LShMI_OR Op Reg
  | RShMI_RR Reg Reg | RShMI_OR Op Reg
  | CJumpMI C String | JumpMI String
  | CallMI_I Str | CallMI_R Reg | RetMI
  | PushMI_I Reg | PushMI_R Reg | PopMI_R Reg
  | Unimplemented String
  deriving(Eq, Ord)

deriving instance Show(GenLNode Reg e x)

lirNodeToMachineInst :: (ClsrId -> Int) -> RegInfo Reg -> GenLNode Reg e x ->
                        M [MachineInst]

lirNodeToMachineInst _ _ (LabelLN lbl) = return [LabelMI $ show lbl]

lirNodeToMachineInst aL _ (CopyWordLN (LitR cValue) reg) = return [
  MovMI_OR (lowerConstant aL cValue) reg]

lirNodeToMachineInst _ _ (CopyWordLN (VarR srcR) destR) =
  return [MovMI_RR srcR destR]

lirNodeToMachineInst _ _ (LoadWordLN symAddr reg) = return [
  MovMI_OR (lowerSymAddress symAddr) reg]

lirNodeToMachineInst _ _ (StoreWordLN symAddr (VarR reg)) = return [
  MovMI_RO reg (lowerSymAddress symAddr)]

lirNodeToMachineInst aL _ (StoreWordLN symAddr (LitR cValue)) = return [
  MovMI_IO (Str $ constToString aL cValue) (lowerSymAddress symAddr)]

lirNodeToMachineInst _ _ (CmpWordLN (LitR _) (LitR _)) =
  error "unfolded constant!"

lirNodeToMachineInst aL _ (CmpWordLN (LitR c) (VarR v)) = return [
  CmpMI_OR (lowerConstant aL c) v]

lirNodeToMachineInst aL _ (CmpWordLN (VarR v) (LitR c)) = return [
  CmpMI_RO v (lowerConstant aL c)]

lirNodeToMachineInst _ _ (CmpWordLN (VarR vA) (VarR vB)) = return [
  CmpMI_RR vA vB]

lirNodeToMachineInst _ _ (CondMoveLN cc (VarR r1) r2) = return [
  CMovMI_RR (jCondToC cc) r1 r2]

lirNodeToMachineInst aL _ (CondMoveLN cc (LitR c) r) = return [
  CMovMI_OR (jCondToC cc) (lowerConstant aL c) r]

lirNodeToMachineInst _ _ (BinOpLN DivLOp _ _ _) = return [
  Unimplemented "i not know to divide!"]

lirNodeToMachineInst aL gcRegs (BinOpLN op a b r) = do
  copyCode <- lirNodeToMachineInst aL gcRegs (CopyWordLN a r)
  return $ copyCode ++ [
    case b of (VarR reg) -> injFor_RR op reg r
              (LitR c) -> injFor_OR op (lowerConstant aL c) r]
  where injFor_RR BitAndLOp = AndMI_RR
        injFor_RR BitOrLOp = OrMI_RR
        injFor_RR BitXorLOp = XorMI_RR
        injFor_RR AddLOp = AddMI_RR
        injFor_RR SubLOp = SubMI_RR
        injFor_RR MultLOp = MulMI_RR
        injFor_RR DivLOp = error "logic error in lirNodeToMachineInst"
        injFor_RR LShiftLOp = LShMI_RR
        injFor_RR RShiftLOp = RShMI_RR

        injFor_OR BitAndLOp = AndMI_OR
        injFor_OR BitOrLOp = OrMI_OR
        injFor_OR BitXorLOp = XorMI_OR
        injFor_OR AddLOp = AddMI_OR
        injFor_OR SubLOp = SubMI_OR
        injFor_OR MultLOp = MulMI_OR
        injFor_OR DivLOp = error "logic error in lirNodeToMachineInst"
        injFor_OR LShiftLOp = LShMI_OR
        injFor_OR RShiftLOp = RShMI_OR

lirNodeToMachineInst _ _ Phi2LN{} = return [
  -- TODO: change this to an 'error' once we have a proper compilation
  -- pipeline
  Unimplemented "phi nodes should have been removed by now" ]

lirNodeToMachineInst _ rI (CallRuntimeLN (AllocStructFn structId) result) =
  let (regA:_) = filter (/= result) $ riFreeRegs rI in do
    notEnoughSpace <- Hoopl.freshLabel
    allocationDone <- Hoopl.freshLabel
    return $
      checkGCLimit regA notEnoughSpace ++ fastPath regA allocationDone ++
      slowPath notEnoughSpace ++ [ LabelMI (show allocationDone) ]
    where
      checkGCLimit regA notEnoughSpace = [
        MovMI_OR (MemOp2 vmGlobalsReg vmGCLoc) regA,
        AddMI_OR (LitWordOp (structSize structId)) regA,
        CmpMI_OR (MemOp2 vmGlobalsReg vmGCLim) regA,
        CJumpMI L (show notEnoughSpace) ]

      fastPath regA allocationDone = [
        MovMI_OR (MemOp2 vmGlobalsReg vmGCLoc) result,
        MovMI_RO regA (MemOp2 vmGlobalsReg vmGCLoc),
        JumpMI (show allocationDone) ]

      slowPath notEnoughSpace =
        [ LabelMI (show notEnoughSpace) ] ++ pushLiveRegs ++
        [ CallMI_I (Str $ "runtime_allocate_" ++
                    case structId of (ClsrST _) -> "closure"
                                     ClsrAppNodeST -> "app_node") ] ++
        popLiveRegs ++ [ MovMI_RR Reg_RAX result ]

      pushLiveRegs = map PushMI_R liveRegs
      popLiveRegs = reverse $ map PopMI_R liveRegs

      liveRegs = getLiveCallerSavedRegs rI

lirNodeToMachineInst _ rI (CallRuntimeLN (ForceFn value) result) =
  return $ map PushMI_R liveRegs ++ callRT ++ reverse (map PopMI_R liveRegs)
  where
    liveRegs = getLiveCallerSavedRegs rI

    callRT = [
      MovMI_RR value Reg_RSI,
      CallMI_I $ Str "runtime_force",
      MovMI_RR Reg_RAX result ]

lirNodeToMachineInst _ _ (PanicLN _) = return [
  JumpMI "runtime_panic" ]

lirNodeToMachineInst _ _ (CJumpLN c tL fL) = return [
  CJumpMI (jCondToC c) (show tL),
  JumpMI (show fL) ]

lirNodeToMachineInst _ _ (JumpLN lbl) = return [
  JumpMI (show lbl) ]

lirNodeToMachineInst aL rI (ReturnLN result) =
  lirNodeToMachineInst aL rI (CopyWordLN result Reg_RAX) `mApp`
  return [ MovMI_RR regBasePtr regStackPtr,
           PopMI_R regBasePtr,
           RetMI ]

machinePrologue  :: Int -> [MachineInst]
machinePrologue stackSize = [
  PushMI_R regBasePtr,
  MovMI_RR regStackPtr regBasePtr,
  SubMI_OR (LitWordOp $ N.showHex stackSize "") regStackPtr ]

jCondToC :: JCondition -> C
jCondToC JE = E
jCondToC JG = G
jCondToC JL = L
jCondToC JNE = NE

instance Show Reg where
  show Reg_RAX = "rax"
  show Reg_RBX = "rbx"
  show Reg_RCX = "rcx"
  show Reg_RDX = "rdx"
  show Reg_RSI = "rsi"
  show Reg_RDI = "rdi"
  show Reg_RBP = "rbp"
  show Reg_RSP = "rsp"
  show Reg_R8  = "r8"
  show Reg_R9  = "r9"
  show Reg_R10 = "r10"
  show Reg_R11 = "r11"
  show Reg_R12 = "r12"
  show Reg_R13 = "r13"
  show Reg_R14 = "r14"
  show Reg_R15 = "r15"

instance Show Op where
  show (MemOp1 reg) = "(" ++ show reg ++ ")"
  show (MemOp2 reg offset) = show offset ++ "(" ++ show reg ++ ")"
  show (LitWordOp lit) = '$':lit

instance Show C where
  show E = "e"
  show G = "g"
  show L = "l"
  show NE = "ne"

showMInst :: MachineInst -> String
showMInst mInst = case mInst of
  LabelMI lbl -> lbl ++ ":"

  MovMI_RR r1 r2 -> movq r1 r2
  MovMI_OR op r -> movq op r
  MovMI_RO r op -> movq r op
  MovMI_IO i op -> movq i op

  CmpMI_RR r1 r2 -> cmpq r1 r2
  CmpMI_OR op r -> cmpq op r
  CmpMI_RO r op -> cmpq r op

  CMovMI_RR c r1 r2 -> cmov c r1 r2
  CMovMI_OR c op r -> cmov c op r
  CMovMI_RO c r op -> cmov c r op
  CMovMI_IO c i op -> cmov c i op

  AddMI_RR r1  r2 -> addq r1 r2
  SubMI_RR r1  r2 -> subq r1 r2
  MulMI_RR r1  r2 -> mulq r1 r2
  AndMI_RR r1  r2 -> andq r1 r2
  OrMI_RR  r1  r2 -> orq  r1 r2
  XorMI_RR r1  r2 -> xorq r1 r2
  LShMI_RR r1  r2 -> shlq r1 r2
  RShMI_RR r1  r2 -> shrq r1 r2
  DivMI_R  r      -> divq r

  AddMI_OR op  r  -> addq op r
  SubMI_OR op  r  -> subq op r
  MulMI_OR op  r  -> mulq op r
  AndMI_OR op  r  -> andq op r
  OrMI_OR  op  r  -> orq  op r
  XorMI_OR op  r  -> xorq op r
  LShMI_OR op  r  -> shlq op r
  RShMI_OR op  r  -> shrq op r
  DivMI_O  op     -> divq op

  CallMI_R r      -> callq r
  CallMI_I i      -> callq i

  PushMI_R r      -> pushq r
  PushMI_I i      -> pushq i
  PopMI_R  r      -> popq  r

  CJumpMI c lbl   -> j c lbl
  JumpMI lbl      -> jmp lbl

  RetMI           -> retq

  Unimplemented s -> "unimplemented: " ++ s
  where
    movq src dest = "movq " ++ show src ++ ", " ++ show dest
    cmpq a b = "cmpq " ++ show a ++ ", " ++ show b
    cmov c src dest = "cmov" ++ show c ++ " " ++ show src ++ ", " ++ show dest
    addq a b = "addq " ++ show a ++ ", " ++ show b
    subq a b = "subq " ++ show a ++ ", " ++ show b
    mulq a b = "mulq " ++ show a ++ ", " ++ show b
    andq a b = "andq " ++ show a ++ ", " ++ show b
    orq  a b = "orq " ++ show a ++ ", " ++ show b
    xorq a b = "xorq " ++ show a ++ ", " ++ show b
    shlq a b = "shlq " ++ show a ++ ", " ++ show b
    shrq a b = "shrq " ++ show a ++ ", " ++ show b
    divq a   = "divq " ++ show a
    callq a  = "callq " ++ show a
    retq     = "retq "
    pushq a  = "pushq " ++ show a
    popq a   = "popq " ++ show a
    j c lbl  = "j" ++ show c ++ " " ++ lbl
    jmp lbl = "jmp " ++ lbl

instance Show MachineInst where
  show lbl@(LabelMI _) = showMInst lbl
  show other = '\t':showMInst other
