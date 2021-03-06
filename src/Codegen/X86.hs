{-# OPTIONS_GHC -Wall -Werror -i.. #-}
{-# LANGUAGE GADTs, StandaloneDeriving, FlexibleInstances #-}

module Codegen.X86(Reg, regStackPtr, regBasePtr, regArgPtr, generalRegSet,
                   MachineInst, lirNodeToMachineInst, machinePrologue,
                   wordSize, asmHeader, peepholeOpt)
       where

import qualified Compiler.Hoopl as Hoopl
import qualified Data.Bits as B
import qualified Data.Set as S

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

regArgPtr :: Reg
regArgPtr = Reg_RDI

vmGlobalsReg :: Reg
vmGlobalsReg = Reg_R15

vmGCLoc :: Int
vmGCLoc = 8

vmGCLim :: Int
vmGCLim = 16

asmHeader :: String
asmHeader = unlines [
  "\t.globl\tclosure_body_0",
  "#ifndef __clang__",
  "\t.type\tclosure_body_0,\t@function",
  "#endif",
  ""]

wordSize :: Int
wordSize = 8

generalRegSet :: S.Set Reg
generalRegSet = S.fromList [
  Reg_RAX, Reg_RBX, Reg_RCX, Reg_RDX, Reg_RSI, Reg_RDI, Reg_R8, Reg_R9, Reg_R10,
  Reg_R11, Reg_R12, Reg_R13, Reg_R14 ]

getLiveCallerSavedRegs :: RegInfo Reg -> [Reg]
getLiveCallerSavedRegs rI = riNonFreeRegsIn rI calleeSavedRegs

lowerConstant :: (ClsrId -> Int) -> Constant -> (Op, Bool)
lowerConstant _ (ClsrCodePtrC clsrId) =
  (SymWordOp $ DirectString $ "$closure_body_" ++ show clsrId, True)
lowerConstant appLimits op =
  (LitWordOp $ DollarString $ constToString appLimits op, False)

constToString :: (ClsrId -> Int) -> Constant -> String
constToString _ (WordC w) = show w
constToString appLimits (ClsrAppLimitC clsrId) = show (appLimits clsrId)
constToString _ (ClsrCodePtrC _) = error "not handled here "
constToString _ ClsrTagC = "1"
constToString _ ClsrBaseTagC = "3"
constToString _ ClsrNodeTagC = "1"
constToString _ IntTagC = "0"
constToString _ BoolTagC = "2"
constToString _ BoolFalseC = "2"
constToString _ BoolTrueC = "6"
constToString _ ClearTagBitsC = show (B.complement 3 :: Int)

lowerOffset :: Offset -> Int
lowerOffset AppsLeftO = 8
lowerOffset NextPtrO = 0
lowerOffset NodeValueO = 16
lowerOffset CodePtrO = 0

lowerSymAddress :: SymAddress Reg -> Op
-- TODO: this is somewhat inconsistent, move all wordSize logic here.
lowerSymAddress (ArgsPtrSA offset) = MemOp2 regArgPtr (wordSize * offset)
lowerSymAddress (StackOffsetSA offset) = MemOp2 regBasePtr (- offset)
lowerSymAddress (VarPlusSymSA reg offset) = MemOp2 reg (lowerOffset offset)
lowerSymAddress (VarPlusVarSA reg1 reg2) = MemOp3 reg1 reg2

structSize :: StructId -> String
structSize (ClsrST _) = "16"
structSize ClsrAppNodeST = "24"

data Op = MemOp1 Reg | MemOp2 Reg Int | MemOp3 Reg Reg | LitWordOp DollarString
        | SymWordOp DirectString deriving(Eq, Ord)

data C = E | G | L | NE deriving(Eq, Ord)

newtype DollarString = DollarString String deriving(Eq, Ord)
instance Show DollarString where show (DollarString s) = '$':s

newtype DirectString = DirectString String deriving(Eq, Ord)
instance Show DirectString where show (DirectString s) = s

data MachineInst =
  LabelMI String | CommentMI String | StringMI String
  | MovMI_RR Reg Reg | MovMI_OR Op Reg | MovMI_RO Reg Op
  | MovAbsMI_OR Op Reg | MovAbsMI_RO Reg Op
  | MovMI_IO DollarString Op | MovMI_IR DollarString Reg
  | CmpMI_RR Reg Reg | CmpMI_OR Op Reg
  | AddMI_RR Reg Reg | AddMI_OR Op Reg | SubMI_RR Reg Reg | SubMI_OR Op Reg
  | IMulMI_RR Reg Reg | IMulMI_OR Op Reg | DivMI_R Reg      | DivMI_O Op
  | AndMI_RR Reg Reg | AndMI_OR Op Reg | OrMI_RR  Reg Reg | OrMI_OR  Op Reg
  | XorMI_RR Reg Reg | XorMI_OR Op Reg | LShMI_RR Reg Reg | LShMI_OR Op Reg
  | RShMI_RR Reg Reg | RShMI_OR Op Reg
  | CJumpMI C String | JumpMI String
  | CallMI_I DirectString | CallMI_R Reg | RetMI
  | PushMI_I Reg | PushMI_R Reg | PopMI_R Reg
  | Unimplemented String
  deriving(Eq, Ord)

deriving instance Show(GenLNode Reg e x)

lirNodeToMachineInst :: EchoesOptions -> (ClsrId -> Int) -> RegInfo Reg ->
                        GenLNode Reg e x -> M [MachineInst]
lirNodeToMachineInst opts clsrMap reg node = do
  code <- lirNodeToMachineInst' clsrMap reg node
  return $ if annotateAssembly opts then (CommentMI $ show node):code else code

lirNodeToMachineInst' :: (ClsrId -> Int) -> RegInfo Reg -> GenLNode Reg e x ->
                         M [MachineInst]

lirNodeToMachineInst' _ _ (LabelLN lbl) = return [LabelMI $ show lbl]

lirNodeToMachineInst' aL _ (CopyWordLN (LitR cValue) reg) =
    let (loweredOp, needsAbs) = lowerConstant aL cValue
    in return [ (if needsAbs then MovAbsMI_OR else MovMI_OR) loweredOp reg]

lirNodeToMachineInst' _ _ (CopyWordLN (VarR srcR) destR) =
  return [MovMI_RR srcR destR]

lirNodeToMachineInst' _ _ (LoadWordLN symAddr reg) = return [
  MovMI_OR (lowerSymAddress symAddr) reg]

lirNodeToMachineInst' _ _ (StoreWordLN symAddr (VarR reg)) = return [
  MovMI_RO reg (lowerSymAddress symAddr)]

lirNodeToMachineInst' aL _ (StoreWordLN symAddr (LitR cValue)) =
    let (loweredOp, needsAbs) = lowerConstant aL cValue
        opOR = if needsAbs then MovAbsMI_OR else MovMI_OR
    in return [ opOR loweredOp Reg_R11,
                MovMI_RO Reg_R11 (lowerSymAddress symAddr) ]

lirNodeToMachineInst' aL _ (CmpWordLN (LitR c) v) = return [
  CmpMI_OR (fst $ lowerConstant aL c) v]

lirNodeToMachineInst' _ _ (CmpWordLN (VarR vA) vB) = return [
  CmpMI_RR vA vB]

lirNodeToMachineInst' _ _ (BinOpLN DivLOp _ _ _) = return [
  Unimplemented "i not know to divide!"]

lirNodeToMachineInst' aL gcRegs (BinOpLN op a b r) = do
  copyCode <- lirNodeToMachineInst' aL gcRegs (CopyWordLN a r)
  return $ copyCode ++ [
    case b of (VarR reg) -> injFor_RR op reg r
              (LitR c) -> injFor_OR op (fst $ lowerConstant aL c) r]
  where injFor_RR BitAndLOp = AndMI_RR
        injFor_RR BitOrLOp = OrMI_RR
        injFor_RR BitXorLOp = XorMI_RR
        injFor_RR AddLOp = AddMI_RR
        injFor_RR SubLOp = SubMI_RR
        injFor_RR MultLOp = IMulMI_RR
        injFor_RR DivLOp = error "logic error in lirNodeToMachineInst"
        injFor_RR LShiftLOp = LShMI_RR
        injFor_RR RShiftLOp = RShMI_RR

        injFor_OR BitAndLOp = AndMI_OR
        injFor_OR BitOrLOp = OrMI_OR
        injFor_OR BitXorLOp = XorMI_OR
        injFor_OR AddLOp = AddMI_OR
        injFor_OR SubLOp = SubMI_OR
        injFor_OR MultLOp = IMulMI_OR
        injFor_OR DivLOp = error "logic error in lirNodeToMachineInst"
        injFor_OR LShiftLOp = LShMI_OR
        injFor_OR RShiftLOp = RShMI_OR

lirNodeToMachineInst' _ _ Phi2LN{} =
  error "logic error: phi nodes should have been removed by now!"

lirNodeToMachineInst' _ rI (CallRuntimeLN (AllocStructFn structId) result) =
  let (regA:_) = filter (/= result) $ riFreeRegs rI in do
    notEnoughSpace <- Hoopl.freshLabel
    allocationDone <- Hoopl.freshLabel
    return $
      checkGCLimit regA notEnoughSpace ++ fastPath regA allocationDone ++
      slowPath notEnoughSpace ++ [ LabelMI (show allocationDone) ]
    where
      checkGCLimit regA notEnoughSpace = [
        MovMI_OR (MemOp2 vmGlobalsReg vmGCLoc) regA,
        AddMI_OR (LitWordOp $ DollarString $ (structSize structId)) regA,
        CmpMI_OR (MemOp2 vmGlobalsReg vmGCLim) regA,
        CJumpMI G (show notEnoughSpace) ]

      fastPath regA allocationDone = [
        MovMI_OR (MemOp2 vmGlobalsReg vmGCLoc) result,
        MovMI_RO regA (MemOp2 vmGlobalsReg vmGCLoc),
        JumpMI (show allocationDone) ]

      slowPath notEnoughSpace =
        let functionName (ClsrST _) = "_call_rt_alloc_base_node"
            functionName ClsrAppNodeST = "_call_rt_alloc_app_node"
        in [ LabelMI (show notEnoughSpace) ] ++ pushLiveRegs ++
           [ CallMI_I $ DirectString $ functionName structId] ++
           popLiveRegs ++ [ MovMI_RR Reg_RAX result ]

      pushLiveRegs = map PushMI_R liveRegs
      popLiveRegs = reverse $ map PopMI_R liveRegs

      liveRegs = getLiveCallerSavedRegs rI

lirNodeToMachineInst' _ rI (CallRuntimeLN (ForceFn value) result) =
  return $ map PushMI_R liveRegs ++ callRT ++ reverse (map PopMI_R liveRegs)
  where
    liveRegs = getLiveCallerSavedRegs rI

    callRT = [
      MovMI_RR value regArgPtr,
      CallMI_I $ DirectString "_runtime_force",
      MovMI_RR Reg_RAX result ]

lirNodeToMachineInst' _ _ (PanicLN panicString) = do
  stringLabel <- Hoopl.freshLabel
  return [
    MovAbsMI_OR (LitWordOp $ DollarString $ show stringLabel) Reg_RDI,
    CallMI_I $ DirectString "_runtime_panic",
    LabelMI $ show stringLabel,
    StringMI panicString
    ]

lirNodeToMachineInst' _ _ (CJumpLN c tL fL) = return [
  CJumpMI (jCondToC c) (show tL),
  JumpMI (show fL) ]

lirNodeToMachineInst' _ _ (JumpLN lbl) = return [
  JumpMI (show lbl) ]

lirNodeToMachineInst' aL rI (ReturnLN result) =
  lirNodeToMachineInst' aL rI (CopyWordLN result Reg_RAX) `mApp`
  return (
    MovMI_RR regBasePtr regStackPtr:
    (map PopMI_R (reverse calleeSavedRegs) ++ [ RetMI ]))

calleeSavedRegs :: [Reg]
calleeSavedRegs = [ Reg_RBP, Reg_RBX, Reg_R12, Reg_R13, Reg_R14, Reg_R15 ]

machinePrologue  :: Int -> [MachineInst]
machinePrologue stackSize = map PushMI_R calleeSavedRegs ++ [
  MovMI_RR regStackPtr regBasePtr,
  let roundedUpStackSize = ((stackSize + 15) `div` 16) * 16
  in SubMI_OR (LitWordOp $ DollarString $ show roundedUpStackSize) regStackPtr ]

peepholeOpt :: [MachineInst] -> [MachineInst]
peepholeOpt (MovMI_RR a b:rest)
  | a == b = peepholeOpt rest
  | otherwise = MovMI_RR a b:peepholeOpt rest
peepholeOpt (i:is) = i:peepholeOpt is
peepholeOpt [] = []

jCondToC :: JCondition -> C
jCondToC JE = E
jCondToC JG = G
jCondToC JL = L
jCondToC JNE = NE

instance Show Reg where
  show Reg_RAX = "%rax"
  show Reg_RBX = "%rbx"
  show Reg_RCX = "%rcx"
  show Reg_RDX = "%rdx"
  show Reg_RSI = "%rsi"
  show Reg_RDI = "%rdi"
  show Reg_RBP = "%rbp"
  show Reg_RSP = "%rsp"
  show Reg_R8  = "%r8"
  show Reg_R9  = "%r9"
  show Reg_R10 = "%r10"
  show Reg_R11 = "%r11"
  show Reg_R12 = "%r12"
  show Reg_R13 = "%r13"
  show Reg_R14 = "%r14"
  show Reg_R15 = "%r15"

instance Show Op where
  show (MemOp1 reg) = "(" ++ show reg ++ ")"
  show (MemOp2 reg offset) = show offset ++ "(" ++ show reg ++ ")"
  show (MemOp3 reg1 reg2) = show reg1 ++ "(" ++ show reg2 ++ ")"
  show (LitWordOp lit) = show lit
  show (SymWordOp sym) = show sym

instance Show C where
  show E = "e"
  show G = "g"
  show L = "l"
  show NE = "ne"

showMInst :: MachineInst -> String
showMInst mInst = case mInst of
  LabelMI lbl -> lbl ++ ":"
  StringMI str -> ".string " ++ escapeString str
  CommentMI str -> "/** " ++ str ++ " **/"

  MovMI_RR r1 r2 -> movq r1 r2
  MovMI_OR op r -> movq op r
  MovMI_RO r op -> movq r op
  MovMI_IO i op -> movq i op
  MovMI_IR i r  -> movq i r
  MovAbsMI_RO i r  -> movabs i r
  MovAbsMI_OR i r  -> movabs i r

  CmpMI_RR r1 r2 -> cmpq r1 r2
  CmpMI_OR op r -> cmpq op r

  AddMI_RR  r1 r2  -> addq r1 r2
  SubMI_RR  r1 r2  -> subq r1 r2
  IMulMI_RR r1  r2 -> imulq r1 r2
  AndMI_RR  r1 r2  -> andq r1 r2
  OrMI_RR   r1 r2  -> orq  r1 r2
  XorMI_RR  r1 r2  -> xorq r1 r2
  LShMI_RR  r1 r2  -> shlq r1 r2
  RShMI_RR  r1 r2  -> shrq r1 r2
  DivMI_R   r      -> divq r

  AddMI_OR  op r  -> addq op r
  SubMI_OR  op r  -> subq op r
  IMulMI_OR op r  -> imulq op r
  AndMI_OR  op r  -> andq op r
  OrMI_OR   op r  -> orq  op r
  XorMI_OR  op r  -> xorq op r
  LShMI_OR  op r  -> shlq op r
  RShMI_OR  op r  -> shrq op r
  DivMI_O   op    -> divq op

  CallMI_R r      -> "callq *" ++ show r
  CallMI_I i      -> call i

  PushMI_R r      -> pushq r
  PushMI_I i      -> pushq i
  PopMI_R  r      -> popq  r

  CJumpMI c lbl   -> j c lbl
  JumpMI lbl      -> jmp lbl

  RetMI           -> retq

  Unimplemented s -> "unimplemented: " ++ s
  where
    movq src dest = "movq " ++ show src ++ ", " ++ show dest
    movabs src dest = "movabsq " ++ show src ++ ", " ++ show dest
    cmpq a b = "cmpq " ++ show a ++ ", " ++ show b
    addq a b  = "addq " ++ show a ++ ", " ++ show b
    subq a b  = "subq " ++ show a ++ ", " ++ show b
    imulq a b = "imulq " ++ show a ++ ", " ++ show b
    andq a b = "andq " ++ show a ++ ", " ++ show b
    orq  a b = "orq " ++ show a ++ ", " ++ show b
    xorq a b = "xorq " ++ show a ++ ", " ++ show b
    shlq a b = "shlq " ++ show a ++ ", " ++ show b
    shrq a b = "shrq " ++ show a ++ ", " ++ show b
    divq a   = "divq " ++ show a
    call a   = "callq " ++ show a
    retq     = "retq "
    pushq a  = "pushq " ++ show a
    popq a   = "popq " ++ show a
    j c lbl  = "j" ++ show c ++ " " ++ lbl
    jmp lbl = "jmp " ++ lbl
    -- TODO: escape quotes etc.
    escapeString s = "\"" ++ s ++ "\""

instance Show MachineInst where
  show lbl@(LabelMI _) = showMInst lbl
  show other = '\t':showMInst other
