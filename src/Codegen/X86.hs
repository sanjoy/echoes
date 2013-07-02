{-# OPTIONS_GHC -Wall -Werror -i.. #-}
{-# LANGUAGE GADTs, StandaloneDeriving, FlexibleInstances #-}

module Codegen.X86(Reg, regStackPtr, regBasePtr, generalRegSet,
                   MachineInst, lirNodeToMachineInst,
                   machinePrologue, machineEpilogue) where

import qualified Data.Bits as B
import qualified Data.Set as S
import qualified Numeric as N

import LIR.LIR
import Utils.Common

data Reg = Reg_RAX | Reg_RBX | Reg_RCX | Reg_RDX | Reg_RSI | Reg_RDI
         | Reg_RBP | Reg_RSP
         | Reg_R8 | Reg_R9 | Reg_R10 | Reg_R11 | Reg_R12 | Reg_R13
         | Reg_R14 | Reg_R15
         deriving(Eq, Ord)

regStackPtr :: Reg
regStackPtr = Reg_RSP

regBasePtr :: Reg
regBasePtr = Reg_RBP

generalRegSet :: S.Set Reg
generalRegSet = S.fromList [
  Reg_RAX, Reg_RBX, Reg_RCX, Reg_RDX, Reg_RSI, Reg_RDI, Reg_R8, Reg_R9, Reg_R10,
  Reg_R11, Reg_R12, Reg_R13, Reg_R14, Reg_R15 ]

lowerConstant :: Constant -> Op
lowerConstant = LitWordOp . constToString

constToString :: Constant -> String
constToString (WordC w) = show w
constToString (ClsrSizeC clsrId) = "clsr_size_" ++ show clsrId
constToString (ClsrAppLimitC clsrId) = "clsr_applimit_" ++ show clsrId
constToString (ClsrCodePtrC clsrId) = "clsr_fn_" ++ show clsrId
constToString ClsrTagC = "0x1"
constToString ClsrBaseTagC = "0x1"
constToString ClsrNodeTagC = "0x3"
constToString IntTagC = "0x0"
constToString BoolTagC = "0x2"
constToString BoolFalseC = "0x2"
constToString BoolTrueC = "0x6"
constToString ClearTagBitsC = N.showHex (B.complement 3 :: Int) ""

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
lowerSymAddress (VarPlusVarL r1 r2) = LitWordOp $ show r2 ++ "(" ++ show r1 ++ ")"

data Op = MemOp1 Reg | MemOp2 Reg Int | LitWordOp String
        deriving(Eq, Ord)

data C = E | G | L deriving(Eq, Ord)

newtype Str = Str String deriving(Eq, Ord)
instance Show Str where show (Str s) = s

data MachineInst =
  LabelMI String
  | MovMI_RR Reg Reg | MovMI_OR Op Reg | MovMI_RO Reg Op | MovMI_IO Str Op
  | CmpMI_RR Reg Reg | CmpMI_OR Op Reg | CmpMI_RO Reg Op
  | CMovMI_RR C Reg Reg | CMovMI_OR C Op Reg | CMovMI_RO C Reg Op | CMovMI_IO C Int Op
  | Unimplemented String
  deriving(Eq, Ord)

deriving instance Show(GenLNode Reg e x)

lirNodeToMachineInst :: GenLNode Reg e x -> [MachineInst]
lirNodeToMachineInst (LabelLN lbl) = [LabelMI $ show lbl]
lirNodeToMachineInst (CopyWordLN (LitR cValue) reg) = [
  MovMI_OR (lowerConstant cValue) reg]
lirNodeToMachineInst (CopyWordLN (VarR srcR) destR) = [MovMI_RR srcR destR]
lirNodeToMachineInst (LoadWordLN symAddr reg) = [
  MovMI_OR (lowerSymAddress symAddr) reg]
lirNodeToMachineInst (StoreWordLN symAddr (VarR reg)) = [
  MovMI_RO reg (lowerSymAddress symAddr)]
lirNodeToMachineInst (StoreWordLN symAddr (LitR cValue)) = [
  MovMI_IO (Str $ constToString cValue) (lowerSymAddress symAddr)]
lirNodeToMachineInst (CmpWordLN (LitR _) (LitR _)) =
  error "unfolded constant!"
lirNodeToMachineInst (CmpWordLN (LitR c) (VarR v)) = [
  CmpMI_OR (lowerConstant c) v]
lirNodeToMachineInst (CmpWordLN (VarR v) (LitR c)) = [
  CmpMI_RO v (lowerConstant c)]
lirNodeToMachineInst (CmpWordLN (VarR vA) (VarR vB)) = [
  CmpMI_RR vA vB]
lirNodeToMachineInst others = [Unimplemented $ show others]

machinePrologue  :: Int -> [MachineInst]
machinePrologue _ = [Unimplemented "prologue"]

machineEpilogue :: Int -> [MachineInst]
machineEpilogue _ = [Unimplemented "epilogue"]

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
  show (LitWordOp lit) = "$" ++ lit

instance Show C where
  show E = "e"
  show G = "g"
  show L = "l"

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
  Unimplemented s -> "unimplemented: " ++ s
  where
    movq src dest = "movq " ++ show src ++ ", " ++ show dest
    cmpq a b = "cmpq " ++ show a ++ ", " ++ show b
    cmov c src dest = "cmov" ++ show c ++ " " ++ show src ++ ", " ++ show dest

instance Show MachineInst where
  show = showMInst
