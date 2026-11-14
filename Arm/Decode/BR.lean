/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
import Arm.BitVec

------------------------------------------------------------------------------

section Decode

open BitVec

-- Branches, Exception Generating and System Instructions

structure Compare_branch_cls where
  sf     : BitVec 1               -- [31:31]
  _fixed : BitVec 5 := 0b011010#5 -- [30:25]
  op     : BitVec 1               -- [24:24]
  imm19  : BitVec 19              -- [23:5]
  Rt     : BitVec 5               --  [4:0]
deriving DecidableEq, Repr

instance : ToString Compare_branch_cls where toString a := toString (repr a)

/-- TBZ/TBNZ: b5 selects both width and the high bit of the bit index. -/
structure Test_branch_cls where
  b5 : BitVec 1
  _fixed : BitVec 6 := 0b011011#6
  op : BitVec 1
  b40 : BitVec 5
  imm14 : BitVec 14
  Rt : BitVec 5
  deriving DecidableEq, Repr

instance : ToString Test_branch_cls where toString a := toString (repr a)

def Test_branch_cls.toBitVec32 (x : Test_branch_cls) : BitVec 32 :=
  x.b5 ++ x._fixed ++ x.op ++ x.b40 ++ x.imm14 ++ x.Rt

structure Uncond_branch_imm_cls where
  op     : BitVec 1              -- [31:31]
  _fixed : BitVec 5 := 0b00101#5 -- [30:26]
  imm26  : BitVec 26             --  [25:0]
deriving DecidableEq, Repr

instance : ToString Uncond_branch_imm_cls where toString a := toString (repr a)

structure Uncond_branch_reg_cls where
  _fixed : BitVec 7 := 0b1101011#7 -- [31:25]
  opc    : BitVec 4                -- [24:21]
  op2    : BitVec 5                -- [20:16]
  op3    : BitVec 6                -- [15:10]
  Rn     : BitVec 5                --   [9:5]
  -- This field is indeed called
  -- op4 in the Arm manual; note
  -- that the width is 5 bits.
  op4    : BitVec 5                --  [4:0]
deriving DecidableEq, Repr

instance : ToString Uncond_branch_reg_cls where toString a := toString (repr a)

/-- Plain BR, BLR and RET; authenticated/exception-return neighbors are separate. -/
def Uncond_branch_reg_cls.isSupported (x : Uncond_branch_reg_cls) : Bool :=
  (x.opc == 0#4 || x.opc == 1#4 || x.opc == 2#4) &&
  x.op2 == 31#5 && x.op3 == 0#6 && x.op4 == 0#5

structure Cond_branch_imm_cls where
  _fixed : BitVec 8 := 0b01010100#8 -- [31:24]
  imm19  : BitVec 19                -- [23:5]
  o0     : BitVec 1                 -- [4:4]
  cond   : BitVec 4                 -- [3:0]
deriving DecidableEq, Repr

instance : ToString Cond_branch_imm_cls where toString a := toString (repr a)

/-- MRS (system register); op0 is 2 + o0. -/
structure Read_system_register_cls where
  _fixed : BitVec 12 := 0xd53#12
  o0 : BitVec 1
  op1 : BitVec 3
  CRn : BitVec 4
  CRm : BitVec 4
  op2 : BitVec 3
  Rt : BitVec 5
  deriving DecidableEq, Repr

instance : ToString Read_system_register_cls where toString a := toString (repr a)

def Read_system_register_cls.encoding (x : Read_system_register_cls) : BitVec 16 :=
  1#1 ++ x.o0 ++ x.op1 ++ x.CRn ++ x.CRm ++ x.op2

def Read_system_register_cls.isThreadPointer (x : Read_system_register_cls) : Bool :=
  x.encoding == 0xc684#16 || x.encoding == 0xe682#16

def Read_system_register_cls.toBitVec32 (x : Read_system_register_cls) : BitVec 32 :=
  x._fixed ++ x.o0 ++ x.op1 ++ x.CRn ++ x.CRm ++ x.op2 ++ x.Rt

structure Hints_cls where
  _fixed1 : BitVec 20 := 0b11010101000000110010#20 -- [31:12]
  CRm     : BitVec 4                               -- [11:8]
  op2     : BitVec 3                               -- [7:5]
  _fixed2 : BitVec 5 := 0b11111#5                  -- [4:0]
deriving DecidableEq, Repr

instance : ToString Hints_cls where toString a := toString (repr a)

def Hints_cls.toBitVec32 (x : Hints_cls) : BitVec 32 :=
  x._fixed1 ++ x.CRm ++ x.op2 ++ x._fixed2

structure Clear_exclusive_cls where
  _fixed1 : BitVec 20 := 0xd5033#20
  imm4 : BitVec 4
  _fixed2 : BitVec 8 := 0x5f#8
deriving DecidableEq, Repr

instance : ToString Clear_exclusive_cls where toString a := toString (repr a)

def Clear_exclusive_cls.toBitVec32 (x : Clear_exclusive_cls) : BitVec 32 :=
  x._fixed1 ++ x.imm4 ++ x._fixed2

inductive BranchInst where
  | Read_system_register : Read_system_register_cls → BranchInst
  | Clear_exclusive : Clear_exclusive_cls → BranchInst
  | Test_branch : Test_branch_cls → BranchInst
  | Compare_branch :
    Compare_branch_cls → BranchInst
  | Uncond_branch_imm :
    Uncond_branch_imm_cls → BranchInst
  | Uncond_branch_reg :
    Uncond_branch_reg_cls → BranchInst
  | Cond_branch_imm :
    Cond_branch_imm_cls → BranchInst
  | Hints :
    Hints_cls → BranchInst
deriving DecidableEq, Repr

instance : ToString BranchInst where toString a := toString (repr a)

end Decode
