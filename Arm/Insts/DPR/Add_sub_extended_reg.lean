/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- ADD/ADDS/SUB/SUBS (extended register), including CMP/CMN aliases.
import Arm.Decode
import Arm.Insts.Common
import Arm.Insts.CosimM

namespace DPR
open BitVec

/-- Decode UXTB/UXTH/UXTW/UXTX and SXTB/SXTH/SXTW/SXTX, then scale.
Narrowing to datasize also handles the 32-bit UXTX/SXTX encodings. -/
def arithmetic_extend_reg (datasize : Nat) (option : BitVec 3)
    (amount : BitVec 3) (value : BitVec 64) : BitVec datasize :=
  let esize := 8 <<< (extractLsb' 0 2 option).toNat
  let part := extractLsb' 0 esize value
  let extended := if getLsbD option 2 then signExtend datasize part else zeroExtend datasize part
  extended <<< amount.toNat

@[state_simp_rules]
def exec_add_sub_extended_reg (inst : Add_sub_extended_reg_cls) (s : ArmState) : ArmState :=
  if inst.imm3.toNat > 4 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let sub_op := inst.op = 1#1
    let setflags := inst.S = 1#1
    -- Rn=31 means SP, while Rm=31 always means ZR.
    let operand1 := read_gpr datasize inst.Rn s
    let operand2 := arithmetic_extend_reg datasize inst.option inst.imm3
      (read_gpr_zr 64 inst.Rm s)
    let operand2 := if sub_op then ~~~operand2 else operand2
    let carry := if sub_op then 1 else 0
    let (result, pstate) := AddWithCarry operand1 operand2 carry
    let s := if setflags then write_pstate pstate s else s
    -- The flags-setting forms discard Rd=31; other forms write SP.
    let s := if setflags then write_gpr_zr datasize inst.Rd result s
             else write_gpr datasize inst.Rd result s
    write_pc (read_pc s + 4#64) s

def Add_sub_extended_reg_cls.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let inst : Add_sub_extended_reg_cls :=
    { sf := ← BitVec.rand 1, op := ← BitVec.rand 1, S := ← BitVec.rand 1,
      Rm := ← BitVec.rand 5, option := ← BitVec.rand 3,
      imm3 := ← BitVec.rand 3 (hi := 4), Rn := ← BitVec.rand 5, Rd := ← BitVec.rand 5 }
  pure (some inst.toBitVec32)

end DPR
