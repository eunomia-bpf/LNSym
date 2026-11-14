/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CCMP/CCMN, register and unsigned imm5 forms at both operand widths.
import Arm.Decode
import Arm.Insts.Common
import Arm.Insts.CosimM

namespace DPR
open BitVec

@[state_simp_rules]
def exec_conditional_compare (inst : Conditional_compare_cls) (s : ArmState) : ArmState :=
  let flags : PState :=
    if ConditionHolds inst.cond s then
      let datasize := 32 <<< inst.sf.toNat
      let lhs := read_gpr_zr datasize inst.Rn s
      let rhs := if inst.immediate = 1#1 then zeroExtend datasize inst.operand
                 else read_gpr_zr datasize inst.operand s
      let rhs := if inst.op = 1#1 then ~~~rhs else rhs
      (AddWithCarry lhs rhs (if inst.op = 1#1 then 1#1 else 0#1)).snd
    else
      { n := extractLsb' 3 1 inst.nzcv, z := extractLsb' 2 1 inst.nzcv,
        c := extractLsb' 1 1 inst.nzcv, v := extractLsb' 0 1 inst.nzcv }
  let s := write_pstate flags s
  write_pc (read_pc s + 4#64) s

/-- Both compare operations, immediate/register operands and flag fallbacks. -/
def Conditional_compare_cls.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let inst : Conditional_compare_cls :=
    { sf := ← BitVec.rand 1, op := ← BitVec.rand 1,
      operand := ← BitVec.rand 5, cond := ← BitVec.rand 4,
      immediate := ← BitVec.rand 1, Rn := ← GPRIndex.rand,
      nzcv := ← BitVec.rand 4 }
  pure (some inst.toBitVec32)

end DPR
