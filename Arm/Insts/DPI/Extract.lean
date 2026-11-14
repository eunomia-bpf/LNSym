/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- EXTR (and its ROR alias), 32- and 64-bit forms.
import Arm.Decode
import Arm.Insts.Common
import Arm.Insts.CosimM

namespace DPI
open BitVec

@[state_simp_rules]
def exec_extract (inst : Extract_cls) (s : ArmState) : ArmState :=
  if inst.N != inst.sf || (inst.sf == 0#1 && getLsbD inst.imms 5) then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := 32 <<< inst.sf.toNat
    let high := read_gpr_zr datasize inst.Rn s
    let low := read_gpr_zr datasize inst.Rm s
    let result := extractLsb' inst.imms.toNat datasize (high ++ low)
    let s := write_gpr_zr datasize inst.Rd result s
    write_pc (read_pc s + 4#64) s

/-- Generate legal W/X extraction amounts, including zero and the maximum. -/
def Extract_cls.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let sf ← BitVec.rand 1
  let amount ← BitVec.rand 6
  let inst : Extract_cls :=
    { sf := sf, N := sf,
      imms := if sf = 0#1 then zeroExtend 6 (amount.setWidth 5) else amount,
      Rn := ← GPRIndex.rand, Rm := ← GPRIndex.rand, Rd := ← GPRIndex.rand }
  pure (some inst.toBitVec32)

end DPI
