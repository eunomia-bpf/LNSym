/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/
-- CSEL, CSINC, CSINV, CSNEG: 32- and 64-bit versions

import Arm.Decode
import Arm.State
import Arm.Insts.Common
import Arm.BitVec
import Arm.Insts.CosimM

namespace DPR

open BitVec

@[state_simp_rules]
def exec_conditional_select (inst : Conditional_select_cls) (s : ArmState) : ArmState :=
    let datasize := if inst.sf = 1#1 then 64 else 32
    -- Bit 11 (op2[1]) and S are fixed zero for this class.
    if inst.S != 0#1 || getLsbD inst.op2 1 then
      write_err
        (StateError.Unimplemented
          s!"Unsupported DPR.Conditional_select_cls {inst} encountered in exec_inst!")
      s
    else
      let result :=
        if ConditionHolds inst.cond s then
          read_gpr_zr datasize inst.Rn s
        else
          let operand := read_gpr_zr datasize inst.Rm s
          -- CSINV/CSNEG invert before the CSINC/CSNEG increment.
          let operand := if inst.op = 1#1 then ~~~operand else operand
          if getLsbD inst.op2 0 then operand + 1 else operand
      let s := write_pc ((read_pc s) + 4#64) s
      write_gpr_zr datasize inst.Rd result s

/-- Generate random instructions of the DPR.Conditional_select class. -/
def Conditional_select_cls.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let inst : Conditional_select_cls :=
    { sf    := ← BitVec.rand 1,
      op    := ← BitVec.rand 1,
      S     := ← pure 0#1,
      Rm    := ← GPRIndex.rand,
      cond  := ← BitVec.rand 4,
      op2   := 0#1 ++ (← BitVec.rand 1),
      Rn    := ← GPRIndex.rand,
      Rd    := ← GPRIndex.rand }
  pure (some (inst.toBitVec32))

----------------------------------------------------------------------

end DPR
