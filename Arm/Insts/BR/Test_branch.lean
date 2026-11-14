/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Decode
import Arm.Insts.Common

namespace BR
open BitVec

@[state_simp_rules]
def Test_branch_inst.branch_taken_pc (inst : Test_branch_cls) (pc : BitVec 64) : BitVec 64 :=
  pc + signExtend 64 (inst.imm14 ++ 0b00#2)

@[state_simp_rules]
def Test_branch_inst.condition_holds (inst : Test_branch_cls) (s : ArmState) : Bool :=
  let datasize := if inst.b5 = 1#1 then 64 else 32
  let value := read_gpr_zr datasize inst.Rt s
  value.getLsbD (inst.b5 ++ inst.b40).toNat == (inst.op == 1#1)

@[state_simp_rules]
def exec_test_branch (inst : Test_branch_cls) (s : ArmState) : ArmState :=
  let pc := read_pc s
  write_pc (if Test_branch_inst.condition_holds inst s then
    Test_branch_inst.branch_taken_pc inst pc else pc + 4#64) s

end BR
