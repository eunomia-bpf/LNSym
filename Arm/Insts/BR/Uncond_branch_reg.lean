/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel
-/

-- Plain BR, BLR, RET

import Arm.Decode
import Arm.State
import Arm.Insts.Common
import Arm.BitVec

namespace BR

open BitVec

/-- Plain branch projection: PAC, guarded stacks and BTI state are outside
this model. Capture Xn before updating LR, including BLR X30. Register31 is XZR,
not SP. Fetching the target belongs to the subsequent instruction step. -/
@[state_simp_rules]
def exec_uncond_branch_reg (inst : Uncond_branch_reg_cls) (s : ArmState) : ArmState :=
  if !inst.isSupported then
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
  else
    let target := read_gpr_zr 64 inst.Rn s
    let s := if inst.opc = 1#4 then write_gpr 64 30#5 (read_pc s + 4#64) s else s
    write_pc target s

end BR
