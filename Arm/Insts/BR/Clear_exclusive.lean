/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Decode
import Arm.Memory.Access

namespace BR

@[state_simp_rules]
def exec_clear_exclusive (_inst : Clear_exclusive_cls) (s : ArmState)
    (memory : MemoryMode := .total) : ArmState :=
  let ex := read_exclusive_state s
  let access : ExclusiveAccess :=
    { action := .clear, address := 0#64, bytes := 0, value := 0#64,
      acquire := false, release := false, success := true }
  let s := write_exclusive_state
    { ex with monitor := none, accesses := ex.accesses ++ [access] } s
  let s := memory.observeExclusive access s
  write_pc (read_pc s + 4#64) s

end BR
