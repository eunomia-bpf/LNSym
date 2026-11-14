/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Decode
import Arm.Insts.Common

namespace BR

/-- TPIDR_EL1/EL2 values and denial are resolved by an explicit current-step
platform binding. This projects system access outcomes, not the full EL/FGT/NV
trap computation or exception-vector entry. Even Rt=31 performs the access
check. Denial has a typed encoding and commits neither Xt nor PC. -/
@[state_simp_rules]
def exec_read_system_register (inst : Read_system_register_cls) (s : ArmState) : ArmState :=
  if !inst.isThreadPointer then
    write_err (.Unimplemented s!"Unsupported system register {inst.encoding}") s
  else
    match read_thread_pointer_inputs s with
    | none => write_err (.Unimplemented "MRS requires explicit system-register inputs") s
    | some inputs =>
      let value := if inst.encoding = 0xc684#16 then inputs.el1 else inputs.el2
      match value with
      | none => write_err (.SystemRegisterDenied inst.encoding) s
      | some value =>
        let s := write_gpr_zr 64 inst.Rt value s
        write_pc (read_pc s + 4#64) s

end BR
