/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- LDXR/LDAXR/STXR/STLXR and byte/halfword forms.
import Arm.Decode
import Arm.Insts.Common

namespace LDST
open BitVec

/-- Flat little-endian memory with natural exclusive alignment. The platform
binding supplies per-attempt physical reservations and monitor/race outcomes.
Permission, translation-abort and LSE2 profiles require further memory support.
The UNDEFINED choice is used for constrained-unpredictable status overlap. -/
@[state_simp_rules]
def exec_exclusive_single (inst : Exclusive_single_cls) (s : ArmState) : ArmState :=
  let load := inst.L = 1#1
  if (load && inst.Rs != 31#5) ||
      (!load && (inst.Rs = inst.Rt || (inst.Rs = inst.Rn && inst.Rn != 31#5))) then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let address := read_gpr 64 inst.Rn s
    if inst.Rn = 31#5 && !(decide (CheckSPAlignment s)) then
      write_err (StateError.Fault s!"[Inst: {inst}] SP {address} is not aligned!") s
    else
      let ex := read_exclusive_state s
      match ex.inputs with
      | none => write_err (StateError.Unimplemented "Exclusive access requires platform inputs") s
      | some inputs =>
        let bytes := 1 <<< inst.size.toNat
        let datasize := bytes * 8
        let regsize := if inst.size = 0b11#2 then 64 else 32
        let monitorPassed := inputs.retainLocal && inputs.virtualPass && inputs.globalPass &&
          (match ex.monitor with
           | none => false
           | some monitor => monitor.covers inputs.physicalAddress bytes)
        if (load || monitorPassed || inputs.abortOnFailure) && address.toNat % bytes != 0 then
          write_err (StateError.Fault s!"[Inst: {inst}] Exclusive access {address} is not aligned!") s
        else if load then
          let value := read_mem_bytes bytes address s
          let access : ExclusiveAccess :=
            { action := .reserve, address, bytes, value := zeroExtend 64 value,
              acquire := inst.o0 = 1#1, release := false, success := true }
          let s := write_gpr_zr regsize inst.Rt (zeroExtend regsize value) s
          let s := write_exclusive_state
            { ex with monitor := some inputs.reservation, accesses := ex.accesses ++ [access] } s
          write_pc (read_pc s + 4#64) s
        else
          let passed := monitorPassed && inputs.commitPass
          let value := read_gpr_zr datasize inst.Rt s
          -- A virtual-address check can return before the local monitor clear.
          -- Otherwise the local check clears it, including physical/global failure.
          let monitor := if !inputs.retainLocal || inputs.virtualPass then none else ex.monitor
          let access : ExclusiveAccess :=
            { action := .attempt, address, bytes, value := zeroExtend 64 value,
              acquire := false, release := inst.o0 = 1#1, success := passed }
          let s := if passed then write_mem_bytes bytes address value s else s
          let s := write_gpr_zr 32 inst.Rs (if passed then 0#32 else 1#32) s
          let s := write_exclusive_state
            { ex with monitor, accesses := ex.accesses ++ [access] } s
          write_pc (read_pc s + 4#64) s

end LDST
