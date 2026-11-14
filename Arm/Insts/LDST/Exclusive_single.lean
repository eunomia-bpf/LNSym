/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- LDXR/LDAXR/STXR/STLXR and byte/halfword forms.
import Arm.Decode
import Arm.Memory.Access

namespace LDST
open BitVec

/-- Flat little-endian exclusives share instruction bodies in both domains.
The platform binds physical reservations and per-attempt monitor/race outcomes;
checked mode also binds byte permissions, initialization and effective LSE2/SP
attributes. Translation permission denial precedes local monitor clearing,
including failed local/global checks, as in ASL2023-03 ExclusiveMonitorsPass.
Physical external aborts and MMU translation are outside this flat profile.
The UNDEFINED choice is used for constrained-unpredictable status overlap. -/
@[state_simp_rules]
def exec_exclusive_single (inst : Exclusive_single_cls) (s : ArmState)
    (memory : MemoryMode := .total) : ArmState :=
  let load := inst.L = 1#1
  if (load && inst.Rs != 31#5) ||
      (!load && (inst.Rs = inst.Rt || (inst.Rs = inst.Rn && inst.Rn != 31#5))) then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let address := read_gpr 64 inst.Rn s
    if inst.Rn = 31#5 && !(decide (memory.spAligned s)) then
      memory.fault (.spAlignment address) s!"[Inst: {inst}] SP {address} is not aligned!" s
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
        if (load || monitorPassed || inputs.abortOnFailure) && !memory.atomicAligned bytes address s then
          memory.fault (.alignment address bytes) s!"[Inst: {inst}] Exclusive access {address} is not aligned!" s
        else MemoryMode.finish do
          -- VA failure returns before translation. After a successful VA check,
          -- even a failed local/global monitor still performs translation first.
          let s ← match memory, read_memory_profile s with
            | .checked, none =>
              .error (write_err (.Unimplemented "Checked exclusive requires a memory profile") s)
            | .checked, some profile =>
              if load && !MemoryMode.permitted profile.readable address bytes then
                .error (memory.fault (.read address bytes) s!"Exclusive read access denied at {address}" s)
              else if !load && inputs.virtualPass &&
                  !MemoryMode.permitted profile.writable address bytes then
                .error (memory.fault (.write address bytes) s!"Exclusive write access denied at {address}" s)
              else .ok s
            | .total, _ => .ok s
          if load then
            let value := read_mem_bytes bytes address s
            let access : ExclusiveAccess :=
              { action := .reserve, address, bytes, value := zeroExtend 64 value,
                acquire := inst.o0 = 1#1, release := false, success := true }
            let s := write_exclusive_state
              { ex with monitor := some inputs.reservation, accesses := ex.accesses ++ [access] } s
            let s := memory.observeExclusive access s
            let (value, s) ← memory.read bytes address s
            let s := write_gpr_zr regsize inst.Rt (zeroExtend regsize value) s
            .ok (write_pc (read_pc s + 4#64) s)
          else
            let passed := monitorPassed && inputs.commitPass
            let value := read_gpr_zr datasize inst.Rt s
            -- The local check clears the monitor before the memory write.
            let monitor := if !inputs.retainLocal || inputs.virtualPass then none else ex.monitor
            let access : ExclusiveAccess :=
              { action := .attempt, address, bytes, value := zeroExtend 64 value,
                acquire := false, release := inst.o0 = 1#1, success := passed }
            let s := write_exclusive_state
              { ex with monitor, accesses := ex.accesses ++ [access] } s
            let s := memory.observeExclusive access s
            let s ← if passed then memory.write bytes address value s else .ok s
            let s := write_gpr_zr 32 inst.Rs (if passed then 0#32 else 1#32) s
            .ok (write_pc (read_pc s + 4#64) s)

end LDST
