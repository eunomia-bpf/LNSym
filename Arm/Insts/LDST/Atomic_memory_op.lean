/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- LDADD/LDCLR/LDSET, byte/halfword/word/doubleword, and store-only aliases.
import Arm.Decode
import Arm.Memory.Access

namespace LDST
open BitVec

/-- Atomic accesses capture address and source before any destination write.
The total-memory domain assumes FEAT_LSE and natural alignment. The checked
domain additionally uses explicit byte permissions, initialization and effective
alignment attributes. Both use flat little-endian memory. Acquire is suppressed
when Rt is ZR, including A=1. -/
@[state_simp_rules]
def exec_atomic_memory_op (inst : Atomic_memory_op_cls) (s : ArmState)
    (memory : MemoryMode := .total) : ArmState :=
  let operation := if inst.o3 != 0#1 then none else
    match inst.opc with
    | 0b000#3 => some AtomicOperation.add
    | 0b001#3 => some AtomicOperation.clear
    | 0b011#3 => some AtomicOperation.set
    | _ => none
  match operation with
  | none => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
  | some operation =>
    let bytes := 1 <<< inst.size.toNat
    let datasize := bytes * 8
    let regsize := if inst.size = 0b11#2 then 64 else 32
    let address := read_gpr 64 inst.Rn s
    if inst.Rn = 31#5 && !(decide (memory.spAligned s)) then
      memory.fault (.spAlignment address) s!"[Inst: {inst}] SP {address} is not aligned!" s
    else if !memory.atomicAligned bytes address s then
      memory.fault (.alignment address bytes) s!"[Inst: {inst}] Atomic access {address} is not aligned!" s
    else
      let operand := read_gpr_zr datasize inst.Rs s
      MemoryMode.finish do
        let (old, s) ← memory.atomic operation bytes address operand
          (inst.A = 1#1 && inst.Rt != 31#5) (inst.R = 1#1) s
        let s := write_gpr_zr regsize inst.Rt (zeroExtend regsize old) s
        .ok (write_pc (read_pc s + 4#64) s)

end LDST
