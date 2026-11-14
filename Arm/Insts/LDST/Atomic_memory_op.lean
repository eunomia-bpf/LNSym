/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- LDADD/LDCLR/LDSET, byte/halfword/word/doubleword, and store-only aliases.
import Arm.Decode
import Arm.Insts.Common

namespace LDST
open BitVec

/-- Atomic accesses capture address and source before any destination write.
The model assumes FEAT_LSE, little-endian flat memory and natural alignment;
permissions, address translation and the FEAT_LSE2 alignment profile remain
separate extensions. Acquire is suppressed when Rt is ZR, including A=1. -/
@[state_simp_rules]
def exec_atomic_memory_op (inst : Atomic_memory_op_cls) (s : ArmState) : ArmState :=
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
    if inst.Rn = 31#5 && !(decide (CheckSPAlignment s)) then
      write_err (StateError.Fault s!"[Inst: {inst}] SP {address} is not aligned!") s
    else if address.toNat % bytes != 0 then
      write_err (StateError.Fault s!"[Inst: {inst}] Atomic access {address} is not aligned!") s
    else
      let operand := read_gpr_zr datasize inst.Rs s
      let old := read_mem_bytes bytes address s
      let value := match operation with
        | .add => old + operand
        | .clear => old &&& ~~~operand
        | .set => old ||| operand
      let access : AtomicAccess :=
        { operation, address, bytes, oldValue := zeroExtend 64 old,
          newValue := zeroExtend 64 value,
          acquire := inst.A = 1#1 && inst.Rt != 31#5, release := inst.R = 1#1 }
      let s := write_mem_bytes bytes address value s
      let s := write_gpr_zr regsize inst.Rt (zeroExtend regsize old) s
      let s := record_atomic_access access s
      write_pc (read_pc s + 4#64) s

end LDST
