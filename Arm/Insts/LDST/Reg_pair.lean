/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Shilpi Goel, Yan Peng
-/
-- LDP, STP (pre-index, post-index and signed offset, GPR and SIMD&FP)

import Arm.Decode
import Arm.Memory.Access

----------------------------------------------------------------------

namespace LDST

open BitVec

structure Reg_pair_cls where
  opc       : BitVec 2
  SIMD?     : Bool
  L?        : Bool
  wback     : Bool
  postindex : Bool
  imm7      : BitVec 7
  Rt2       : BitVec 5
  Rn        : BitVec 5
  Rt        : BitVec 5
deriving DecidableEq, Repr

instance : ToString Reg_pair_cls where toString a := toString (repr a)

@[state_simp_rules]
def reg_pair_constrain_unpredictable (wback : Bool) (inst : Reg_pair_cls) : Bool :=
  match inst.SIMD?, inst.L? with
  | false, false => wback ∧ ((inst.Rt = inst.Rn) ∨ inst.Rt2 = inst.Rn) ∧ inst.Rn ≠ 31#5
  | false, true => (wback ∧ ((inst.Rt = inst.Rn) ∨ inst.Rt2 = inst.Rn) ∧ inst.Rn ≠ 31#5)
                ∨ (inst.Rt = inst.Rt2)
  | true, false => false
  | true, true => inst.Rt = inst.Rt2

@[state_simp_rules]
def reg_pair_operation (inst : Reg_pair_cls) (inst_str : String) (signed : Bool)
  (datasize : Nat) (offset : BitVec 64) (s : ArmState)
  (H1 : 8 ∣ datasize) (memory : MemoryMode := .total) : ArmState :=
  let address := read_gpr 64 inst.Rn s
  if inst.Rn = 31#5 ∧ ¬(memory.spAligned s) then
    memory.fault (.spAlignment address) s!"[Inst: {inst_str}] SP {address} is not aligned!" s
  else
    let address := if inst.postindex then address else address + offset
    let bytes := datasize / 8
    have h1 : bytes * 8 = datasize := Nat.div_mul_cancel H1
    have h2 : datasize + datasize = 2 * datasize := by omega
    have h3 : datasize + datasize = 2 * bytes * 8 := by
      rw [Nat.mul_assoc, h1, h2]
    -- Total mode preserves the original flat model. Checked mode uses two
    -- ordered accesses unless the platform selects a single double-size access.
    let single := memory = .total || (!inst.SIMD? && (!inst.L? || !signed) &&
      (read_memory_profile s).any (fun profile => profile.pairSingleAccess))
    MemoryMode.finish do
      let s ← if !inst.L? then do
          let data1 := ldst_read inst.SIMD? datasize inst.Rt s
          let data2 := ldst_read inst.SIMD? datasize inst.Rt2 s
          if single then
            memory.write (2 * bytes) address (BitVec.cast h3 (data2 ++ data1)) s
          else
            let s ← memory.write bytes address (BitVec.cast h1.symm data1) s
            memory.write bytes (address + BitVec.ofNat 64 bytes) (BitVec.cast h1.symm data2) s
        else do
          let (data1, data2, s) ← if single then do
              let (data, s) ← memory.read (2 * bytes) address s
              pure (extractLsb' 0 datasize data, extractLsb' datasize datasize data, s)
            else do
              let (data1, s) ← memory.read bytes address s
              let (data2, s) ← memory.read bytes (address + BitVec.ofNat 64 bytes) s
              pure (BitVec.cast h1 data1, BitVec.cast h1 data2, s)
          if !inst.SIMD? && signed then
            pure (write_gpr_zr 64 inst.Rt2 (signExtend 64 data2)
              (write_gpr_zr 64 inst.Rt (signExtend 64 data1) s))
          else
            pure (ldst_write inst.SIMD? datasize inst.Rt2 data2
              (ldst_write inst.SIMD? datasize inst.Rt data1 s))
      pure (if inst.wback then
        write_gpr 64 inst.Rn (if inst.postindex then address + offset else address) s
        else s)

@[state_simp_rules]
def exec_reg_pair_common (inst : Reg_pair_cls) (inst_str : String) (s : ArmState)
  (memory : MemoryMode := .total) : ArmState :=
  if -- UNDEFINED case for none-SIMD Reg Pair
     not inst.SIMD? ∧
     ((not inst.L? ∧ lsb inst.opc 0 = 1#1) ∨ (inst.opc = 0b11#2))
     -- UNDEFINED case for SIMD Reg Pair
     ∨ inst.SIMD? ∧ (inst.opc = 0b11#2)
     -- constrain unpredictable
     ∨ reg_pair_constrain_unpredictable inst.wback inst
  then
    write_err (StateError.Illegal "Illegal instruction {inst_str} encountered!") s
  else
    let signed := (lsb inst.opc 0) != 0#1
    let scale := if not inst.SIMD?
                 then 2 + (BitVec.toNat (lsb inst.opc 1))
                 else 2 + (BitVec.toNat inst.opc)
    let datasize := 8 <<< scale
    let offset := (signExtend 64 inst.imm7) <<< scale
    have H1 : 8 ∣ datasize := by
      simp_all! only [gt_iff_lt, Nat.shiftLeft_eq, Nat.dvd_mul_right, datasize]
    -- State Updates
    let s' := reg_pair_operation inst inst_str signed datasize offset s H1 memory
    if read_err s' = .None then write_pc (read_pc s + 4#64) s' else s'

@[state_simp_rules]
def exec_reg_pair_pre_indexed
  (inst : Reg_pair_pre_indexed_cls) (s : ArmState)
  (memory : MemoryMode := .total) : ArmState :=
  let extracted_inst : Reg_pair_cls :=
    { opc := inst.opc,
      SIMD? := inst.V = 1#1,
      L? := inst.L = 1#1,
      wback := true,
      postindex := false,
      imm7 := inst.imm7,
      Rt2 := inst.Rt2,
      Rn := inst.Rn,
      Rt := inst.Rt }
  exec_reg_pair_common extracted_inst s!"{inst}" s memory

@[state_simp_rules]
def exec_reg_pair_post_indexed
  (inst : Reg_pair_post_indexed_cls) (s : ArmState)
  (memory : MemoryMode := .total) : ArmState :=
  let extracted_inst : Reg_pair_cls :=
    { opc := inst.opc,
      SIMD? := inst.V = 1#1,
      L? := inst.L = 1#1,
      wback := true,
      postindex := true,
      imm7 := inst.imm7,
      Rt2 := inst.Rt2,
      Rn := inst.Rn,
      Rt := inst.Rt }
  exec_reg_pair_common extracted_inst s!"{inst}" s memory

@[state_simp_rules]
def exec_reg_pair_signed_offset
  (inst : Reg_pair_signed_offset_cls) (s : ArmState)
  (memory : MemoryMode := .total) : ArmState :=
  let extracted_inst : Reg_pair_cls :=
    { opc := inst.opc,
      SIMD? := inst.V = 1#1,
      L? := inst.L = 1#1,
      wback := false,
      postindex := false,
      imm7 := inst.imm7,
      Rt2 := inst.Rt2,
      Rn := inst.Rn,
      Rt := inst.Rt }
  exec_reg_pair_common extracted_inst s!"{inst}" s memory

end LDST
