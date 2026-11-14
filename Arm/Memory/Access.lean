/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Insts.Common

/-- The original total-memory domain and a platform-bound access domain share
instruction execution functions. The checked domain records native byte effects
and failures; it is not a second ISA interpreter. -/
inductive MemoryMode where
  | total | checked
  deriving DecidableEq, Repr

namespace MemoryMode
open BitVec

-- Symbolic step generation uses an explicit simplification set.
attribute [state_simp_rules] Bind.bind Pure.pure Except.bind Except.pure

@[state_simp_rules]
def finish (result : Except ArmState ArmState) : ArmState :=
  match result with | .ok s | .error s => s

/-- All bytes of a wrapping architectural range must be permitted. -/
def permitted (permission : BitVec 64 -> Bool) (address : BitVec 64) (bytes : Nat) : Bool :=
  (List.range bytes).all (fun i => permission (address + BitVec.ofNat 64 i))

@[state_simp_rules]
def fault (mode : MemoryMode) (reason : MemoryAccessFault) (message : String)
    (s : ArmState) : ArmState :=
  let s := match mode with
    | .total => s
    | .checked => record_memory_access (.fault reason) s
  write_err (.Fault message) s

@[state_simp_rules]
def spAligned (mode : MemoryMode) (s : ArmState) : Prop :=
  match mode, read_memory_profile s with
  | .checked, some profile => profile.spAlignmentCheck = false ∨ CheckSPAlignment s
  | _, _ => CheckSPAlignment s

instance (mode : MemoryMode) : Decidable (spAligned mode s) := by
  cases mode <;> cases h : read_memory_profile s <;>
    simp only [spAligned, h] <;> infer_instance

@[state_simp_rules]
def read (mode : MemoryMode) (bytes : Nat) (address : BitVec 64) (s : ArmState) :
    Except ArmState (BitVec (bytes * 8) × ArmState) :=
  match mode with
  | .total => .ok (read_mem_bytes bytes address s, s)
  | .checked =>
    match read_memory_profile s with
    | none => .error (write_err (.Unimplemented "Checked read requires a memory profile") s)
    | some profile =>
      if permitted profile.readable address bytes then
        let value := read_mem_bytes bytes address s
        let data := (List.range bytes).map (fun i => read_mem (address + BitVec.ofNat 64 i) s)
        let event := MemoryAccessEvent.memory .read address data
          (permitted profile.initialized address bytes)
        .ok (value, record_memory_access event s)
      else
        .error (mode.fault (.read address bytes) s!"Read access denied at {address} ({bytes} bytes)" s)

@[state_simp_rules]
def write (mode : MemoryMode) (bytes : Nat) (address : BitVec 64)
    (value : BitVec (bytes * 8)) (s : ArmState) : Except ArmState ArmState :=
  match mode with
  | .total => .ok (write_mem_bytes bytes address value s)
  | .checked =>
    match read_memory_profile s with
    | none => .error (write_err (.Unimplemented "Checked write requires a memory profile") s)
    | some profile =>
      if permitted profile.writable address bytes then
        let data := (List.range bytes).map (fun i => extractLsb' (i * 8) 8 value)
        let initialized := fun a =>
          if (a - address).toNat < bytes then true else profile.initialized a
        let s := write_mem_bytes bytes address value s
        let s := write_memory_profile (some { profile with initialized }) s
        .ok (record_memory_access (.memory .write address data true) s)
      else
        .error (mode.fault (.write address bytes) s!"Write access denied at {address} ({bytes} bytes)" s)


/-- Effective flat-memory atomic alignment profile. Ordinary pair granularity
alone does not disable alignment faults. This follows ASL2023-03
AArch64_UnalignedAccessFaults: even with LSE2, the range must fit one aligned
16-byte quantity. The original total-memory domain stays naturally aligned. -/
@[state_simp_rules]
def atomicAligned (mode : MemoryMode) (bytes : Nat) (address : BitVec 64)
    (s : ArmState) : Bool :=
  address.toNat % bytes == 0 ||
  (mode == .checked && (read_memory_profile s).any (fun profile =>
    profile.lse2UnalignedWithin16 && address.toNat % 16 + bytes <= 16))

/-- One indivisible flat-memory RMW effect. Permission denial precedes any
memory, initialization, atomic-history or register commit. These byte permissions
are platform inputs, not a model of MMU translation or physical external aborts. -/
@[state_simp_rules]
def atomic (mode : MemoryMode) (operation : AtomicOperation) (bytes : Nat)
    (address : BitVec 64) (operand : BitVec (bytes * 8)) (acquire release : Bool)
    (s : ArmState) : Except ArmState (BitVec (bytes * 8) × ArmState) := do
  let s ← match mode with
    | .total => .ok s
    | .checked =>
      match read_memory_profile s with
      | none => .error (write_err (.Unimplemented "Checked atomic requires a memory profile") s)
      | some profile =>
        if !permitted profile.readable address bytes then
          .error (mode.fault (.read address bytes) s!"Atomic read access denied at {address}" s)
        else if !permitted profile.writable address bytes then
          .error (mode.fault (.write address bytes) s!"Atomic write access denied at {address}" s)
        else .ok s
  let old := read_mem_bytes bytes address s
  let value := match operation with
    | .add => old + operand
    | .clear => old &&& ~~~operand
    | .set => old ||| operand
  let access : AtomicAccess :=
    { operation, address, bytes, oldValue := zeroExtend 64 old,
      newValue := zeroExtend 64 value, acquire, release }
  let s := match mode, read_memory_profile s with
    | .checked, some profile =>
      let initialized := fun a =>
        if (a - address).toNat < bytes then true else profile.initialized a
      let s := write_memory_profile (some { profile with initialized }) s
      record_memory_access (.atomic access (permitted profile.initialized address bytes)) s
    | _, _ => s
  let s := record_atomic_access access (write_mem_bytes bytes address value s)
  .ok (old, s)

/-- Place monitor actions in the same ordered trace as memory effects/faults. -/
@[state_simp_rules]
def observeExclusive (mode : MemoryMode) (access : ExclusiveAccess) (s : ArmState) : ArmState :=
  match mode with
  | .total => s
  | .checked => record_memory_access (.exclusive access) s

end MemoryMode
