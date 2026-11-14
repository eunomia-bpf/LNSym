/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Exec

/-! Encoded B/H/W/X exclusive loads/stores and CLREX. Literal integer results
and explicit monitor outcomes exercise physical range containment, virtual/local/
global/commit failures, alignment/abort policy, SP/ZR and register aliases.
This is finite model regression evidence, not a hardware/Sail differential claim.
-/
section ExclusiveMemoryTest
open BitVec

private def priorAtomic : AtomicAccess :=
  { operation := .set, address := 8#64, bytes := 1, oldValue := 1#64,
    newValue := 3#64, acquire := false, release := true }
private def priorExclusive : ExclusiveAccess :=
  { action := .attempt, address := 0x8000#64, bytes := 4, value := 42#64,
    acquire := false, release := false, success := false }

private def profiles : List (ExclusiveInputs × Option ExclusiveMonitor × BitVec 64) := [
  ({ physicalAddress := 0x9000#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := true, globalPass := true, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x1000#64),
  ({ physicalAddress := 0x9000#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := false, virtualPass := true, globalPass := true, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x1000#64),
  ({ physicalAddress := 0x9000#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := false, globalPass := true, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x1000#64),
  ({ physicalAddress := 0x9000#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := true, globalPass := false, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x1000#64),
  ({ physicalAddress := 0x9000#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := true, globalPass := true, commitPass := false, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x1000#64),
  ({ physicalAddress := 0x9000#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := true, globalPass := true, commitPass := true, abortOnFailure := false }, none, 0x1000#64),
  ({ physicalAddress := 0x9010#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := true, globalPass := true, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x1000#64),
  ({ physicalAddress := 0x900f#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := true, globalPass := true, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x100f#64),
  ({ physicalAddress := 0x9000#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := true, globalPass := true, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 0 }, 0x1000#64),
  ({ physicalAddress := 0x9000#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := true, globalPass := true, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x2000#64),
  ({ physicalAddress := 0x9008#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := true, globalPass := true, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x1008#64),
  ({ physicalAddress := 0x9001#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := false, globalPass := true, commitPass := true, abortOnFailure := false }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x1001#64),
  ({ physicalAddress := 0x9001#64, reservation := { physicalStart := 0x9000#64, bytes := 16 }, retainLocal := true, virtualPass := false, globalPass := true, commitPass := true, abortOnFailure := true }, some { physicalStart := 0x9000#64, bytes := 16 }, 0x1001#64)
]
private def profile (i : Fin 13) := profiles[i.val]'(by
  simpa only [profiles, List.length_cons, List.length_nil] using i.isLt)

private def entry (word : BitVec 32) (initial : BitVec 128) (value base : BitVec 64)
    (inputs : Option ExclusiveInputs) (monitor : Option ExclusiveMonitor) : ArmState :=
  let s := write_gpr 64 0#5 value ArmState.default
  let s := write_gpr 64 1#5 base s
  let s := write_gpr 64 2#5 0xaaaabbbb99998888#64 s
  let s := write_gpr 64 3#5 0xccccdddd77776666#64 s
  let s := write_gpr 64 31#5 base s
  let s := write_pstate { n := 1#1, z := 0#1, c := 1#1, v := 1#1 } s
  let s := write_mem_bytes 16 base initial s
  let s := write_mem_bytes 1 (base - 1#64) 0xa5#8 s
  let s := write_mem_bytes 1 (base + 16#64) 0x5a#8 s
  let s := record_atomic_access priorAtomic s
  let s := write_exclusive_state { inputs, monitor, accesses := [priorExclusive] } s
  set_program s [(0#64, word)]

private def frame (s t : ArmState) (dst : BitVec 5) (base : BitVec 64) : Bool :=
  read_pc t == 4#64 && read_err t == .None && read_pstate t == read_pstate s &&
  read_atomic_accesses t == read_atomic_accesses s && t.program == s.program &&
  read_mem_bytes 1 (base - 1#64) t == 0xa5#8 &&
  read_mem_bytes 1 (base + 16#64) t == 0x5a#8 &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    (reg == dst && reg != 31#5 || read_gpr 64 reg t == read_gpr 64 reg s) &&
    read_sfp 128 reg t == read_sfp 128 reg s)

private def decodeFrame (word : BitVec 32) (dst : BitVec 5) : Bool :=
  (match decode_raw_inst word with
    | some (.LDST (.Exclusive_single i)) => i.toBitVec32 == word
    | _ => false) &&
  (match mayModifiedRegs word with
    | .ok regs => if dst == 31#5 then regs == [] else regs == [.GPR dst]
    | _ => false)

private def priorMemory : MemoryAccessEvent := .memory .read 0x8000#64 [42#8] true

private def boundMemory (ci : Nat) (base : BitVec 64) (bytes : Nat) (load : Bool) : MemoryProfile :=
  let last := base + BitVec.ofNat 64 (bytes - 1)
  let denied := if ci == 3 then last else base
  let deny := ci == 2 || ci == 3 || ci == 5
  { readable := fun a => !((deny && (load || ci == 5) || ci == 4 && !load) && a == denied),
    writable := fun a => !((deny && (!load || ci == 5) || ci == 4 && load) && a == denied),
    initialized := fun a => ci != 1 && (ci != 6 || a != last) }

private def bindMemory (s : ArmState) (ci : Option Nat) (base : BitVec 64)
    (bytes : Nat) (load : Bool) : ArmState :=
  match ci with
  | none => s
  | some ci => write_memory_profile (some (boundMemory ci base bytes load))
      (record_memory_access priorMemory s)

private def memoryFrame (s t : ArmState) (base : BitVec 64) (bytes : Nat) (wrote : Bool) : Bool :=
  match read_memory_profile s, read_memory_profile t with
  | none, none => true
  | some before, some after =>
    before.spAlignmentCheck == after.spAlignmentCheck &&
    before.pairSingleAccess == after.pairSingleAccess &&
    before.lse2UnalignedWithin16 == after.lse2UnalignedWithin16 &&
    (List.range 18).all (fun i =>
      let a := base - 1#64 + BitVec.ofNat 64 i
      after.readable a == before.readable a && after.writable a == before.writable a &&
      after.initialized a == (if wrote && (a - base).toNat < bytes then true else before.initialized a))
  | _, _ => false

private def permissionFault (s t : ArmState) (base : BitVec 64) (reason : MemoryAccessFault) : Bool :=
  (match read_err t with | .Fault _ => true | _ => false) && read_pc t == read_pc s &&
  read_exclusive_state t == read_exclusive_state s &&
  read_atomic_accesses t == read_atomic_accesses s && read_pstate t == read_pstate s &&
  t.program == s.program && read_memory_accesses t == [priorMemory, .fault reason] &&
  read_mem_bytes 18 (base - 1#64) t == read_mem_bytes 18 (base - 1#64) s &&
  memoryFrame s t base 0 false &&
  (List.range 32).all (fun n =>
    let r := BitVec.ofNat 5 n
    read_gpr 64 r t == read_gpr 64 r s && read_sfp 128 r t == read_sfp 128 r s)

private def checkLoad (word : BitVec 32) (initial : BitVec 128) (expected : BitVec 64) (ci : Option Nat := none) : Bool :=
  let (inputs, _, base) := profile 0
  let s := entry word initial 0xfedcba98800180ff#64 base (some inputs)
    (some { physicalStart := 0x7000#64, bytes := 32 })
  let bytes := 1 <<< (extractLsb' 30 2 word).toNat
  let s := bindMemory s ci base bytes true
  let t := if ci.isSome then stepi_checked s else run 1 s
  let dst := extractLsb' 0 5 word
  let event : ExclusiveAccess :=
    { action := .reserve, address := base, bytes := 1 <<< (extractLsb' 30 2 word).toNat,
      value := expected, acquire := getLsbD word 15, release := false, success := true }
  let ex := read_exclusive_state s
  let expectedEx := { ex with monitor := some inputs.reservation, accesses := [priorExclusive, event] }
  if ci.any (fun c => c == 2 || c == 3 || c == 5) then
    permissionFault s t base (.read base bytes)
  else
    frame s t dst base && decodeFrame word dst &&
    (dst == 31#5 || read_gpr 64 dst t == expected) &&
    read_mem_bytes 16 base t == initial && read_exclusive_state t == expectedEx &&
    memoryFrame s t base bytes false &&
    read_memory_accesses t == (if ci.isSome then
      [priorMemory, .exclusive event, .memory .read base
        ((List.range bytes).map (fun i => extractLsb' (i * 8) 8 initial))
        (ci != some 1 && ci != some 6)] else [])

private def loadVectors : List (BitVec 32 × BitVec 128 × BitVec 64) := [
  (0x85f7c20#32, 0x0#128, 0x0#64),
  (0x85f7c21#32, 0x0#128, 0x0#64),
  (0x85f7c3f#32, 0x0#128, 0x0#64),
  (0x85f7fe0#32, 0x0#128, 0x0#64),
  (0x85f7c20#32, 0xffffffffffffffffffffffffffffffff#128, 0xff#64),
  (0x85f7c21#32, 0xffffffffffffffffffffffffffffffff#128, 0xff#64),
  (0x85f7c3f#32, 0xffffffffffffffffffffffffffffffff#128, 0xff#64),
  (0x85f7fe0#32, 0xffffffffffffffffffffffffffffffff#128, 0xff#64),
  (0x85f7c20#32, 0x112233445566778899aabbccddeeff#128, 0xff#64),
  (0x85f7c21#32, 0x112233445566778899aabbccddeeff#128, 0xff#64),
  (0x85f7c3f#32, 0x112233445566778899aabbccddeeff#128, 0xff#64),
  (0x85f7fe0#32, 0x112233445566778899aabbccddeeff#128, 0xff#64),
  (0x85ffc20#32, 0x0#128, 0x0#64),
  (0x85ffc21#32, 0x0#128, 0x0#64),
  (0x85ffc3f#32, 0x0#128, 0x0#64),
  (0x85fffe0#32, 0x0#128, 0x0#64),
  (0x85ffc20#32, 0xffffffffffffffffffffffffffffffff#128, 0xff#64),
  (0x85ffc21#32, 0xffffffffffffffffffffffffffffffff#128, 0xff#64),
  (0x85ffc3f#32, 0xffffffffffffffffffffffffffffffff#128, 0xff#64),
  (0x85fffe0#32, 0xffffffffffffffffffffffffffffffff#128, 0xff#64),
  (0x85ffc20#32, 0x112233445566778899aabbccddeeff#128, 0xff#64),
  (0x85ffc21#32, 0x112233445566778899aabbccddeeff#128, 0xff#64),
  (0x85ffc3f#32, 0x112233445566778899aabbccddeeff#128, 0xff#64),
  (0x85fffe0#32, 0x112233445566778899aabbccddeeff#128, 0xff#64),
  (0x485f7c20#32, 0x0#128, 0x0#64),
  (0x485f7c21#32, 0x0#128, 0x0#64),
  (0x485f7c3f#32, 0x0#128, 0x0#64),
  (0x485f7fe0#32, 0x0#128, 0x0#64),
  (0x485f7c20#32, 0xffffffffffffffffffffffffffffffff#128, 0xffff#64),
  (0x485f7c21#32, 0xffffffffffffffffffffffffffffffff#128, 0xffff#64),
  (0x485f7c3f#32, 0xffffffffffffffffffffffffffffffff#128, 0xffff#64),
  (0x485f7fe0#32, 0xffffffffffffffffffffffffffffffff#128, 0xffff#64),
  (0x485f7c20#32, 0x112233445566778899aabbccddeeff#128, 0xeeff#64),
  (0x485f7c21#32, 0x112233445566778899aabbccddeeff#128, 0xeeff#64),
  (0x485f7c3f#32, 0x112233445566778899aabbccddeeff#128, 0xeeff#64),
  (0x485f7fe0#32, 0x112233445566778899aabbccddeeff#128, 0xeeff#64),
  (0x485ffc20#32, 0x0#128, 0x0#64),
  (0x485ffc21#32, 0x0#128, 0x0#64),
  (0x485ffc3f#32, 0x0#128, 0x0#64),
  (0x485fffe0#32, 0x0#128, 0x0#64),
  (0x485ffc20#32, 0xffffffffffffffffffffffffffffffff#128, 0xffff#64),
  (0x485ffc21#32, 0xffffffffffffffffffffffffffffffff#128, 0xffff#64),
  (0x485ffc3f#32, 0xffffffffffffffffffffffffffffffff#128, 0xffff#64),
  (0x485fffe0#32, 0xffffffffffffffffffffffffffffffff#128, 0xffff#64),
  (0x485ffc20#32, 0x112233445566778899aabbccddeeff#128, 0xeeff#64),
  (0x485ffc21#32, 0x112233445566778899aabbccddeeff#128, 0xeeff#64),
  (0x485ffc3f#32, 0x112233445566778899aabbccddeeff#128, 0xeeff#64),
  (0x485fffe0#32, 0x112233445566778899aabbccddeeff#128, 0xeeff#64),
  (0x885f7c20#32, 0x0#128, 0x0#64),
  (0x885f7c21#32, 0x0#128, 0x0#64),
  (0x885f7c3f#32, 0x0#128, 0x0#64),
  (0x885f7fe0#32, 0x0#128, 0x0#64),
  (0x885f7c20#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffff#64),
  (0x885f7c21#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffff#64),
  (0x885f7c3f#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffff#64),
  (0x885f7fe0#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffff#64),
  (0x885f7c20#32, 0x112233445566778899aabbccddeeff#128, 0xccddeeff#64),
  (0x885f7c21#32, 0x112233445566778899aabbccddeeff#128, 0xccddeeff#64),
  (0x885f7c3f#32, 0x112233445566778899aabbccddeeff#128, 0xccddeeff#64),
  (0x885f7fe0#32, 0x112233445566778899aabbccddeeff#128, 0xccddeeff#64),
  (0x885ffc20#32, 0x0#128, 0x0#64),
  (0x885ffc21#32, 0x0#128, 0x0#64),
  (0x885ffc3f#32, 0x0#128, 0x0#64),
  (0x885fffe0#32, 0x0#128, 0x0#64),
  (0x885ffc20#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffff#64),
  (0x885ffc21#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffff#64),
  (0x885ffc3f#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffff#64),
  (0x885fffe0#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffff#64),
  (0x885ffc20#32, 0x112233445566778899aabbccddeeff#128, 0xccddeeff#64),
  (0x885ffc21#32, 0x112233445566778899aabbccddeeff#128, 0xccddeeff#64),
  (0x885ffc3f#32, 0x112233445566778899aabbccddeeff#128, 0xccddeeff#64),
  (0x885fffe0#32, 0x112233445566778899aabbccddeeff#128, 0xccddeeff#64),
  (0xc85f7c20#32, 0x0#128, 0x0#64),
  (0xc85f7c21#32, 0x0#128, 0x0#64),
  (0xc85f7c3f#32, 0x0#128, 0x0#64),
  (0xc85f7fe0#32, 0x0#128, 0x0#64),
  (0xc85f7c20#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffffffffffff#64),
  (0xc85f7c21#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffffffffffff#64),
  (0xc85f7c3f#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffffffffffff#64),
  (0xc85f7fe0#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffffffffffff#64),
  (0xc85f7c20#32, 0x112233445566778899aabbccddeeff#128, 0x8899aabbccddeeff#64),
  (0xc85f7c21#32, 0x112233445566778899aabbccddeeff#128, 0x8899aabbccddeeff#64),
  (0xc85f7c3f#32, 0x112233445566778899aabbccddeeff#128, 0x8899aabbccddeeff#64),
  (0xc85f7fe0#32, 0x112233445566778899aabbccddeeff#128, 0x8899aabbccddeeff#64),
  (0xc85ffc20#32, 0x0#128, 0x0#64),
  (0xc85ffc21#32, 0x0#128, 0x0#64),
  (0xc85ffc3f#32, 0x0#128, 0x0#64),
  (0xc85fffe0#32, 0x0#128, 0x0#64),
  (0xc85ffc20#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffffffffffff#64),
  (0xc85ffc21#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffffffffffff#64),
  (0xc85ffc3f#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffffffffffff#64),
  (0xc85fffe0#32, 0xffffffffffffffffffffffffffffffff#128, 0xffffffffffffffff#64),
  (0xc85ffc20#32, 0x112233445566778899aabbccddeeff#128, 0x8899aabbccddeeff#64),
  (0xc85ffc21#32, 0x112233445566778899aabbccddeeff#128, 0x8899aabbccddeeff#64),
  (0xc85ffc3f#32, 0x112233445566778899aabbccddeeff#128, 0x8899aabbccddeeff#64),
  (0xc85fffe0#32, 0x112233445566778899aabbccddeeff#128, 0x8899aabbccddeeff#64)
]

example : loadVectors.all
    (fun (word, initial, expected) => checkLoad word initial expected) = true := by native_decide

private def checkStore (word : BitVec 32) (pi : Fin 13) (initial : BitVec 128)
    (operand : BitVec 64) (expected : BitVec 128) (passed : Bool) (ci : Option Nat := none) : Bool :=
  let (inputs, monitor, base) := profile pi
  let s := entry word initial operand base (some inputs) monitor
  let bytes := 1 <<< (extractLsb' 30 2 word).toNat
  let s := bindMemory s ci base bytes false
  let t := if ci.isSome then stepi_checked s else run 1 s
  let status := extractLsb' 16 5 word
  let src := extractLsb' 0 5 word
  let bytes := 1 <<< (extractLsb' 30 2 word).toNat
  let event : ExclusiveAccess :=
    { action := .attempt, address := base, bytes,
      value := zeroExtend 64 (read_gpr_zr (bytes * 8) src s),
      acquire := false, release := getLsbD word 15, success := passed }
  let ex := read_exclusive_state s
  let expectedMonitor := if !inputs.retainLocal || inputs.virtualPass then none else monitor
  let expectedEx := { ex with monitor := expectedMonitor, accesses := [priorExclusive, event] }
  if inputs.virtualPass && ci.any (fun c => c == 2 || c == 3 || c == 5) then
    permissionFault s t base (.write base bytes)
  else
    frame s t status base && decodeFrame word status &&
    (status == 31#5 || read_gpr 64 status t == (if passed then 0#64 else 1#64)) &&
    read_mem_bytes 16 base t == expected && read_exclusive_state t == expectedEx &&
    memoryFrame s t base bytes passed &&
    read_memory_accesses t == (if ci.isSome then [priorMemory, .exclusive event] ++
      (if passed then [.memory .write base
        ((List.range bytes).map (fun i => extractLsb' (i * 8) 8 expected)) true] else []) else [])

private def storeVectors : List (BitVec 32 × Fin 13 × BitVec 128 × BitVec 64 × BitVec 128 × Bool) := [
  (0x8027c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x8027c20#32, 1, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8027c20#32, 2, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8027c20#32, 3, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8027c20#32, 4, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8027c20#32, 5, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8027c20#32, 6, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8027c20#32, 7, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x8027c20#32, 8, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8027c20#32, 9, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x8027c20#32, 10, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x8027c20#32, 11, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8027c21#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddee00#128, true),
  (0x81f7c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x8027c3f#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddee00#128, true),
  (0x8027fe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x81f7fe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x8037c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x802fc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x802fc20#32, 1, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x802fc20#32, 2, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x802fc20#32, 3, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x802fc20#32, 4, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x802fc20#32, 5, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x802fc20#32, 6, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x802fc20#32, 7, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x802fc20#32, 8, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x802fc20#32, 9, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x802fc20#32, 10, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x802fc20#32, 11, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x802fc21#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddee00#128, true),
  (0x81ffc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x802fc3f#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddee00#128, true),
  (0x802ffe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x81fffe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x803fc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, true),
  (0x48027c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x48027c20#32, 1, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x48027c20#32, 2, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x48027c20#32, 3, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x48027c20#32, 4, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x48027c20#32, 5, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x48027c20#32, 6, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x48027c20#32, 7, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x48027c20#32, 8, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x48027c20#32, 9, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x48027c20#32, 10, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x48027c20#32, 11, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x48027c21#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd1000#128, true),
  (0x481f7c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x48027c3f#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd0000#128, true),
  (0x48027fe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x481f7fe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x48037c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x4802fc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x4802fc20#32, 1, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x4802fc20#32, 2, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x4802fc20#32, 3, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x4802fc20#32, 4, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x4802fc20#32, 5, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x4802fc20#32, 6, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x4802fc20#32, 7, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x4802fc20#32, 8, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x4802fc20#32, 9, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x4802fc20#32, 10, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x4802fc20#32, 11, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x4802fc21#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd1000#128, true),
  (0x481ffc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x4802fc3f#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd0000#128, true),
  (0x4802ffe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x481fffe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x4803fc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccdd80ff#128, true),
  (0x88027c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x88027c20#32, 1, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x88027c20#32, 2, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x88027c20#32, 3, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x88027c20#32, 4, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x88027c20#32, 5, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x88027c20#32, 6, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x88027c20#32, 7, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x88027c20#32, 8, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x88027c20#32, 9, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x88027c20#32, 10, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x88027c20#32, 11, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x88027c21#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb00001000#128, true),
  (0x881f7c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x88027c3f#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb00000000#128, true),
  (0x88027fe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x881f7fe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x88037c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x8802fc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x8802fc20#32, 1, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8802fc20#32, 2, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8802fc20#32, 3, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8802fc20#32, 4, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8802fc20#32, 5, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8802fc20#32, 6, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8802fc20#32, 7, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8802fc20#32, 8, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8802fc20#32, 9, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x8802fc20#32, 10, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x8802fc20#32, 11, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0x8802fc21#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb00001000#128, true),
  (0x881ffc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x8802fc3f#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb00000000#128, true),
  (0x8802ffe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x881fffe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0x8803fc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabb800180ff#128, true),
  (0xc8027c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc8027c20#32, 1, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc8027c20#32, 2, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc8027c20#32, 3, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc8027c20#32, 4, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc8027c20#32, 5, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc8027c20#32, 6, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc8027c20#32, 7, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc8027c20#32, 8, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc8027c20#32, 9, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc8027c20#32, 10, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc8027c20#32, 11, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc8027c21#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566770000000000001000#128, true),
  (0xc81f7c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc8027c3f#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566770000000000000000#128, true),
  (0xc8027fe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc81f7fe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc8037c20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc802fc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc802fc20#32, 1, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc802fc20#32, 2, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc802fc20#32, 3, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc802fc20#32, 4, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc802fc20#32, 5, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc802fc20#32, 6, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc802fc20#32, 7, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc802fc20#32, 8, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc802fc20#32, 9, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc802fc20#32, 10, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc802fc20#32, 11, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566778899aabbccddeeff#128, false),
  (0xc802fc21#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566770000000000001000#128, true),
  (0xc81ffc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc802fc3f#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x112233445566770000000000000000#128, true),
  (0xc802ffe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc81fffe0#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true),
  (0xc803fc20#32, 0, 0x112233445566778899aabbccddeeff#128, 0xfedcba98800180ff#64, 0x11223344556677fedcba98800180ff#128, true)
]

example : storeVectors.all
    (fun (word, pi, initial, operand, expected, passed) =>
      checkStore word pi initial operand expected passed) = true := by native_decide

private def refusal (word : BitVec 32) (pi : Fin 13) (base sp : BitVec 64)
    (missing : Bool) (kind : Nat) : Bool :=
  let (inputs, monitor, _) := profile pi
  let s := entry word 0x112233445566778899aabbccddeeff00#128 0xfedcba98800180ff#64 base
    (if missing then none else some inputs) monitor
  let s := write_gpr 64 31#5 sp s
  let t := run 1 s
  (match read_err t with
    | .Fault _ => kind == 0 | .Illegal _ => kind == 1
    | .Unimplemented _ => kind == 2 | _ => false) &&
  read_pc t == read_pc s && read_pstate t == read_pstate s &&
  read_exclusive_state t == read_exclusive_state s && read_atomic_accesses t == read_atomic_accesses s &&
  read_mem_bytes 32 (base - 8#64) t == read_mem_bytes 32 (base - 8#64) s &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    read_gpr 64 reg t == read_gpr 64 reg s && read_sfp 128 reg t == read_sfp 128 reg s)

example : ([
  (0x885f7c20#32, 0, 0x1000#64, 0x1000#64, true, 2),
  (0x88027c20#32, 0, 0x1000#64, 0x1000#64, true, 2),
  (0x88407c20#32, 0, 0x1000#64, 0x1000#64, false, 1),
  (0x88007c20#32, 0, 0x1000#64, 0x1000#64, false, 1),
  (0x88017c20#32, 0, 0x1000#64, 0x1000#64, false, 1),
  (0x85f7fe0#32, 0, 0x1000#64, 0x1008#64, false, 0),
  (0x8027fe0#32, 0, 0x1000#64, 0x1008#64, false, 0),
  (0x485f7fe0#32, 0, 0x1000#64, 0x1008#64, false, 0),
  (0x48027fe0#32, 0, 0x1000#64, 0x1008#64, false, 0),
  (0x885f7fe0#32, 0, 0x1000#64, 0x1008#64, false, 0),
  (0x88027fe0#32, 0, 0x1000#64, 0x1008#64, false, 0),
  (0xc85f7fe0#32, 0, 0x1000#64, 0x1008#64, false, 0),
  (0xc8027fe0#32, 0, 0x1000#64, 0x1008#64, false, 0),
  (0x485f7c20#32, 0, 0x1001#64, 0x1000#64, false, 0),
  (0x48027c20#32, 0, 0x1001#64, 0x1000#64, false, 0),
  (0x48027c20#32, 12, 0x1001#64, 0x1000#64, false, 0),
  (0x885f7c20#32, 0, 0x1001#64, 0x1000#64, false, 0),
  (0x88027c20#32, 0, 0x1001#64, 0x1000#64, false, 0),
  (0x88027c20#32, 12, 0x1001#64, 0x1000#64, false, 0),
  (0xc85f7c20#32, 0, 0x1001#64, 0x1000#64, false, 0),
  (0xc8027c20#32, 0, 0x1001#64, 0x1000#64, false, 0),
  (0xc8027c20#32, 12, 0x1001#64, 0x1000#64, false, 0)
] : List (BitVec 32 × Fin 13 × BitVec 64 × BitVec 64 × Bool × Nat)).all
    (fun (word, pi, base, sp, missing, kind) => refusal word pi base sp missing kind) = true := by native_decide

-- Every ignored CRm immediate clears the local reservation, with or without
-- a platform input binding. No data register or memory access is involved.
example : (List.range 16).all (fun imm => [false, true].all (fun bound =>
    let word := 0xd503305f#32 ||| (BitVec.ofNat 32 imm <<< 8)
    let (inputs, monitor, base) := profile 0
    let s := entry word 0xabcdef#128 0#64 base (if bound then some inputs else none) monitor
    let t := run 1 s
    let ex := read_exclusive_state s
    let event : ExclusiveAccess :=
      { action := .clear, address := 0#64, bytes := 0, value := 0#64,
        acquire := false, release := false, success := true }
    frame s t 31#5 base && read_mem_bytes 16 base t == read_mem_bytes 16 base s &&
    read_exclusive_state t == { ex with monitor := none, accesses := [priorExclusive, event] } &&
    (match decode_raw_inst word with
      | some (.BR (.Clear_exclusive i)) => i.toBitVec32 == word
      | _ => false) && (match mayModifiedRegs word with | .ok [] => true | _ => false))) = true := by
  native_decide

-- A real instruction sequence reserves, commits once, clears and then fails
-- the next store, without converting monitor failure into a memory write.
example : (let (inputs, monitor, base) := profile 0
    let s := entry 0xc85f7c20#32 0x112233445566778899aabbccddeeff00#128 0#64 base (some inputs) monitor
    let s := write_gpr 64 3#5 0xfedcba98800180ff#64 s
    let s := set_program s [(0#64, 0xc85f7c20#32), (4#64, 0xc802fc23#32),
      (8#64, 0xd5033f5f#32), (12#64, 0xc802fc23#32)]
    let t := run 4 s
    read_pc t == 16#64 && read_err t == .None && read_gpr 64 0#5 t == 0x99aabbccddeeff00#64 &&
    read_gpr 64 2#5 t == 1#64 && read_mem_bytes 8 base t == 0xfedcba98800180ff#64 &&
    (read_exclusive_state t).monitor == none &&
    ((read_exclusive_state t).accesses.map fun a => (a.action, a.success)) ==
      [(.attempt, false), (.reserve, true), (.attempt, true), (.clear, true), (.attempt, false)]) = true := by
  native_decide

-- An ordinary NOP preserves the exclusive state, including platform inputs.
example : (let (inputs, monitor, base) := profile 0
    let s := entry 0xd503201f#32 0#128 0#64 base (some inputs) monitor
    read_exclusive_state (run 1 s) == read_exclusive_state s) = true := by native_decide


-- Permission faults must precede monitor clearing, even when the local/global
-- check or final commit would fail. VA failure avoids translation permissions.
example : loadVectors.all (fun (word, initial, expected) =>
    (List.range 7).all (fun ci => checkLoad word initial expected (some ci))) = true := by
  native_decide

example : storeVectors.all (fun (word, pi, initial, operand, expected, passed) =>
    (List.range 7).all (fun ci => checkStore word pi initial operand expected passed (some ci))) = true := by
  native_decide

-- CLREX requires neither a memory profile nor per-attempt exclusive inputs.
example : (List.range 16).all (fun imm => [false,true].all (fun bound =>
    [false,true].all (fun memoryBound =>
      let (inputs, monitor, base) := profile 0
      let word := 0xd503305f#32 ||| (BitVec.ofNat 32 imm <<< 8)
      let s := entry word 0#128 0#64 base (if bound then some inputs else none) monitor
      let s := if memoryBound then bindMemory s (some 5) base 8 false
        else record_memory_access priorMemory s
      let t := stepi_checked s
      let access : ExclusiveAccess :=
        { action := .clear, address := 0#64, bytes := 0, value := 0#64,
          acquire := false, release := false, success := true }
      frame s t 31#5 base && read_mem_bytes 16 base t == 0#128 &&
      read_exclusive_state t == { (read_exclusive_state s) with
        monitor := none, accesses := [priorExclusive, access] } &&
      read_memory_accesses t == [priorMemory, .exclusive access] &&
      memoryFrame s t base 0 false))) = true := by
  native_decide


private def checkAlignment (word : BitVec 32) (address old : BitVec 64)
    (load natural allow spCheck deny virtual abort : Bool) : Bool :=
  let (inputs, monitor, _) := profile 0
  let inputs := { inputs with virtualPass := virtual, abortOnFailure := abort }
  let bytes := 1 <<< (extractLsb' 30 2 word).toNat
  let s := entry word (old.zeroExtend 128) 0#64 address (some inputs) monitor
  let p : MemoryProfile :=
    { readable := fun _ => !deny, writable := fun _ => !deny,
      spAlignmentCheck := spCheck, lse2UnalignedWithin16 := allow }
  let s := write_memory_profile (some p) (record_memory_access priorMemory s)
  let t := stepi_checked s
  let spFault := extractLsb' 5 5 word == 31#5 && spCheck && address.toNat % 16 != 0
  let aligned := natural || (allow && address.toNat % 16 + bytes <= 16)
  let alignmentFault := (load || virtual || abort) && !aligned
  let permFault := (load || virtual) && deny
  let faulted := spFault || alignmentFault || permFault
  let wrote := !faulted && !load && virtual
  let access : ExclusiveAccess :=
    { action := if load then .reserve else .attempt, address, bytes,
      value := if load then old else 0#64, acquire := false, release := false,
      success := load || virtual }
  let effects := if faulted then [.fault (if spFault then .spAlignment address
      else if alignmentFault then .alignment address bytes
      else if load then .read address bytes else .write address bytes)]
    else [.exclusive access] ++ (if load then [.memory .read address
      ((List.range bytes).map (fun i => extractLsb' (i * 8) 8 old)) false]
      else if virtual then [.memory .write address (List.replicate bytes 0#8) true] else [])
  let ex := read_exclusive_state s
  let expectedEx := if faulted then ex else { ex with
    monitor := if load then some inputs.reservation else if virtual then none else monitor,
    accesses := [priorExclusive, access] }
  read_exclusive_state t == expectedEx &&
  read_memory_accesses t == [priorMemory] ++ effects &&
  read_pc t == (if faulted then 0#64 else 4#64) &&
  (if faulted then match read_err t with | .Fault _ => true | _ => false
    else read_err t == .None) &&
  read_mem_bytes 16 address t == (if wrote then 0#128 else old.zeroExtend 128) &&
  read_mem_bytes 1 (address - 1#64) t == 0xa5#8 &&
  read_mem_bytes 1 (address + 16#64) t == 0x5a#8 &&
  read_pstate t == read_pstate s && read_atomic_accesses t == [priorAtomic] &&
  t.program == s.program && memoryFrame s t address bytes wrote &&
  (List.range 32).all (fun n =>
    let r := BitVec.ofNat 5 n
    read_gpr 64 r t == (if !faulted && load && r == 0#5 then old
      else if !faulted && !load && r == 2#5 then (if virtual then 0#64 else 1#64)
      else read_gpr 64 r s) && read_sfp 128 r t == read_sfp 128 r s)

-- Literal natural-alignment outcomes, including top-of-address-space cases.
-- Fault priority also covers the supplied implementation choice on failed STXR.
example : ([
  (0x485f7c20#32, 0x1001#64, 0x2211#64, true, false),
  (0xc85f7c20#32, 0x1009#64, 0x8877665544332211#64, true, false),
  (0x88027c20#32, 0x1001#64, 0x44332211#64, false, false),
  (0xc8027c20#32, 0x1009#64, 0x8877665544332211#64, false, false),
  (0xc85f7fe0#32, 0x1008#64, 0x8877665544332211#64, true, true),
  (0xc8027fe0#32, 0x1001#64, 0x8877665544332211#64, false, false),
  (0xc8027c20#32, 0xffffffffffffffff#64, 0x8877665544332211#64, false, false),
  (0x885f7c20#32, 0xfffffffffffffffc#64, 0x44332211#64, true, true),
  (0x085f7c20#32, 0x100f#64, 0x11#64, true, true),
  (0x08027c20#32, 0x100f#64, 0x11#64, false, true)
] : List (BitVec 32 × BitVec 64 × BitVec 64 × Bool × Bool)).all
    (fun (word, address, old, load, natural) =>
      [false,true].all (fun allow => [false,true].all (fun sp =>
        [false,true].all (fun deny => [false,true].all (fun virtual =>
          [false,true].all (fun abort => checkAlignment word address old load natural allow sp deny virtual abort)))))) = true := by
  native_decide

-- One real checked sequence observes reserve/read, attempt/write, clear, and
-- failed attempt, in a single trace. The successful write initializes its bytes.
example : (let (inputs, monitor, base) := profile 0
    let s := entry 0xc85f7c20#32 0x112233445566778899aabbccddeeff00#128 0#64 base (some inputs) monitor
    let s := write_gpr 64 3#5 0xfedcba98800180ff#64 s
    let s := write_memory_profile (some {}) (record_memory_access priorMemory s)
    let s := set_program s [(0#64, 0xc85f7c20#32), (4#64, 0xc802fc23#32),
      (8#64, 0xd5033f5f#32), (12#64, 0xc802fc23#32)]
    let t := stepi_checked (stepi_checked (stepi_checked (stepi_checked s)))
    let reserve : ExclusiveAccess :=
      { action := .reserve, address := base, bytes := 8,
        value := 0x99aabbccddeeff00#64, acquire := false, release := false, success := true }
    let attempt : ExclusiveAccess :=
      { action := .attempt, address := base, bytes := 8,
        value := 0xfedcba98800180ff#64, acquire := false, release := true, success := true }
    let clear : ExclusiveAccess :=
      { action := .clear, address := 0#64, bytes := 0,
        value := 0#64, acquire := false, release := false, success := true }
    read_pc t == 16#64 && read_err t == .None && read_gpr 64 0#5 t == reserve.value &&
    read_gpr 64 2#5 t == 1#64 && read_mem_bytes 8 base t == attempt.value &&
    (read_exclusive_state t).monitor == none &&
    (read_exclusive_state t).accesses == [priorExclusive, reserve, attempt, clear, { attempt with success := false }] &&
    read_memory_accesses t == [priorMemory, .exclusive reserve,
      .memory .read base [0x00#8,0xff#8,0xee#8,0xdd#8,0xcc#8,0xbb#8,0xaa#8,0x99#8] false,
      .exclusive attempt, .memory .write base [0xff#8,0x80#8,0x01#8,0x80#8,0x98#8,0xba#8,0xdc#8,0xfe#8] true,
      .exclusive clear, .exclusive { attempt with success := false }] &&
    (match read_memory_profile t with
      | some p => (List.range 10).all (fun i => p.initialized (base - 1#64 + BitVec.ofNat 64 i) == (0 < i && i < 9))
      | none => false)) = true := by
  native_decide

end ExclusiveMemoryTest
