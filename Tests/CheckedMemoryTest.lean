/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Exec

/-! Permission, initialization and ordered fault-prefix tests call the public
checked step. Instruction bodies are shared with the total-memory model.
Assembled words and integer golden values are independent fixtures. Imported
legacy symbolic tests remain in the build to protect the original domain.
-/
section CheckedMemoryTest
open BitVec

private def initial : BitVec 256 := 0xfedcba987654321011223344556677888899aabbccddeeff00112233800180ff#256
private def priorEvent : MemoryAccessEvent := .memory .write 0x7000#64 [0xaa#8] true
private def valueBytes (n : Nat) (value : BitVec 256) : List (BitVec 8) :=
  (List.range n).map (fun i => extractLsb' (i * 8) 8 value)

private def entry (word : BitVec 32) (base address : BitVec 64) : ArmState :=
  let s := write_gpr 64 0#5 0x1122334455667788#64 ArmState.default
  let s := write_gpr 64 1#5 base s
  let s := write_gpr 64 2#5 0x99aabbccddeeff00#64 s
  let s := write_gpr 64 3#5 16#64 s
  let s := write_gpr 64 31#5 base s
  let s := write_sfp 128 0#5 0x0123456789abcdeffedcba9876543210#128 s
  let s := write_sfp 128 2#5 0x8899aabbccddeeff0011223344556677#128 s
  let s := write_pstate { n := 1#1, z := 0#1, c := 1#1, v := 1#1 } s
  let s := write_mem_bytes 32 address initial s
  let s := write_mem_bytes 1 (address - 1#64) 0xa5#8 s
  let s := write_mem_bytes 1 (address + 32#64) 0x5a#8 s
  let s := record_atomic_access
    { operation := .set, address := 8#64, bytes := 1,
      oldValue := 1#64, newValue := 3#64, acquire := false, release := true } s
  let s := write_exclusive_state { monitor := some { physicalStart := 0x9000#64, bytes := 16 } } s
  set_program (record_memory_access priorEvent s) [(0#64, word)]

private def fixedFrame (s t : ArmState) (address : BitVec 64) : Bool :=
  read_pstate t == read_pstate s && read_atomic_accesses t == read_atomic_accesses s &&
  read_exclusive_state t == read_exclusive_state s && t.program == s.program &&
  read_mem_bytes 1 (address - 1#64) t == 0xa5#8 &&
  read_mem_bytes 1 (address + 32#64) t == 0x5a#8

private structure SingleCase where
  word : BitVec 32
  base : BitVec 64
  address : BitVec 64
  afterBase : BitVec 64
  bytes : Nat
  load : Bool
  simd : Bool
  value : BitVec 128
  stored : BitVec 256

private def singles : List SingleCase := [
  { word := 0xf9400020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 8, load := true, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0xf8400020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 8, load := true, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0xf8410c20#32, base := 0x1000#64, address := 0x1010#64, afterBase := 0x1010#64, bytes := 8, load := true, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0xf8410420#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1010#64, bytes := 8, load := true, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0xf8636820#32, base := 0x1000#64, address := 0x1010#64, afterBase := 0x1000#64, bytes := 8, load := true, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0x3dc00020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 16, load := true, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x3cc00020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 16, load := true, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x3cc10c20#32, base := 0x1000#64, address := 0x1010#64, afterBase := 0x1010#64, bytes := 16, load := true, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x3cc10420#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1010#64, bytes := 16, load := true, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x3ce36820#32, base := 0x1000#64, address := 0x1010#64, afterBase := 0x1000#64, bytes := 16, load := true, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x39400020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 1, load := true, simd := false, value := 0xff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223380018088#256 },
  { word := 0x79400020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 2, load := true, simd := false, value := 0x80ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223380017788#256 },
  { word := 0xb9400020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 4, load := true, simd := false, value := 0x800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223355667788#256 },
  { word := 0xbd400020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 4, load := true, simd := true, value := 0x800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223376543210#256 },
  { word := 0xfd400020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 8, load := true, simd := true, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeefffedcba9876543210#256 },
  { word := 0xf9000020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 8, load := false, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0xf8000020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 8, load := false, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0xf8010c20#32, base := 0x1000#64, address := 0x1010#64, afterBase := 0x1010#64, bytes := 8, load := false, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0xf8010420#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1010#64, bytes := 8, load := false, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0xf8236820#32, base := 0x1000#64, address := 0x1010#64, afterBase := 0x1000#64, bytes := 8, load := false, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 },
  { word := 0x3d800020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 16, load := false, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x3c800020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 16, load := false, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x3c810c20#32, base := 0x1000#64, address := 0x1010#64, afterBase := 0x1010#64, bytes := 16, load := false, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x3c810420#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1010#64, bytes := 16, load := false, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x3ca36820#32, base := 0x1000#64, address := 0x1010#64, afterBase := 0x1000#64, bytes := 16, load := false, simd := true, value := 0x8899aabbccddeeff00112233800180ff#128, stored := 0xfedcba987654321011223344556677880123456789abcdeffedcba9876543210#256 },
  { word := 0x39000020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 1, load := false, simd := false, value := 0xff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223380018088#256 },
  { word := 0x79000020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 2, load := false, simd := false, value := 0x80ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223380017788#256 },
  { word := 0xb9000020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 4, load := false, simd := false, value := 0x800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223355667788#256 },
  { word := 0xbd000020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 4, load := false, simd := true, value := 0x800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223376543210#256 },
  { word := 0xfd000020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 8, load := false, simd := true, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeefffedcba9876543210#256 },
  { word := 0x39c00020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 1, load := true, simd := false, value := 0xffffffff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223380018088#256 },
  { word := 0x39800020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 1, load := true, simd := false, value := 0xffffffffffffffff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223380018088#256 },
  { word := 0x79c00020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 2, load := true, simd := false, value := 0xffff80ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223380017788#256 },
  { word := 0x79800020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 2, load := true, simd := false, value := 0xffffffffffff80ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223380017788#256 },
  { word := 0xb9800020#32, base := 0x1000#64, address := 0x1000#64, afterBase := 0x1000#64, bytes := 4, load := true, simd := false, value := 0xffffffff800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff0011223355667788#256 },
  { word := 0xf9400020#32, base := 0xfffffffffffffffc#64, address := 0xfffffffffffffffc#64, afterBase := 0xfffffffffffffffc#64, bytes := 8, load := true, simd := false, value := 0x112233800180ff#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff1122334455667788#256 }
]

-- first/last-byte denial, irrelevant permission denial, and uninitialized data.
private def singleProfile (i : Fin 5) (c : SingleCase) : MemoryProfile :=
  let denied := c.address + BitVec.ofNat 64 (if i.val == 2 then c.bytes - 1 else 0)
  let permission := fun a => if i.val == 1 || i.val == 2 then a != denied else true
  { readable := if c.load then permission else fun _ => i.val != 3,
    writable := if c.load then (fun _ => i.val != 3) else permission,
    initialized := fun _ => i.val != 4 }

private def checkSingle (c : SingleCase) (i : Fin 5) : Bool :=
  let profile := singleProfile i c
  let s := write_memory_profile (some profile) (entry c.word c.base c.address)
  let t := stepi_checked s
  let failed := i.val == 1 || i.val == 2
  let event := if c.load then
      .memory .read c.address (valueBytes c.bytes initial) (i.val != 4)
    else MemoryAccessEvent.memory .write c.address (valueBytes c.bytes c.stored) true
  let events := [priorEvent] ++ (if failed then
      [.fault (if c.load then .read c.address c.bytes else .write c.address c.bytes)] else [event])
  fixedFrame s t c.address &&
  (if failed then (match read_err t with | .Fault _ => true | _ => false) else read_err t == .None) &&
  read_pc t == (if failed then 0#64 else 4#64) && read_memory_accesses t == events &&
  read_mem_bytes 32 c.address t == (if failed || c.load then initial else c.stored) &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    let gp := if !failed && c.load && !c.simd && n == 0 then c.value.setWidth 64
              else if n == 1 then (if failed then c.base else c.afterBase) else read_gpr 64 reg s
    let fp := if !failed && c.load && c.simd && n == 0 then c.value else read_sfp 128 reg s
    read_gpr 64 reg t == gp && read_sfp 128 reg t == fp) &&
  (match read_memory_profile t with
    | none => false
    | some p => (List.range (c.bytes + 2)).all (fun j =>
        let a := c.address + BitVec.ofNat 64 j - 1#64
        let written := !failed && !c.load && j > 0 && j <= c.bytes
        p.initialized a == (written || profile.initialized a) &&
        p.readable a == profile.readable a && p.writable a == profile.writable a))

example : singles.all (fun c => ([0,1,2,3,4] : List (Fin 5)).all (checkSingle c)) = true := by
  native_decide

private structure PairCase where
  word : BitVec 32
  address : BitVec 64
  afterBase : BitVec 64
  bytes : Nat
  load : Bool
  simd : Bool
  singleEligible : Bool
  first : BitVec 128
  second : BitVec 128
  stored : BitVec 256

private def pairs : List PairCase := [
  { word := 0x297c0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 4, load := true, simd := false, singleEligible := true, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeffddeeff0055667788#256 },
  { word := 0x29c40820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 4, load := true, simd := false, singleEligible := true, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeffddeeff0055667788#256 },
  { word := 0x28fc0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 4, load := true, simd := false, singleEligible := true, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeffddeeff0055667788#256 },
  { word := 0xa97e0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 8, load := true, simd := false, singleEligible := true, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba9876543210112233445566778899aabbccddeeff001122334455667788#256 },
  { word := 0xa9c20820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 8, load := true, simd := false, singleEligible := true, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba9876543210112233445566778899aabbccddeeff001122334455667788#256 },
  { word := 0xa8fe0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 8, load := true, simd := false, singleEligible := true, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba9876543210112233445566778899aabbccddeeff001122334455667788#256 },
  { word := 0x697c0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 4, load := true, simd := false, singleEligible := false, first := 0xffffffff800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeffddeeff0055667788#256 },
  { word := 0x69c40820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 4, load := true, simd := false, singleEligible := false, first := 0xffffffff800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeffddeeff0055667788#256 },
  { word := 0x68fc0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 4, load := true, simd := false, singleEligible := false, first := 0xffffffff800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeffddeeff0055667788#256 },
  { word := 0x293c0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 4, load := false, simd := false, singleEligible := true, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeffddeeff0055667788#256 },
  { word := 0x29840820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 4, load := false, simd := false, singleEligible := true, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeffddeeff0055667788#256 },
  { word := 0x28bc0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 4, load := false, simd := false, singleEligible := true, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeffddeeff0055667788#256 },
  { word := 0xa93e0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 8, load := false, simd := false, singleEligible := true, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba9876543210112233445566778899aabbccddeeff001122334455667788#256 },
  { word := 0xa9820820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 8, load := false, simd := false, singleEligible := true, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba9876543210112233445566778899aabbccddeeff001122334455667788#256 },
  { word := 0xa8be0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 8, load := false, simd := false, singleEligible := true, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba9876543210112233445566778899aabbccddeeff001122334455667788#256 },
  { word := 0x2d7c0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 4, load := true, simd := true, singleEligible := false, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff4455667776543210#256 },
  { word := 0x2dc40820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 4, load := true, simd := true, singleEligible := false, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff4455667776543210#256 },
  { word := 0x2cfc0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 4, load := true, simd := true, singleEligible := false, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff4455667776543210#256 },
  { word := 0x6d7e0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 8, load := true, simd := true, singleEligible := false, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba987654321011223344556677880011223344556677fedcba9876543210#256 },
  { word := 0x6dc20820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 8, load := true, simd := true, singleEligible := false, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba987654321011223344556677880011223344556677fedcba9876543210#256 },
  { word := 0x6cfe0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 8, load := true, simd := true, singleEligible := false, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba987654321011223344556677880011223344556677fedcba9876543210#256 },
  { word := 0xad7f0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 16, load := true, simd := true, singleEligible := false, first := 0x8899aabbccddeeff00112233800180ff#128, second := 0xfedcba98765432101122334455667788#128, stored := 0x8899aabbccddeeff00112233445566770123456789abcdeffedcba9876543210#256 },
  { word := 0xadc10820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 16, load := true, simd := true, singleEligible := false, first := 0x8899aabbccddeeff00112233800180ff#128, second := 0xfedcba98765432101122334455667788#128, stored := 0x8899aabbccddeeff00112233445566770123456789abcdeffedcba9876543210#256 },
  { word := 0xacff0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 16, load := true, simd := true, singleEligible := false, first := 0x8899aabbccddeeff00112233800180ff#128, second := 0xfedcba98765432101122334455667788#128, stored := 0x8899aabbccddeeff00112233445566770123456789abcdeffedcba9876543210#256 },
  { word := 0x2d3c0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 4, load := false, simd := true, singleEligible := false, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff4455667776543210#256 },
  { word := 0x2d840820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 4, load := false, simd := true, singleEligible := false, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff4455667776543210#256 },
  { word := 0x2cbc0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 4, load := false, simd := true, singleEligible := false, first := 0x800180ff#128, second := 0x112233#128, stored := 0xfedcba987654321011223344556677888899aabbccddeeff4455667776543210#256 },
  { word := 0x6d3e0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 8, load := false, simd := true, singleEligible := false, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba987654321011223344556677880011223344556677fedcba9876543210#256 },
  { word := 0x6d820820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 8, load := false, simd := true, singleEligible := false, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba987654321011223344556677880011223344556677fedcba9876543210#256 },
  { word := 0x6cbe0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 8, load := false, simd := true, singleEligible := false, first := 0x112233800180ff#128, second := 0x8899aabbccddeeff#128, stored := 0xfedcba987654321011223344556677880011223344556677fedcba9876543210#256 },
  { word := 0xad3f0820#32, address := 0xfe0#64, afterBase := 0x1000#64, bytes := 16, load := false, simd := true, singleEligible := false, first := 0x8899aabbccddeeff00112233800180ff#128, second := 0xfedcba98765432101122334455667788#128, stored := 0x8899aabbccddeeff00112233445566770123456789abcdeffedcba9876543210#256 },
  { word := 0xad810820#32, address := 0x1020#64, afterBase := 0x1020#64, bytes := 16, load := false, simd := true, singleEligible := false, first := 0x8899aabbccddeeff00112233800180ff#128, second := 0xfedcba98765432101122334455667788#128, stored := 0x8899aabbccddeeff00112233445566770123456789abcdeffedcba9876543210#256 },
  { word := 0xacbf0820#32, address := 0x1000#64, afterBase := 0xfe0#64, bytes := 16, load := false, simd := true, singleEligible := false, first := 0x8899aabbccddeeff00112233800180ff#128, second := 0xfedcba98765432101122334455667788#128, stored := 0x8899aabbccddeeff00112233445566770123456789abcdeffedcba9876543210#256 }
]

private def pairProfile (i : Fin 7) (coalesced : Bool) (c : PairCase) : MemoryProfile :=
  let which := if i.val == 2 || i.val == 4 then c.bytes else 0
  let last := if i.val == 3 || i.val == 4 then c.bytes - 1 else 0
  let denied := c.address + BitVec.ofNat 64 (which + last)
  let permission := fun a => if 1 <= i.val && i.val <= 4 then a != denied else true
  { readable := if c.load then permission else fun _ => i.val != 6,
    writable := if c.load then (fun _ => i.val != 6) else permission,
    initialized := fun a => if i.val == 5 then (a - c.address).toNat < c.bytes
                    else i.val == 0 || i.val == 6,
    pairSingleAccess := coalesced }

private def checkPair (c : PairCase) (i : Fin 7) (coalesced : Bool) : Bool :=
  let profile := pairProfile i coalesced c
  let s := write_memory_profile (some profile) (entry c.word 0x1000#64 c.address)
  let t := stepi_checked s
  let failed := 1 <= i.val && i.val <= 4
  let secondFailed := i.val == 2 || i.val == 4
  let single := coalesced && c.singleEligible
  let bytes := if single then 2 * c.bytes else c.bytes
  let firstData := valueBytes bytes (if c.load then initial else c.stored)
  let secondData := valueBytes c.bytes ((if c.load then initial else c.stored) >>> (8 * c.bytes))
  let firstEvent := MemoryAccessEvent.memory (if c.load then .read else .write)
    c.address firstData (if c.load then i.val == 0 || i.val == 6 || (i.val == 5 && !single) else true)
  let secondAddress := c.address + BitVec.ofNat 64 c.bytes
  let secondEvent := MemoryAccessEvent.memory (if c.load then .read else .write)
    secondAddress secondData (if c.load then i.val == 0 || i.val == 6 else true)
  let faultAddress := if !single && secondFailed then secondAddress else c.address
  let reason := if c.load then MemoryAccessFault.read faultAddress bytes else .write faultAddress bytes
  let events := [priorEvent] ++ (if failed then
      (if !single && secondFailed then [firstEvent] else []) ++ [.fault reason]
    else if single then [firstEvent] else [firstEvent, secondEvent])
  let firstCommitted := !c.load && (!failed || (!single && secondFailed))
  let secondCommitted := !c.load && !failed
  let firstMask := (1#256 <<< (8 * c.bytes)) - 1#256
  let memory := if !c.load && !failed then c.stored
    else if firstCommitted then (initial &&& ~~~firstMask) ||| (c.stored &&& firstMask) else initial
  fixedFrame s t c.address &&
  (if failed then (match read_err t with | .Fault _ => true | _ => false) else read_err t == .None) &&
  read_pc t == (if failed then 0#64 else 4#64) && read_memory_accesses t == events &&
  read_mem_bytes 32 c.address t == memory &&
  (List.range 32).all (fun n =>
    let r := BitVec.ofNat 5 n
    let gp := if !failed && c.load && !c.simd && n == 0 then c.first.setWidth 64
              else if !failed && c.load && !c.simd && n == 2 then c.second.setWidth 64
              else if n == 1 then (if failed then 0x1000#64 else c.afterBase) else read_gpr 64 r s
    let fp := if !failed && c.load && c.simd && n == 0 then c.first
              else if !failed && c.load && c.simd && n == 2 then c.second else read_sfp 128 r s
    read_gpr 64 r t == gp && read_sfp 128 r t == fp) &&
  (match read_memory_profile t with
    | none => false
    | some p => (List.range (2 * c.bytes + 2)).all (fun j =>
        let a := c.address + BitVec.ofNat 64 j - 1#64
        let first := firstCommitted && j > 0 && j <= c.bytes
        let second := secondCommitted && j > c.bytes && j <= 2 * c.bytes
        p.initialized a == (first || second || profile.initialized a) &&
        p.readable a == profile.readable a && p.writable a == profile.writable a))

example : pairs.all (fun c => ([0,1,2,3,4,5,6] : List (Fin 7)).all (fun i =>
    [false,true].all (checkPair c i))) = true := by native_decide

-- SP check can be disabled only by an explicit platform profile.
example : [false,true].all (fun checkSP =>
    let profile : MemoryProfile := { spAlignmentCheck := checkSP }
    let s := entry 0xf94003e0#32 0x1008#64 0x1008#64
    let s := write_memory_profile (some profile) s
    let t := stepi_checked s
    if checkSP then
      read_pc t == 0#64 && read_gpr 64 0#5 t == read_gpr 64 0#5 s &&
      read_memory_accesses t == [priorEvent, .fault (.spAlignment 0x1008#64)]
    else read_pc t == 4#64 && read_gpr 64 0#5 t == initial.setWidth 64 &&
      read_memory_accesses t == [priorEvent, .memory .read 0x1008#64 (valueBytes 8 initial) false]) = true := by
  native_decide

-- Unsupported checked classes and missing profiles never use the total domain.
example : ([0xf9400020#32, 0xf8220020#32, 0xc85f7c20#32, 0x4c407020#32] : List (BitVec 32)).all
    (fun word => [false,true].all (fun bound =>
      if word == 0xf9400020#32 && bound then true else
      let s := entry word 0x1000#64 0x1000#64
      let s := if bound then write_memory_profile (some {}) s else s
      let t := stepi_checked s
      (match read_err t with | .Unimplemented _ => true | _ => false) &&
      read_pc t == 0#64 && read_memory_accesses t == [priorEvent] &&
      read_mem_bytes 32 0x1000#64 t == initial &&
      (List.range 32).all (fun n =>
        let r := BitVec.ofNat 5 n
        read_gpr 64 r t == read_gpr 64 r s && read_sfp 128 r t == read_sfp 128 r s))) = true := by
  native_decide

-- The original total-memory API still ignores the added platform attributes.
example : (let s := entry 0xf9400020#32 0x1000#64 0x1000#64
    let s := write_memory_profile (some { readable := fun _ => false }) s
    let t := stepi s
    read_err t == .None && read_pc t == 4#64 && read_gpr 64 0#5 t == initial.setWidth 64 &&
    read_memory_accesses t == [priorEvent]) = true := by native_decide

end CheckedMemoryTest
