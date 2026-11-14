/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Exec

/-! Assembled B/H/W/X LSE ADD/CLR/SET, all ordering variants, zero sources,
store aliases and source/destination/base overlap. Literal integer golden values
catch incorrect width, source capture, ZR/SP identity and atomic trace ordering.
This uses the flat-memory naturally aligned FEAT_LSE domain, not a concurrency
or permission-fault conformance claim.
-/
section AtomicMemoryTest
open BitVec

private def priorAccess : AtomicAccess :=
  { operation := .add, address := 8#64, bytes := 1, oldValue := 3#64,
    newValue := 5#64, acquire := false, release := false }

private def entry (word : BitVec 32) (initial : BitVec 128) (operand : BitVec 64) : ArmState :=
  let s := write_gpr 64 0#5 0xaaaaaaaaaaaaaaaa#64 ArmState.default
  let s := write_gpr 64 1#5 0x1000#64 s
  let s := write_gpr 64 2#5 operand s
  let s := write_gpr 64 31#5 0x1000#64 s
  let s := write_pstate { n := 1#1, z := 0#1, c := 1#1, v := 1#1 } s
  let s := write_mem_bytes 16 0x1000#64 initial s
  let s := write_mem_bytes 1 0xfff#64 0xa5#8 s
  let s := write_mem_bytes 1 0x1010#64 0x5a#8 s
  set_program (record_atomic_access priorAccess s) [(0#64, word)]

private def check (word : BitVec 32) (initial : BitVec 128) (operand old : BitVec 64)
    (expected : BitVec 128) (acquire release : Bool) (operation : AtomicOperation) : Bool :=
  let s := entry word initial operand
  let t := run 1 s
  let dst := extractLsb' 0 5 word
  let bytes := 1 <<< (extractLsb' 30 2 word).toNat
  let newValue := zeroExtend 64 (extractLsb' 0 (bytes * 8) expected)
  let event : AtomicAccess :=
    { operation, address := 0x1000#64, bytes, oldValue := old, newValue, acquire, release }
  read_pc t == 4#64 && read_err t == .None && read_pstate t == read_pstate s &&
  read_gpr 64 dst t == (if dst == 31#5 then 0x1000#64 else old) &&
  read_mem_bytes 16 0x1000#64 t == expected &&
  read_mem_bytes 1 0xfff#64 t == 0xa5#8 && read_mem_bytes 1 0x1010#64 t == 0x5a#8 &&
  read_atomic_accesses t == [priorAccess, event] &&
  (match decode_raw_inst word with
    | some (.LDST (.Atomic_memory_op i)) => i.toBitVec32 == word
    | _ => false) &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    (reg == dst || read_gpr 64 reg t == read_gpr 64 reg s) &&
    read_sfp 128 reg t == read_sfp 128 reg s) &&
  (match mayModifiedRegs word with
    | .ok regs => if dst == 31#5 then regs == [] else regs == [.GPR dst]
    | _ => false)

private def vectors : List (BitVec 32 × BitVec 128 × BitVec 64 × BitVec 64 × BitVec 128 × Bool × Bool × AtomicOperation) := [
  (0x38220020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xff#128, false, false, .add),
  (0x38220020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xffffffffffffffffffffffffffffff00#128, false, false, .add),
  (0x38220020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeefe#128, false, false, .add),
  (0x38220022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeefe#128, false, false, .add),
  (0x38220021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeefe#128, false, false, .add),
  (0x38210020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, false, .add),
  (0x3822003f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeefe#128, false, false, .add),
  (0x383f0020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, false, .add),
  (0x382203e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeefe#128, false, false, .add),
  (0x383f03ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, false, .add),
  (0x38210021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, false, .add),
  (0x38a20020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xff#128, true, false, .add),
  (0x38a20020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xffffffffffffffffffffffffffffff00#128, true, false, .add),
  (0x38a20020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeefe#128, true, false, .add),
  (0x38620020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xff#128, false, true, .add),
  (0x38620020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xffffffffffffffffffffffffffffff00#128, false, true, .add),
  (0x38620020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeefe#128, false, true, .add),
  (0x38e20020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xff#128, true, true, .add),
  (0x38e20020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xffffffffffffffffffffffffffffff00#128, true, true, .add),
  (0x38e20020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeefe#128, true, true, .add),
  (0x38221020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, false, false, .clear),
  (0x38221020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xfffffffffffffffffffffffffffffffe#128, false, false, .clear),
  (0x38221020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddee00#128, false, false, .clear),
  (0x38a21020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, true, false, .clear),
  (0x38a21020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xfffffffffffffffffffffffffffffffe#128, true, false, .clear),
  (0x38a21020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddee00#128, true, false, .clear),
  (0x38a21022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddee00#128, true, false, .clear),
  (0x38a21021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddee00#128, true, false, .clear),
  (0x38a11020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, true, false, .clear),
  (0x38a2103f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddee00#128, false, false, .clear),
  (0x38bf1020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, true, false, .clear),
  (0x38a213e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddee00#128, true, false, .clear),
  (0x38bf13ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, false, .clear),
  (0x38a11021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, true, false, .clear),
  (0x38621020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, false, true, .clear),
  (0x38621020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xfffffffffffffffffffffffffffffffe#128, false, true, .clear),
  (0x38621020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddee00#128, false, true, .clear),
  (0x38e21020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, true, true, .clear),
  (0x38e21020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xfffffffffffffffffffffffffffffffe#128, true, true, .clear),
  (0x38e21020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddee00#128, true, true, .clear),
  (0x38223020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xff#128, false, false, .set),
  (0x38223020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xffffffffffffffffffffffffffffffff#128, false, false, .set),
  (0x38223020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0x38a23020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xff#128, true, false, .set),
  (0x38a23020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xffffffffffffffffffffffffffffffff#128, true, false, .set),
  (0x38a23020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, true, false, .set),
  (0x38623020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xff#128, false, true, .set),
  (0x38623020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xffffffffffffffffffffffffffffffff#128, false, true, .set),
  (0x38623020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x38623022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x38623021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x38613020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x3862303f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x387f3020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x386233e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x387f33ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x38613021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x38e23020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xff#128, true, true, .set),
  (0x38e23020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xff#64, 0xffffffffffffffffffffffffffffffff#128, true, true, .set),
  (0x38e23020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xff#64, 0x112233445566778899aabbccddeeff#128, true, true, .set),
  (0x78220020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffff#128, false, false, .add),
  (0x78220020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xffffffffffffffffffffffffffff0000#128, false, false, .add),
  (0x78220020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6ffe#128, false, false, .add),
  (0x78a20020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffff#128, true, false, .add),
  (0x78a20020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xffffffffffffffffffffffffffff0000#128, true, false, .add),
  (0x78a20020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6ffe#128, true, false, .add),
  (0x78620020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffff#128, false, true, .add),
  (0x78620020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xffffffffffffffffffffffffffff0000#128, false, true, .add),
  (0x78620020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6ffe#128, false, true, .add),
  (0x78e20020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffff#128, true, true, .add),
  (0x78e20020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xffffffffffffffffffffffffffff0000#128, true, true, .add),
  (0x78e20020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6ffe#128, true, true, .add),
  (0x78e20022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6ffe#128, true, true, .add),
  (0x78e20021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6ffe#128, true, true, .add),
  (0x78e10020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddfeff#128, true, true, .add),
  (0x78e2003f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6ffe#128, false, true, .add),
  (0x78ff0020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, true, true, .add),
  (0x78e203e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6ffe#128, true, true, .add),
  (0x78ff03ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .add),
  (0x78e10021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddfeff#128, true, true, .add),
  (0x78221020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, false, false, .clear),
  (0x78221020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xfffffffffffffffffffffffffffffffe#128, false, false, .clear),
  (0x78221020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6e00#128, false, false, .clear),
  (0x78221022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6e00#128, false, false, .clear),
  (0x78221021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6e00#128, false, false, .clear),
  (0x78211020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .clear),
  (0x7822103f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6e00#128, false, false, .clear),
  (0x783f1020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .clear),
  (0x782213e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6e00#128, false, false, .clear),
  (0x783f13ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .clear),
  (0x78211021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .clear),
  (0x78a21020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, true, false, .clear),
  (0x78a21020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xfffffffffffffffffffffffffffffffe#128, true, false, .clear),
  (0x78a21020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6e00#128, true, false, .clear),
  (0x78621020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, false, true, .clear),
  (0x78621020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xfffffffffffffffffffffffffffffffe#128, false, true, .clear),
  (0x78621020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6e00#128, false, true, .clear),
  (0x78e21020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, true, true, .clear),
  (0x78e21020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xfffffffffffffffffffffffffffffffe#128, true, true, .clear),
  (0x78e21020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccdd6e00#128, true, true, .clear),
  (0x78223020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffff#128, false, false, .set),
  (0x78223020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xffffffffffffffffffffffffffffffff#128, false, false, .set),
  (0x78223020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0x78a23020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffff#128, true, false, .set),
  (0x78a23020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xffffffffffffffffffffffffffffffff#128, true, false, .set),
  (0x78a23020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, true, false, .set),
  (0x78a23022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, true, false, .set),
  (0x78a23021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, true, false, .set),
  (0x78a13020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddfeff#128, true, false, .set),
  (0x78a2303f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0x78bf3020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, true, false, .set),
  (0x78a233e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, true, false, .set),
  (0x78bf33ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0x78a13021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddfeff#128, true, false, .set),
  (0x78623020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffff#128, false, true, .set),
  (0x78623020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xffffffffffffffffffffffffffffffff#128, false, true, .set),
  (0x78623020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0x78e23020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffff#128, true, true, .set),
  (0x78e23020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffff#64, 0xffffffffffffffffffffffffffffffff#128, true, true, .set),
  (0x78e23020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xeeff#64, 0x112233445566778899aabbccddeeff#128, true, true, .set),
  (0xb8220020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffff#128, false, false, .add),
  (0xb8220020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xffffffffffffffffffffffff00000000#128, false, false, .add),
  (0xb8220020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdf6ffe#128, false, false, .add),
  (0xb8a20020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffff#128, true, false, .add),
  (0xb8a20020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xffffffffffffffffffffffff00000000#128, true, false, .add),
  (0xb8a20020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdf6ffe#128, true, false, .add),
  (0xb8620020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffff#128, false, true, .add),
  (0xb8620020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xffffffffffffffffffffffff00000000#128, false, true, .add),
  (0xb8620020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdf6ffe#128, false, true, .add),
  (0xb8620022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdf6ffe#128, false, true, .add),
  (0xb8620021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdf6ffe#128, false, true, .add),
  (0xb8610020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddfeff#128, false, true, .add),
  (0xb862003f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdf6ffe#128, false, true, .add),
  (0xb87f0020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .add),
  (0xb86203e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdf6ffe#128, false, true, .add),
  (0xb87f03ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .add),
  (0xb8610021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddfeff#128, false, true, .add),
  (0xb8e20020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffff#128, true, true, .add),
  (0xb8e20020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xffffffffffffffffffffffff00000000#128, true, true, .add),
  (0xb8e20020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdf6ffe#128, true, true, .add),
  (0xb8221020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, false, false, .clear),
  (0xb8221020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xfffffffffffffffffffffffffffffffe#128, false, false, .clear),
  (0xb8221020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdc6e00#128, false, false, .clear),
  (0xb8a21020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, true, false, .clear),
  (0xb8a21020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xfffffffffffffffffffffffffffffffe#128, true, false, .clear),
  (0xb8a21020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdc6e00#128, true, false, .clear),
  (0xb8621020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, false, true, .clear),
  (0xb8621020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xfffffffffffffffffffffffffffffffe#128, false, true, .clear),
  (0xb8621020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdc6e00#128, false, true, .clear),
  (0xb8e21020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, true, true, .clear),
  (0xb8e21020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xfffffffffffffffffffffffffffffffe#128, true, true, .clear),
  (0xb8e21020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdc6e00#128, true, true, .clear),
  (0xb8e21022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdc6e00#128, true, true, .clear),
  (0xb8e21021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdc6e00#128, true, true, .clear),
  (0xb8e11020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, true, true, .clear),
  (0xb8e2103f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdc6e00#128, false, true, .clear),
  (0xb8ff1020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, true, true, .clear),
  (0xb8e213e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabb4cdc6e00#128, true, true, .clear),
  (0xb8ff13ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .clear),
  (0xb8e11021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, true, true, .clear),
  (0xb8223020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffff#128, false, false, .set),
  (0xb8223020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xffffffffffffffffffffffffffffffff#128, false, false, .set),
  (0xb8223020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0xb8223022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0xb8223021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0xb8213020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddfeff#128, false, false, .set),
  (0xb822303f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0xb83f3020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0xb82233e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0xb83f33ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .set),
  (0xb8213021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddfeff#128, false, false, .set),
  (0xb8a23020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffff#128, true, false, .set),
  (0xb8a23020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xffffffffffffffffffffffffffffffff#128, true, false, .set),
  (0xb8a23020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, true, false, .set),
  (0xb8623020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffff#128, false, true, .set),
  (0xb8623020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xffffffffffffffffffffffffffffffff#128, false, true, .set),
  (0xb8623020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0xb8e23020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffff#128, true, true, .set),
  (0xb8e23020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffff#64, 0xffffffffffffffffffffffffffffffff#128, true, true, .set),
  (0xb8e23020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0xccddeeff#64, 0x112233445566778899aabbccddeeff#128, true, true, .set),
  (0xf8220020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffffffffffff#128, false, false, .add),
  (0xf8220020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xffffffffffffffff0000000000000000#128, false, false, .add),
  (0xf8220020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677888888884cdf6ffe#128, false, false, .add),
  (0xf8a20020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffffffffffff#128, true, false, .add),
  (0xf8a20020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xffffffffffffffff0000000000000000#128, true, false, .add),
  (0xf8a20020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677888888884cdf6ffe#128, true, false, .add),
  (0xf8a20022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677888888884cdf6ffe#128, true, false, .add),
  (0xf8a20021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677888888884cdf6ffe#128, true, false, .add),
  (0xf8a10020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddfeff#128, true, false, .add),
  (0xf8a2003f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677888888884cdf6ffe#128, false, false, .add),
  (0xf8bf0020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddeeff#128, true, false, .add),
  (0xf8a203e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677888888884cdf6ffe#128, true, false, .add),
  (0xf8bf03ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, false, .add),
  (0xf8a10021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddfeff#128, true, false, .add),
  (0xf8620020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffffffffffff#128, false, true, .add),
  (0xf8620020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xffffffffffffffff0000000000000000#128, false, true, .add),
  (0xf8620020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677888888884cdf6ffe#128, false, true, .add),
  (0xf8e20020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffffffffffff#128, true, true, .add),
  (0xf8e20020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xffffffffffffffff0000000000000000#128, true, true, .add),
  (0xf8e20020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677888888884cdf6ffe#128, true, true, .add),
  (0xf8221020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, false, false, .clear),
  (0xf8221020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xfffffffffffffffffffffffffffffffe#128, false, false, .clear),
  (0xf8221020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677001122334cdc6e00#128, false, false, .clear),
  (0xf8a21020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, true, false, .clear),
  (0xf8a21020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xfffffffffffffffffffffffffffffffe#128, true, false, .clear),
  (0xf8a21020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677001122334cdc6e00#128, true, false, .clear),
  (0xf8621020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, false, true, .clear),
  (0xf8621020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xfffffffffffffffffffffffffffffffe#128, false, true, .clear),
  (0xf8621020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677001122334cdc6e00#128, false, true, .clear),
  (0xf8621022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677001122334cdc6e00#128, false, true, .clear),
  (0xf8621021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677001122334cdc6e00#128, false, true, .clear),
  (0xf8611020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .clear),
  (0xf862103f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677001122334cdc6e00#128, false, true, .clear),
  (0xf87f1020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .clear),
  (0xf86213e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677001122334cdc6e00#128, false, true, .clear),
  (0xf87f13ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .clear),
  (0xf8611021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .clear),
  (0xf8e21020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0x0#128, true, true, .clear),
  (0xf8e21020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xfffffffffffffffffffffffffffffffe#128, true, true, .clear),
  (0xf8e21020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677001122334cdc6e00#128, true, true, .clear),
  (0xf8223020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffffffffffff#128, false, false, .set),
  (0xf8223020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xffffffffffffffffffffffffffffffff#128, false, false, .set),
  (0xf8223020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677ffffffffccddeeff#128, false, false, .set),
  (0xf8a23020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffffffffffff#128, true, false, .set),
  (0xf8a23020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xffffffffffffffffffffffffffffffff#128, true, false, .set),
  (0xf8a23020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677ffffffffccddeeff#128, true, false, .set),
  (0xf8623020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffffffffffff#128, false, true, .set),
  (0xf8623020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xffffffffffffffffffffffffffffffff#128, false, true, .set),
  (0xf8623020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677ffffffffccddeeff#128, false, true, .set),
  (0xf8e23020#32, 0x0#128, 0xffffffffffffffff#64, 0x0#64, 0xffffffffffffffff#128, true, true, .set),
  (0xf8e23020#32, 0xffffffffffffffffffffffffffffffff#128, 0x1#64, 0xffffffffffffffff#64, 0xffffffffffffffffffffffffffffffff#128, true, true, .set),
  (0xf8e23020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677ffffffffccddeeff#128, true, true, .set),
  (0xf8e23022#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677ffffffffccddeeff#128, true, true, .set),
  (0xf8e23021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677ffffffffccddeeff#128, true, true, .set),
  (0xf8e13020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddfeff#128, true, true, .set),
  (0xf8e2303f#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677ffffffffccddeeff#128, false, true, .set),
  (0xf8ff3020#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddeeff#128, true, true, .set),
  (0xf8e233e0#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x11223344556677ffffffffccddeeff#128, true, true, .set),
  (0xf8ff33ff#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddeeff#128, false, true, .set),
  (0xf8e13021#32, 0x112233445566778899aabbccddeeff#128, 0xffeeddcc800180ff#64, 0x8899aabbccddeeff#64, 0x112233445566778899aabbccddfeff#128, true, true, .set)
]

example : vectors.all
    (fun (word, initial, operand, old, expected, acquire, release, operation) =>
      check word initial operand old expected acquire release operation) = true := by native_decide

-- Faults and unsupported neighboring opcodes retain all incoming effects.
private def refusal (word : BitVec 32) (base sp : BitVec 64) (fault : Bool) : Bool :=
  let s := entry word 0x112233445566778899aabbccddeeff00#128 0xffffffffffffffff#64
  let s := write_gpr 64 1#5 base (write_gpr 64 31#5 sp s)
  let t := run 1 s
  (match read_err t with
    | .Fault _ => fault
    | .Unimplemented _ => !fault
    | _ => false) &&
  read_pc t == read_pc s && read_pstate t == read_pstate s &&
  read_atomic_accesses t == read_atomic_accesses s &&
  read_mem_bytes 32 0xff8#64 t == read_mem_bytes 32 0xff8#64 s &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    read_gpr 64 reg t == read_gpr 64 reg s && read_sfp 128 reg t == read_sfp 128 reg s)

example : ([
  (0x78220020#32, 0x1001#64, 0x1000#64, true),
  (0xb8220020#32, 0x1001#64, 0x1000#64, true),
  (0xf8220020#32, 0x1001#64, 0x1000#64, true),
  (0x382203e0#32, 0x1000#64, 0x1008#64, true),
  (0x38222020#32, 0x1000#64, 0x1000#64, false),
  (0x38228020#32, 0x1000#64, 0x1000#64, false)
] : List (BitVec 32 × BitVec 64 × BitVec 64 × Bool)).all
    (fun (word, base, sp, fault) => refusal word base sp fault) = true := by native_decide

-- An ordinary instruction preserves the pre-existing atomic history.
example : read_atomic_accesses (run 1 (entry 0xd503201f#32 0#128 0#64)) = [priorAccess] := by
  native_decide


-- Reuse the assembled integer goldens above, including aliases and overlapping
-- registers. Denied writes, including no-op RMWs, must not expose a read effect
-- or initialize memory. Both-denied cases establish read-denial priority.
private def priorMemoryEvent : MemoryAccessEvent := .memory .read 8#64 [3#8] true

private def checkChecked (word : BitVec 32) (initial : BitVec 128) (operand old : BitVec 64)
    (expected : BitVec 128) (acquire release : Bool) (operation : AtomicOperation)
    (profileCase : Nat) : Bool :=
  let address := 0x1000#64
  let bytes := 1 <<< (extractLsb' 30 2 word).toNat
  let last := address + BitVec.ofNat 64 (bytes - 1)
  let denyRead := profileCase == 2 || profileCase == 3 || profileCase == 6
  let denyWrite := profileCase == 4 || profileCase == 5 || profileCase == 6
  let denied := if profileCase == 3 || profileCase == 5 then last else address
  let profile : MemoryProfile :=
    { readable := fun a => !(denyRead && a == denied) && a != 0x2000#64,
      writable := fun a => !(denyWrite && a == denied) && a != 0x2000#64,
      initialized := fun a => profileCase == 7 || (profileCase != 1 && a != last) }
  let s := write_memory_profile (some profile)
    (record_memory_access priorMemoryEvent (entry word initial operand))
  let t := stepi_checked s
  let success := !denyRead && !denyWrite
  let dst := extractLsb' 0 5 word
  let access : AtomicAccess :=
    { operation, address, bytes, oldValue := old,
      newValue := zeroExtend 64 (extractLsb' 0 (bytes * 8) expected), acquire, release }
  let effect := if success then MemoryAccessEvent.atomic access (profileCase == 7)
    else .fault (if denyRead then .read address bytes else .write address bytes)
  (if success then read_err t == .None else
    match read_err t with | .Fault _ => true | _ => false) &&
  read_pc t == (if success then 4#64 else 0#64) &&
  read_pstate t == read_pstate s && t.program == s.program &&
  read_exclusive_state t == read_exclusive_state s &&
  read_atomic_accesses t == (if success then [priorAccess, access] else [priorAccess]) &&
  read_memory_accesses t == [priorMemoryEvent, effect] &&
  read_mem_bytes 16 address t == (if success then expected else initial) &&
  read_mem_bytes 1 0xfff#64 t == 0xa5#8 && read_mem_bytes 1 0x1010#64 t == 0x5a#8 &&
  (match read_memory_profile t with
    | none => false
    | some after =>
      after.spAlignmentCheck == profile.spAlignmentCheck &&
      after.pairSingleAccess == profile.pairSingleAccess &&
      after.lse2UnalignedWithin16 == profile.lse2UnalignedWithin16 &&
      (List.range 18).all (fun i =>
        let a := 0xfff#64 + BitVec.ofNat 64 i
        after.readable a == profile.readable a && after.writable a == profile.writable a &&
        after.initialized a == (if success && (a - address).toNat < bytes then true
          else profile.initialized a))) &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    read_gpr 64 reg t == (if success && dst != 31#5 && reg == dst then old
      else read_gpr 64 reg s) && read_sfp 128 reg t == read_sfp 128 reg s)

example : vectors.all
    (fun (word, initial, operand, old, expected, acquire, release, operation) =>
      (List.range 8).all (checkChecked word initial operand old expected acquire release operation)) = true := by
  native_decide

-- Misalignment precedes permissions. Effective LSE2 allows only contained
-- quantities, including wrapping addresses; pair access shape alone cannot.
private def checkAlignment (word : BitVec 32) (address old : BitVec 64)
    (allowUnaligned spCheck deny natural : Bool) : Bool :=
  let bytes := 1 <<< (extractLsb' 30 2 word).toNat
  let s := entry word 0#128 0#64
  let s := write_gpr 64 1#5 address (write_gpr 64 31#5 address s)
  let s := write_mem_bytes bytes address (old.setWidth (bytes * 8)) s
  let profile : MemoryProfile :=
    { readable := fun _ => !deny, writable := fun _ => !deny,
      initialized := fun _ => true, spAlignmentCheck := spCheck,
      pairSingleAccess := true, lse2UnalignedWithin16 := allowUnaligned }
  let s := write_memory_profile (some profile) s
  let t := stepi_checked s
  let spFault := extractLsb' 5 5 word == 31#5 && spCheck && address.toNat % 16 != 0
  let aligned := natural || (allowUnaligned && address.toNat % 16 + bytes <= 16)
  let success := !spFault && aligned && !deny
  let access : AtomicAccess :=
    { operation := .add, address, bytes, oldValue := old, newValue := old,
      acquire := false, release := false }
  let event := if spFault then MemoryAccessEvent.fault (.spAlignment address)
    else if !aligned then .fault (.alignment address bytes)
    else if deny then .fault (.read address bytes) else .atomic access true
  read_pc t == (if success then 4#64 else 0#64) &&
  (if success then read_err t == .None else
    match read_err t with | .Fault _ => true | _ => false) &&
  read_memory_accesses t == [event] &&
  read_atomic_accesses t == (if success then [priorAccess, access] else [priorAccess]) &&
  read_mem_bytes bytes address t == old.setWidth (bytes * 8) &&
  read_pstate t == read_pstate s && read_exclusive_state t == read_exclusive_state s &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    read_gpr 64 reg t == (if success && reg == 0#5 then old else read_gpr 64 reg s) &&
    read_sfp 128 reg t == read_sfp 128 reg s) &&
  (let total := stepi s;
    (if (extractLsb' 5 5 word == 31#5 && address.toNat % 16 != 0) || !natural then
      match read_err total with | .Fault _ => true | _ => false
    else read_err total == .None) && read_memory_accesses total == [])

example : ([
  (0x78220020#32, 0x1001#64, 0x2211#64, false),
  (0xb8220020#32, 0x1001#64, 0x44332211#64, false),
  (0xf8220020#32, 0x1001#64, 0x8877665544332211#64, false),
  (0xf8220020#32, 0x1009#64, 0x8877665544332211#64, false),
  (0xf8220020#32, 0xffffffffffffffff#64, 0x8877665544332211#64, false),
  (0xf8220020#32, 0xfffffffffffffff8#64, 0x8877665544332211#64, true),
  (0xf82203e0#32, 0x1008#64, 0x8877665544332211#64, true),
  (0xf82203e0#32, 0x1001#64, 0x8877665544332211#64, false)
] : List (BitVec 32 × BitVec 64 × BitVec 64 × Bool)).all (fun (word, address, old, natural) =>
    [false,true].all (fun allow => [false,true].all (fun sp =>
      [false,true].all (fun deny => checkAlignment word address old allow sp deny natural)))) = true := by
  native_decide

end AtomicMemoryTest
