/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Exec

/-! Encoded CSEL/CSINC/CSINV/CSNEG: both outcomes and widths, aliases, ZR,
32-bit zero extension, wraparound, and preservation of flags/SP/other registers.
These tests catch rejecting the three non-CSEL forms or transforming Rn on the
true branch instead of Rm on the false branch. -/
section ConditionalSelectTest
open BitVec

private def entry (word : BitVec 32) (z : BitVec 1) (b : BitVec 64) : ArmState :=
  let s := write_gpr 64 31#5 0x1000#64 ArmState.default
  let s := write_gpr 64 0#5 0x55#64 s
  let s := write_gpr 64 1#5 0x1122334400000005#64 s
  let s := write_gpr 64 2#5 b s
  let s := write_pstate { n := 1#1, z := z, c := 1#1, v := 1#1 } s
  set_program s [(0#64, word)]

private def check (word : BitVec 32) (z : BitVec 1) (expected : BitVec 64)
    (b : BitVec 64 := 0x8877665500000007#64) : Bool :=
  let s := entry word z b
  let t := run 1 s
  read_gpr 64 0#5 t == expected && read_pc t == 4#64 && read_err t == .None &&
  read_pstate t == read_pstate s &&
  (List.range 31).all (fun n => read_gpr 64 (BitVec.ofNat 5 (n + 1)) t ==
    read_gpr 64 (BitVec.ofNat 5 (n + 1)) s)

-- EQ false/true: CSEL, CSINC, CSINV, CSNEG, then the same W forms.
example : ([(0x9a820020#32, 0#1, 0x8877665500000007#64),
            (0x9a820420#32, 0#1, 0x8877665500000008#64),
            (0xda820020#32, 0#1, 0x778899aafffffff8#64),
            (0xda820420#32, 0#1, 0x778899aafffffff9#64),
            (0x9a820020#32, 1#1, 0x1122334400000005#64),
            (0x9a820420#32, 1#1, 0x1122334400000005#64),
            (0xda820020#32, 1#1, 0x1122334400000005#64),
            (0xda820420#32, 1#1, 0x1122334400000005#64),
            (0x1a820020#32, 0#1, 7#64), (0x1a820420#32, 0#1, 8#64),
            (0x5a820020#32, 0#1, 0xfffffff8#64), (0x5a820420#32, 0#1, 0xfffffff9#64),
            (0x1a820020#32, 1#1, 5#64), (0x1a820420#32, 1#1, 5#64),
            (0x5a820020#32, 1#1, 5#64), (0x5a820420#32, 1#1, 5#64)] :
    List (Prod (BitVec 32) (Prod (BitVec 1) (BitVec 64)))).all
      (fun (word, z, expected) => check word z expected) = true := by native_decide

example : check 0x9a820420#32 0#1 0#64 0xffffffffffffffff#64 = true := by native_decide
example : check 0x1a820420#32 0#1 0#64 0x88776655ffffffff#64 = true := by native_decide
-- CINC, CINV, CNEG, CSET, CSETM; destination XZR must not write SP.
example : check 0x9a810420#32 0#1 0x1122334400000006#64 = true := by native_decide
example : check 0xda810020#32 0#1 0xeeddccbbfffffffa#64 = true := by native_decide
example : check 0xda810420#32 0#1 0xeeddccbbfffffffb#64 = true := by native_decide
example : check 0x9a9f07e0#32 0#1 1#64 = true := by native_decide
example : check 0xda9f03e0#32 0#1 0xffffffffffffffff#64 = true := by native_decide
example : check 0xda82043f#32 0#1 0x55#64 = true := by native_decide

end ConditionalSelectTest
