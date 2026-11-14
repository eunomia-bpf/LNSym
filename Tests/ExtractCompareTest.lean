/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Exec

/-! Encoded EXTR/ROR and conditional compare: concatenation order, W zero
extension, boundary shifts, ZR, alias capture, arithmetic NZCV and fallback NZCV.
Conditional compares must preserve all GPRs and report an empty GPR footprint.
-/
section ExtractCompareTest
open BitVec

private def entry (word : BitVec 32) (a b : BitVec 64) (z : BitVec 1) : ArmState :=
  let s := write_gpr 64 31#5 0x1000#64 ArmState.default
  let s := write_gpr 64 0#5 0x55#64 s
  let s := write_gpr 64 1#5 a s
  let s := write_gpr 64 2#5 b s
  let s := write_pstate { n := 1#1, z := z, c := 1#1, v := 0#1 } s
  set_program s [(0#64, word)]

private def checkExtract (word : BitVec 32) (expected : BitVec 64) : Bool :=
  let s := entry word 0x1122334455667788#64 0x8877665544332211#64 1#1
  let t := run 1 s
  let dst := extractLsb' 0 5 word
  read_gpr_zr 64 dst t == expected && read_pc t == 4#64 && read_err t == .None &&
  read_pstate t == read_pstate s &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    if reg == dst && reg != 31#5 then true
    else read_gpr 64 reg t == read_gpr 64 reg s)

private def checkCompare (word : BitVec 32) (a b : BitVec 64)
    (z : BitVec 1) (expected : BitVec 4) : Bool :=
  let s := entry word a b z
  let t := run 1 s
  let p := read_pstate t
  p.n ++ p.z ++ p.c ++ p.v == expected && read_pc t == 4#64 && read_err t == .None &&
  (List.range 32).all (fun n => read_gpr 64 (BitVec.ofNat 5 n) t ==
    read_gpr 64 (BitVec.ofNat 5 n) s) &&
  (match DPR.MayModifyRegs word with | .ok [] => true | _ => false)

example : ([
  (0x93c22020#32, 0x8888776655443322#64),
  (0x13822020#32, 0x88443322#64),
  (0x93c20020#32, 0x8877665544332211#64),
  (0x93c2fc20#32, 0x22446688aaccef11#64),
  (0x13827c20#32, 0xaaccef10#64),
  (0x93c13420#32, 0xbc4089119a22ab33#64),
  (0x13813420#32, 0xbc42ab33#64),
  (0x93c223e0#32, 0x88776655443322#64),
  (0x93df2020#32, 0x8800000000000000#64),
  (0x93c2203f#32, 0x0#64),
  (0x93c22021#32, 0x8888776655443322#64)
] : List (BitVec 32 × BitVec 64)).all
    (fun (word, expected) => checkExtract word expected) = true := by native_decide

example : ([
  (0xfa420025#32, 0x7#64, 0x2#64, 0x1#1, 0x2#4),
  (0xfa420025#32, 0x2#64, 0x7#64, 0x1#1, 0x8#4),
  (0xfa420025#32, 0x7#64, 0x7#64, 0x1#1, 0x6#4),
  (0xfa420025#32, 0x8000000000000000#64, 0x1#64, 0x1#1, 0x3#4),
  (0xfa420025#32, 0x7fffffffffffffff#64, 0xffffffffffffffff#64, 0x1#1, 0x9#4),
  (0xfa420025#32, 0x7#64, 0x2#64, 0x0#1, 0x5#4),
  (0x7a420025#32, 0x1234567800000007#64, 0xdeadbeef00000002#64, 0x1#1, 0x2#4),
  (0x7a420025#32, 0x80000000#64, 0x1#64, 0x1#1, 0x3#4),
  (0x7a420025#32, 0x7fffffff#64, 0xffffffff#64, 0x1#1, 0x9#4),
  (0x7a420025#32, 0x0#64, 0x1#64, 0x1#1, 0x8#4),
  (0x7a420025#32, 0x7#64, 0x2#64, 0x0#1, 0x5#4),
  (0xfa5f082a#32, 0x1f#64, 0x0#64, 0x1#1, 0x6#4),
  (0xfa5f082a#32, 0x0#64, 0x0#64, 0x1#1, 0x8#4),
  (0xfa5f082a#32, 0x1f#64, 0x0#64, 0x0#1, 0xa#4),
  (0x7a5f082a#32, 0x123456780000001f#64, 0x0#64, 0x1#1, 0x6#4),
  (0x7a5f082a#32, 0x1f#64, 0x0#64, 0x0#1, 0xa#4),
  (0xfa40082a#32, 0x0#64, 0x0#64, 0x1#1, 0x6#4),
  (0xfa4203e5#32, 0x64#64, 0x2#64, 0x1#1, 0x8#4),
  (0xfa5f0025#32, 0x0#64, 0x7b#64, 0x1#1, 0x6#4),
  (0xba420025#32, 0xffffffffffffffff#64, 0x1#64, 0x1#1, 0x6#4),
  (0xba420025#32, 0x7fffffffffffffff#64, 0x1#64, 0x1#1, 0x9#4),
  (0x3a420025#32, 0xffffffff#64, 0x1#64, 0x1#1, 0x6#4),
  (0x3a420025#32, 0xffffffff#64, 0x1#64, 0x0#1, 0x5#4)
] : List (BitVec 32 × BitVec 64 × BitVec 64 × BitVec 1 × BitVec 4)).all
    (fun (word, a, b, z, expected) => checkCompare word a b z expected) = true := by native_decide

-- N must match sf, and a W extraction amount cannot be 32 or greater.
example : ([0x13c22020#32, 0x93822020#32, 0x13828020#32] : List (BitVec 32)).all
    (fun word => match read_err (run 1 (entry word 1#64 2#64 0#1)) with
      | .Illegal _ => true | _ => false) = true := by native_decide

end ExtractCompareTest
