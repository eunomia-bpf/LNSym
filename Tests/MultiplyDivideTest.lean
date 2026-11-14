/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Exec

/-! Encoded multiply/divide regressions: width/sign extension, accumulator and
source aliasing, high product bits, ZR/SP distinction, and division by zero.
Ra is architecturally ignored for UMULH; its noncanonical encoding is included.
The other GPRs and NZCV must be preserved, and successful instructions advance PC.
-/
section MultiplyDivideTest
open BitVec

private def entry (word : BitVec 32) (a b c : BitVec 64) : ArmState :=
  let s := write_gpr 64 31#5 0x1000#64 ArmState.default
  let s := write_gpr 64 0#5 0x55#64 s
  let s := write_gpr 64 1#5 a s
  let s := write_gpr 64 2#5 b s
  let s := write_gpr 64 3#5 c s
  let s := write_pstate { n := 1#1, z := 0#1, c := 1#1, v := 0#1 } s
  set_program s [(0#64, word)]

private def check (word : BitVec 32) (a b c expected : BitVec 64) : Bool :=
  let s := entry word a b c
  let t := run 1 s
  let dst := extractLsb' 0 5 word
  read_gpr_zr 64 dst t == expected && read_pc t == 4#64 && read_err t == .None &&
  read_pstate t == read_pstate s &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    if reg == dst && reg != 31#5 then true
    else read_gpr 64 reg t == read_gpr 64 reg s)

private def vectors : List (BitVec 32 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) := [
  (0x1b020c20#32, 0x6#64, 0x7#64, 0x32#64, 0x5c#64),
  (0x9b020c20#32, 0x6#64, 0x7#64, 0x32#64, 0x5c#64),
  (0x1b028c20#32, 0xdeadbeefffffffff#64, 0x2#64, 0x3#64, 0x5#64),
  (0x9b028c20#32, 0x6#64, 0x7#64, 0x32#64, 0x8#64),
  (0x9b028c21#32, 0x6#64, 0x7#64, 0x32#64, 0x8#64),
  (0x9b028c22#32, 0x6#64, 0x7#64, 0x32#64, 0x8#64),
  (0x9b028020#32, 0x6#64, 0x7#64, 0x0#64, 0x2b#64),
  (0x9b028fe0#32, 0x6#64, 0x7#64, 0x32#64, 0x32#64),
  (0x9b028c3f#32, 0x6#64, 0x7#64, 0x32#64, 0x0#64),
  (0x9ba20c20#32, 0x12345678ffffffff#64, 0xabcdef01ffffffff#64, 0x1#64, 0xfffffffe00000002#64),
  (0x9ba20c20#32, 0xffffffff#64, 0x1#64, 0xffffffffffffffff#64, 0xfffffffe#64),
  (0x9b220c20#32, 0x12345678ffffffff#64, 0x2#64, 0xa#64, 0x8#64),
  (0x9b220c20#32, 0x80000000#64, 0xffffffff#64, 0x5#64, 0x80000005#64),
  (0x9b220c20#32, 0xffffffff#64, 0xffffffff#64, 0xffffffffffffffff#64, 0x0#64),
  (0x9ba27c20#32, 0xffffffff#64, 0xffffffff#64, 0x7b#64, 0xfffffffe00000001#64),
  (0x9b227c20#32, 0x80000000#64, 0xffffffff#64, 0x7b#64, 0x80000000#64),
  (0x9bc27c20#32, 0xffffffffffffffff#64, 0xffffffffffffffff#64, 0x0#64, 0xfffffffffffffffe#64),
  (0x9bc27c20#32, 0x8000000000000000#64, 0x2#64, 0x0#64, 0x1#64),
  (0x9bc20020#32, 0xffffffffffffffff#64, 0xffffffffffffffff#64, 0x7b#64, 0xfffffffffffffffe#64),
  (0x9bc27c21#32, 0xffffffffffffffff#64, 0xffffffffffffffff#64, 0x0#64, 0xfffffffffffffffe#64),
  (0x1ac20820#32, 0x123456780000000a#64, 0xdeadbeef00000003#64, 0x0#64, 0x3#64),
  (0x9ac20820#32, 0xffffffffffffffff#64, 0x2#64, 0x0#64, 0x7fffffffffffffff#64),
  (0x9ac20820#32, 0xa#64, 0x3#64, 0x0#64, 0x3#64),
  (0x9ac20820#32, 0xa#64, 0x0#64, 0x0#64, 0x0#64),
  (0x9adf0820#32, 0xa#64, 0x3#64, 0x0#64, 0x0#64),
  (0x9ac20be0#32, 0xa#64, 0x3#64, 0x0#64, 0x0#64),
  (0x9ac2083f#32, 0xa#64, 0x3#64, 0x0#64, 0x0#64),
  (0x1ac20820#32, 0xa#64, 0x100000000#64, 0x0#64, 0x0#64),
  (0x9ac20820#32, 0x2#64, 0xa#64, 0x0#64, 0x0#64)
]

example : vectors.all (fun (word, a, b, c, expected) => check word a b c expected) = true := by
  native_decide

-- Long multiply is unallocated at sf=0, rather than a 32-bit operation.
example : (match read_err (run 1 (entry 0x1ba27c20#32 1#64 2#64 3#64)) with
  | .Illegal _ => true | _ => false) = true := by native_decide

end MultiplyDivideTest
