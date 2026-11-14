/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Exec

/-! Encoded CNT and UADDLV checks. Golden results are literal byte population
counts and integer sums, independent of the model's element operations.
Exercise both widths, all legal reduction arrangements, aliases and V31.
-/
section VectorReductionTest
open BitVec

private def entry (word : BitVec 32) (input : BitVec 128) : ArmState :=
  let src := extractLsb' 5 5 word
  let dst := extractLsb' 0 5 word
  let s := write_gpr 64 31#5 0x1230#64 ArmState.default
  let s := write_pstate { n := 1#1, z := 0#1, c := 1#1, v := 1#1 } s
  let s := write_sfp 128 dst 0xffffffffffffffffffffffffffffffff#128 s
  let s := write_sfp 128 src input s
  set_program s [(0#64, word)]

private def frame (word : BitVec 32) (s t : ArmState) : Bool :=
  let dst := extractLsb' 0 5 word
  read_pc t == 4#64 && read_err t == .None && read_pstate t == read_pstate s &&
  (List.range 32).all (fun n =>
    let reg := BitVec.ofNat 5 n
    read_gpr 64 reg t == read_gpr 64 reg s &&
    (reg == dst || read_sfp 128 reg t == read_sfp 128 reg s)) &&
  (match mayModifiedRegs word with
    | .ok [.SFP reg] => reg == dst
    | _ => false)

private def check (word : BitVec 32) (input expected : BitVec 128) : Bool :=
  let s := entry word input
  let t := run 1 s
  read_sfp 128 (extractLsb' 0 5 word) t == expected && frame word s t

-- All 256 byte values in both 8B/16B arrangements. The other input half is
-- nonzero in 8B cases, and the destination is prefilled to check upper clearing.
private def byteCounts : List Nat := [0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7, 4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8]
example : (byteCounts.zipIdx).all (fun (count, byte) =>
    check 0x0e205820#32
      (BitVec.ofNat 128 (byte * 0x01010101010101010101010101010101))
      (BitVec.ofNat 128 (count * 0x0101010101010101)) &&
    check 0x4e205820#32
      (BitVec.ofNat 128 (byte * 0x01010101010101010101010101010101))
      (BitVec.ofNat 128 (count * 0x01010101010101010101010101010101))) = true := by
  native_decide

example : ([
  (0x0e205820#32, 0x0#128, 0x0#128),
  (0x0e205821#32, 0x0#128, 0x0#128),
  (0x0e205bff#32, 0x0#128, 0x0#128),
  (0x0e205820#32, 0xffffffffffffffffffffffffffffffff#128, 0x808080808080808#128),
  (0x0e205821#32, 0xffffffffffffffffffffffffffffffff#128, 0x808080808080808#128),
  (0x0e205bff#32, 0xffffffffffffffffffffffffffffffff#128, 0x808080808080808#128),
  (0x0e205820#32, 0x800102037f55aafffedcba9876543210#128, 0x705050305030301#128),
  (0x0e205821#32, 0x800102037f55aafffedcba9876543210#128, 0x705050305030301#128),
  (0x0e205bff#32, 0x800102037f55aafffedcba9876543210#128, 0x705050305030301#128),
  (0x0e205820#32, 0x1#128, 0x1#128),
  (0x0e205821#32, 0x1#128, 0x1#128),
  (0x0e205bff#32, 0x1#128, 0x1#128),
  (0x0e205820#32, 0x80000000000000000000000000000000#128, 0x0#128),
  (0x0e205821#32, 0x80000000000000000000000000000000#128, 0x0#128),
  (0x0e205bff#32, 0x80000000000000000000000000000000#128, 0x0#128),
  (0x0e205820#32, 0xffff00008000ffff0000ffff80000000#128, 0x80801000000#128),
  (0x0e205821#32, 0xffff00008000ffff0000ffff80000000#128, 0x80801000000#128),
  (0x0e205bff#32, 0xffff00008000ffff0000ffff80000000#128, 0x80801000000#128),
  (0x4e205820#32, 0x0#128, 0x0#128),
  (0x4e205821#32, 0x0#128, 0x0#128),
  (0x4e205bff#32, 0x0#128, 0x0#128),
  (0x4e205820#32, 0xffffffffffffffffffffffffffffffff#128, 0x8080808080808080808080808080808#128),
  (0x4e205821#32, 0xffffffffffffffffffffffffffffffff#128, 0x8080808080808080808080808080808#128),
  (0x4e205bff#32, 0xffffffffffffffffffffffffffffffff#128, 0x8080808080808080808080808080808#128),
  (0x4e205820#32, 0x800102037f55aafffedcba9876543210#128, 0x1010102070404080705050305030301#128),
  (0x4e205821#32, 0x800102037f55aafffedcba9876543210#128, 0x1010102070404080705050305030301#128),
  (0x4e205bff#32, 0x800102037f55aafffedcba9876543210#128, 0x1010102070404080705050305030301#128),
  (0x4e205820#32, 0x1#128, 0x1#128),
  (0x4e205821#32, 0x1#128, 0x1#128),
  (0x4e205bff#32, 0x1#128, 0x1#128),
  (0x4e205820#32, 0x80000000000000000000000000000000#128, 0x1000000000000000000000000000000#128),
  (0x4e205821#32, 0x80000000000000000000000000000000#128, 0x1000000000000000000000000000000#128),
  (0x4e205bff#32, 0x80000000000000000000000000000000#128, 0x1000000000000000000000000000000#128),
  (0x4e205820#32, 0xffff00008000ffff0000ffff80000000#128, 0x8080000010008080000080801000000#128),
  (0x4e205821#32, 0xffff00008000ffff0000ffff80000000#128, 0x8080000010008080000080801000000#128),
  (0x4e205bff#32, 0xffff00008000ffff0000ffff80000000#128, 0x8080000010008080000080801000000#128),
  (0x2e303820#32, 0x0#128, 0x0#128),
  (0x2e303821#32, 0x0#128, 0x0#128),
  (0x2e303bff#32, 0x0#128, 0x0#128),
  (0x2e303820#32, 0xffffffffffffffffffffffffffffffff#128, 0x7f8#128),
  (0x2e303821#32, 0xffffffffffffffffffffffffffffffff#128, 0x7f8#128),
  (0x2e303bff#32, 0xffffffffffffffffffffffffffffffff#128, 0x7f8#128),
  (0x2e303820#32, 0x800102037f55aafffedcba9876543210#128, 0x438#128),
  (0x2e303821#32, 0x800102037f55aafffedcba9876543210#128, 0x438#128),
  (0x2e303bff#32, 0x800102037f55aafffedcba9876543210#128, 0x438#128),
  (0x2e303820#32, 0x1#128, 0x1#128),
  (0x2e303821#32, 0x1#128, 0x1#128),
  (0x2e303bff#32, 0x1#128, 0x1#128),
  (0x2e303820#32, 0x80000000000000000000000000000000#128, 0x0#128),
  (0x2e303821#32, 0x80000000000000000000000000000000#128, 0x0#128),
  (0x2e303bff#32, 0x80000000000000000000000000000000#128, 0x0#128),
  (0x2e303820#32, 0xffff00008000ffff0000ffff80000000#128, 0x27e#128),
  (0x2e303821#32, 0xffff00008000ffff0000ffff80000000#128, 0x27e#128),
  (0x2e303bff#32, 0xffff00008000ffff0000ffff80000000#128, 0x27e#128),
  (0x6e303820#32, 0x0#128, 0x0#128),
  (0x6e303821#32, 0x0#128, 0x0#128),
  (0x6e303bff#32, 0x0#128, 0x0#128),
  (0x6e303820#32, 0xffffffffffffffffffffffffffffffff#128, 0xff0#128),
  (0x6e303821#32, 0xffffffffffffffffffffffffffffffff#128, 0xff0#128),
  (0x6e303bff#32, 0xffffffffffffffffffffffffffffffff#128, 0xff0#128),
  (0x6e303820#32, 0x800102037f55aafffedcba9876543210#128, 0x73b#128),
  (0x6e303821#32, 0x800102037f55aafffedcba9876543210#128, 0x73b#128),
  (0x6e303bff#32, 0x800102037f55aafffedcba9876543210#128, 0x73b#128),
  (0x6e303820#32, 0x1#128, 0x1#128),
  (0x6e303821#32, 0x1#128, 0x1#128),
  (0x6e303bff#32, 0x1#128, 0x1#128),
  (0x6e303820#32, 0x80000000000000000000000000000000#128, 0x80#128),
  (0x6e303821#32, 0x80000000000000000000000000000000#128, 0x80#128),
  (0x6e303bff#32, 0x80000000000000000000000000000000#128, 0x80#128),
  (0x6e303820#32, 0xffff00008000ffff0000ffff80000000#128, 0x6fa#128),
  (0x6e303821#32, 0xffff00008000ffff0000ffff80000000#128, 0x6fa#128),
  (0x6e303bff#32, 0xffff00008000ffff0000ffff80000000#128, 0x6fa#128),
  (0x2e703820#32, 0x0#128, 0x0#128),
  (0x2e703821#32, 0x0#128, 0x0#128),
  (0x2e703bff#32, 0x0#128, 0x0#128),
  (0x2e703820#32, 0xffffffffffffffffffffffffffffffff#128, 0x3fffc#128),
  (0x2e703821#32, 0xffffffffffffffffffffffffffffffff#128, 0x3fffc#128),
  (0x2e703bff#32, 0xffffffffffffffffffffffffffffffff#128, 0x3fffc#128),
  (0x2e703820#32, 0x800102037f55aafffedcba9876543210#128, 0x261d8#128),
  (0x2e703821#32, 0x800102037f55aafffedcba9876543210#128, 0x261d8#128),
  (0x2e703bff#32, 0x800102037f55aafffedcba9876543210#128, 0x261d8#128),
  (0x2e703820#32, 0x1#128, 0x1#128),
  (0x2e703821#32, 0x1#128, 0x1#128),
  (0x2e703bff#32, 0x1#128, 0x1#128),
  (0x2e703820#32, 0x80000000000000000000000000000000#128, 0x0#128),
  (0x2e703821#32, 0x80000000000000000000000000000000#128, 0x0#128),
  (0x2e703bff#32, 0x80000000000000000000000000000000#128, 0x0#128),
  (0x2e703820#32, 0xffff00008000ffff0000ffff80000000#128, 0x17fff#128),
  (0x2e703821#32, 0xffff00008000ffff0000ffff80000000#128, 0x17fff#128),
  (0x2e703bff#32, 0xffff00008000ffff0000ffff80000000#128, 0x17fff#128),
  (0x6e703820#32, 0x0#128, 0x0#128),
  (0x6e703821#32, 0x0#128, 0x0#128),
  (0x6e703bff#32, 0x0#128, 0x0#128),
  (0x6e703820#32, 0xffffffffffffffffffffffffffffffff#128, 0x7fff8#128),
  (0x6e703821#32, 0xffffffffffffffffffffffffffffffff#128, 0x7fff8#128),
  (0x6e703bff#32, 0xffffffffffffffffffffffffffffffff#128, 0x7fff8#128),
  (0x6e703820#32, 0x800102037f55aafffedcba9876543210#128, 0x40e30#128),
  (0x6e703821#32, 0x800102037f55aafffedcba9876543210#128, 0x40e30#128),
  (0x6e703bff#32, 0x800102037f55aafffedcba9876543210#128, 0x40e30#128),
  (0x6e703820#32, 0x1#128, 0x1#128),
  (0x6e703821#32, 0x1#128, 0x1#128),
  (0x6e703bff#32, 0x1#128, 0x1#128),
  (0x6e703820#32, 0x80000000000000000000000000000000#128, 0x8000#128),
  (0x6e703821#32, 0x80000000000000000000000000000000#128, 0x8000#128),
  (0x6e703bff#32, 0x80000000000000000000000000000000#128, 0x8000#128),
  (0x6e703820#32, 0xffff00008000ffff0000ffff80000000#128, 0x3fffd#128),
  (0x6e703821#32, 0xffff00008000ffff0000ffff80000000#128, 0x3fffd#128),
  (0x6e703bff#32, 0xffff00008000ffff0000ffff80000000#128, 0x3fffd#128),
  (0x6eb03820#32, 0x0#128, 0x0#128),
  (0x6eb03821#32, 0x0#128, 0x0#128),
  (0x6eb03bff#32, 0x0#128, 0x0#128),
  (0x6eb03820#32, 0xffffffffffffffffffffffffffffffff#128, 0x3fffffffc#128),
  (0x6eb03821#32, 0xffffffffffffffffffffffffffffffff#128, 0x3fffffffc#128),
  (0x6eb03bff#32, 0xffffffffffffffffffffffffffffffff#128, 0x3fffffffc#128),
  (0x6eb03820#32, 0x800102037f55aafffedcba9876543210#128, 0x2748799aa#128),
  (0x6eb03821#32, 0x800102037f55aafffedcba9876543210#128, 0x2748799aa#128),
  (0x6eb03bff#32, 0x800102037f55aafffedcba9876543210#128, 0x2748799aa#128),
  (0x6eb03820#32, 0x1#128, 0x1#128),
  (0x6eb03821#32, 0x1#128, 0x1#128),
  (0x6eb03bff#32, 0x1#128, 0x1#128),
  (0x6eb03820#32, 0x80000000000000000000000000000000#128, 0x80000000#128),
  (0x6eb03821#32, 0x80000000000000000000000000000000#128, 0x80000000#128),
  (0x6eb03bff#32, 0x80000000000000000000000000000000#128, 0x80000000#128),
  (0x6eb03820#32, 0xffff00008000ffff0000ffff80000000#128, 0x20000fffe#128),
  (0x6eb03821#32, 0xffff00008000ffff0000ffff80000000#128, 0x20000fffe#128),
  (0x6eb03bff#32, 0xffff00008000ffff0000ffff80000000#128, 0x20000fffe#128)
] : List (BitVec 32 × BitVec 128 × BitVec 128)).all
    (fun (word, input, expected) => check word input expected) = true := by native_decide

-- Reserved CNT element sizes; invalid UADDLV 2S and 1D/2D arrangements.
example : ([0x0e605820#32, 0x0ea05820#32, 0x0ee05820#32, 0x4e605820#32, 0x4ea05820#32, 0x4ee05820#32, 0x2eb03820#32, 0x2ef03820#32, 0x6ef03820#32] : List (BitVec 32)).all (fun word =>
    let s := entry word 0x12345678#128
    let t := run 1 s
    (match read_err t with | .Illegal _ => true | _ => false) &&
    read_pc t == read_pc s && read_pstate t == read_pstate s &&
    (List.range 32).all (fun n =>
      let reg := BitVec.ofNat 5 n
      read_gpr 64 reg t == read_gpr 64 reg s &&
      read_sfp 128 reg t == read_sfp 128 reg s)) = true := by native_decide

-- Previously supported REV64 remains on its original execution path.
example : check 0x4e200820#32 0x000102030405060708090a0b0c0d0e0f#128
    0x07060504030201000f0e0d0c0b0a0908#128 = true := by native_decide

end VectorReductionTest
