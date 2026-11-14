/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Exec

/-! Single-register transfer regressions. Literal assembled encodings cover all
GPR sizes, signed W/X loads, D/Q SIMD, five address modes and offset extensions.
Checks include byte preservation, writeback, ZR/SP/bank identities, all other
GPR/SFP registers, NZCV, PC and the decoder's register-modification footprint.
-/
section SingleRegMemoryTest
open BitVec

private def datum : BitVec 128 := 0x0123456789abcdef80fedcba9876fe80#128
private def entry (word : BitVec 32) (index address : BitVec 64) : ArmState :=
  let s := write_gpr 64 31#5 0x1000#64 ArmState.default
  let s := write_gpr 64 0#5 0xfedcba9876543210#64 s
  let s := write_gpr 64 1#5 0x1000#64 s
  let s := write_gpr 64 2#5 index s
  let s := write_sfp 128 0#5 0x8899aabbccddeeff0011223344556677#128 s
  let s := write_pstate { n := 1#1, z := 0#1, c := 1#1, v := 0#1 } s
  let s := write_mem_bytes 16 address datum s
  set_program s [(0#64, word)]

private def frame (s t : ArmState) (gp fp : List (BitVec 5)) : Bool :=
  read_pstate t == read_pstate s && (List.range 32).all (fun n =>
    let r := BitVec.ofNat 5 n
    (gp.contains r || read_gpr 64 r t == read_gpr 64 r s) &&
    (fp.contains r || read_sfp 128 r t == read_sfp 128 r s))

private def footprint (word : BitVec 32) (regs : List RegType) : Bool :=
  match LDST.mayModifiedRegs word with | .ok found => decide (found = regs) | _ => false

private def checkLoad (word : BitVec 32) (index address : BitVec 64)
    (expected : BitVec 128) (base : BitVec 64) (wb : Bool) : Bool :=
  let s := entry word index address
  let t := run 1 s
  let rn := extractLsb' 5 5 word
  let rt := extractLsb' 0 5 word
  let vector := getLsbD word 26
  let value := if vector then read_sfp 128 rt t else zeroExtend 128 (read_gpr_zr 64 rt t)
  let changed := [rn] ++ (if !vector && rt != 31#5 then [rt] else [])
  let regs := [if vector then RegType.SFP rt else RegType.GPR rt] ++
    (if wb then [RegType.GPR rn] else [])
  value == expected && read_gpr 64 rn t == base && read_pc t == 4#64 && read_err t == .None &&
  frame s t changed (if vector then [rt] else []) && footprint word regs &&
  read_mem_bytes 16 address t == datum && read_mem (address - 1#64) t == 0#8 &&
  read_mem (address + 16#64) t == 0#8

private def checkStore (word : BitVec 32) (index address : BitVec 64)
    (expected : BitVec 128) (base : BitVec 64) (wb : Bool) : Bool :=
  let s := entry word index address
  let t := run 1 s
  let rn := extractLsb' 5 5 word
  read_mem_bytes 16 address t == expected && read_gpr 64 rn t == base &&
  read_pc t == 4#64 && read_err t == .None && frame s t [rn] [] &&
  footprint word (if wb then [RegType.GPR rn] else []) &&
  read_mem (address - 1#64) t == 0#8 && read_mem (address + 16#64) t == 0#8

private abbrev MemoryVector := BitVec 32 × BitVec 64 × BitVec 64 × BitVec 128 × BitVec 64 × Bool

example : ([
  (0x39400420#32, 0x1#64, 0x1001#64, 0x80#128, 0x1000#64, false),
  (0x385ff020#32, 0x1#64, 0xfff#64, 0x80#128, 0x1000#64, false),
  (0x385ffc20#32, 0x1#64, 0xfff#64, 0x80#128, 0xfff#64, true),
  (0x38401420#32, 0x1#64, 0x1000#64, 0x80#128, 0x1001#64, true),
  (0x38627820#32, 0x1#64, 0x1001#64, 0x80#128, 0x1000#64, false),
  (0x79400420#32, 0x1#64, 0x1002#64, 0xfe80#128, 0x1000#64, false),
  (0x785ff020#32, 0x1#64, 0xfff#64, 0xfe80#128, 0x1000#64, false),
  (0x785fec20#32, 0x1#64, 0xffe#64, 0xfe80#128, 0xffe#64, true),
  (0x78402420#32, 0x1#64, 0x1000#64, 0xfe80#128, 0x1002#64, true),
  (0x78627820#32, 0x1#64, 0x1002#64, 0xfe80#128, 0x1000#64, false),
  (0xb9400420#32, 0x1#64, 0x1004#64, 0x9876fe80#128, 0x1000#64, false),
  (0xb85ff020#32, 0x1#64, 0xfff#64, 0x9876fe80#128, 0x1000#64, false),
  (0xb85fcc20#32, 0x1#64, 0xffc#64, 0x9876fe80#128, 0xffc#64, true),
  (0xb8404420#32, 0x1#64, 0x1000#64, 0x9876fe80#128, 0x1004#64, true),
  (0xb8627820#32, 0x1#64, 0x1004#64, 0x9876fe80#128, 0x1000#64, false),
  (0xf9400420#32, 0x1#64, 0x1008#64, 0x80fedcba9876fe80#128, 0x1000#64, false),
  (0xf85ff020#32, 0x1#64, 0xfff#64, 0x80fedcba9876fe80#128, 0x1000#64, false),
  (0xf85f8c20#32, 0x1#64, 0xff8#64, 0x80fedcba9876fe80#128, 0xff8#64, true),
  (0xf8408420#32, 0x1#64, 0x1000#64, 0x80fedcba9876fe80#128, 0x1008#64, true),
  (0xf8627820#32, 0x1#64, 0x1008#64, 0x80fedcba9876fe80#128, 0x1000#64, false),
  (0x39800420#32, 0x1#64, 0x1001#64, 0xffffffffffffff80#128, 0x1000#64, false),
  (0x389ff020#32, 0x1#64, 0xfff#64, 0xffffffffffffff80#128, 0x1000#64, false),
  (0x389ffc20#32, 0x1#64, 0xfff#64, 0xffffffffffffff80#128, 0xfff#64, true),
  (0x38801420#32, 0x1#64, 0x1000#64, 0xffffffffffffff80#128, 0x1001#64, true),
  (0x38a27820#32, 0x1#64, 0x1001#64, 0xffffffffffffff80#128, 0x1000#64, false),
  (0x39c00420#32, 0x1#64, 0x1001#64, 0xffffff80#128, 0x1000#64, false),
  (0x38dff020#32, 0x1#64, 0xfff#64, 0xffffff80#128, 0x1000#64, false),
  (0x38dffc20#32, 0x1#64, 0xfff#64, 0xffffff80#128, 0xfff#64, true),
  (0x38c01420#32, 0x1#64, 0x1000#64, 0xffffff80#128, 0x1001#64, true),
  (0x38e27820#32, 0x1#64, 0x1001#64, 0xffffff80#128, 0x1000#64, false),
  (0x79800420#32, 0x1#64, 0x1002#64, 0xfffffffffffffe80#128, 0x1000#64, false),
  (0x789ff020#32, 0x1#64, 0xfff#64, 0xfffffffffffffe80#128, 0x1000#64, false),
  (0x789fec20#32, 0x1#64, 0xffe#64, 0xfffffffffffffe80#128, 0xffe#64, true),
  (0x78802420#32, 0x1#64, 0x1000#64, 0xfffffffffffffe80#128, 0x1002#64, true),
  (0x78a27820#32, 0x1#64, 0x1002#64, 0xfffffffffffffe80#128, 0x1000#64, false),
  (0x79c00420#32, 0x1#64, 0x1002#64, 0xfffffe80#128, 0x1000#64, false),
  (0x78dff020#32, 0x1#64, 0xfff#64, 0xfffffe80#128, 0x1000#64, false),
  (0x78dfec20#32, 0x1#64, 0xffe#64, 0xfffffe80#128, 0xffe#64, true),
  (0x78c02420#32, 0x1#64, 0x1000#64, 0xfffffe80#128, 0x1002#64, true),
  (0x78e27820#32, 0x1#64, 0x1002#64, 0xfffffe80#128, 0x1000#64, false),
  (0xb9800420#32, 0x1#64, 0x1004#64, 0xffffffff9876fe80#128, 0x1000#64, false),
  (0xb89ff020#32, 0x1#64, 0xfff#64, 0xffffffff9876fe80#128, 0x1000#64, false),
  (0xb89fcc20#32, 0x1#64, 0xffc#64, 0xffffffff9876fe80#128, 0xffc#64, true),
  (0xb8804420#32, 0x1#64, 0x1000#64, 0xffffffff9876fe80#128, 0x1004#64, true),
  (0xb8a27820#32, 0x1#64, 0x1004#64, 0xffffffff9876fe80#128, 0x1000#64, false),
  (0xfd400420#32, 0x1#64, 0x1008#64, 0x80fedcba9876fe80#128, 0x1000#64, false),
  (0xfc5ff020#32, 0x1#64, 0xfff#64, 0x80fedcba9876fe80#128, 0x1000#64, false),
  (0xfc5f8c20#32, 0x1#64, 0xff8#64, 0x80fedcba9876fe80#128, 0xff8#64, true),
  (0xfc408420#32, 0x1#64, 0x1000#64, 0x80fedcba9876fe80#128, 0x1008#64, true),
  (0xfc627820#32, 0x1#64, 0x1008#64, 0x80fedcba9876fe80#128, 0x1000#64, false),
  (0x3dc00420#32, 0x1#64, 0x1010#64, 0x123456789abcdef80fedcba9876fe80#128, 0x1000#64, false),
  (0x3cdff020#32, 0x1#64, 0xfff#64, 0x123456789abcdef80fedcba9876fe80#128, 0x1000#64, false),
  (0x3cdf0c20#32, 0x1#64, 0xff0#64, 0x123456789abcdef80fedcba9876fe80#128, 0xff0#64, true),
  (0x3cc10420#32, 0x1#64, 0x1000#64, 0x123456789abcdef80fedcba9876fe80#128, 0x1010#64, true),
  (0x3ce27820#32, 0x1#64, 0x1010#64, 0x123456789abcdef80fedcba9876fe80#128, 0x1000#64, false),
  (0x38a2c820#32, 0xffffffff#64, 0xfff#64, 0xffffffffffffff80#128, 0x1000#64, false),
  (0x78a25820#32, 0x100000001#64, 0x1002#64, 0xfffffffffffffe80#128, 0x1000#64, false),
  (0xb8a2f820#32, 0xffffffffffffffff#64, 0xffc#64, 0xffffffff9876fe80#128, 0x1000#64, false),
  (0x3ce2d820#32, 0xffffffff#64, 0xff0#64, 0x123456789abcdef80fedcba9876fe80#128, 0x1000#64, false),
  (0x787f6820#32, 0x1#64, 0x1000#64, 0xfe80#128, 0x1000#64, false),
  (0xf8625820#32, 0x100000001#64, 0x1008#64, 0x80fedcba9876fe80#128, 0x1000#64, false),
  (0xf940003f#32, 0x1#64, 0x1000#64, 0x0#128, 0x1000#64, false),
  (0xf8408fe0#32, 0x1#64, 0x1008#64, 0x80fedcba9876fe80#128, 0x1008#64, true),
  (0xfc408fff#32, 0x1#64, 0x1008#64, 0x80fedcba9876fe80#128, 0x1008#64, true),
  (0x3dc0003f#32, 0x1#64, 0x1000#64, 0x123456789abcdef80fedcba9876fe80#128, 0x1000#64, false),
  (0xf9400021#32, 0x1#64, 0x1000#64, 0x80fedcba9876fe80#128, 0x80fedcba9876fe80#64, false),
  (0xf8627822#32, 0x1#64, 0x1008#64, 0x80fedcba9876fe80#128, 0x1000#64, false),
  (0xb8804fe0#32, 0x1#64, 0x1004#64, 0xffffffff9876fe80#128, 0x1004#64, true)
] : List MemoryVector).all
    (fun (w, i, a, e, b, wb) => checkLoad w i a e b wb) = true := by native_decide
example : ([
  (0x39000420#32, 0x1#64, 0x1001#64, 0x123456789abcdef80fedcba9876fe10#128, 0x1000#64, false),
  (0x381ff020#32, 0x1#64, 0xfff#64, 0x123456789abcdef80fedcba9876fe10#128, 0x1000#64, false),
  (0x381ffc20#32, 0x1#64, 0xfff#64, 0x123456789abcdef80fedcba9876fe10#128, 0xfff#64, true),
  (0x38001420#32, 0x1#64, 0x1000#64, 0x123456789abcdef80fedcba9876fe10#128, 0x1001#64, true),
  (0x38227820#32, 0x1#64, 0x1001#64, 0x123456789abcdef80fedcba9876fe10#128, 0x1000#64, false),
  (0x79000420#32, 0x1#64, 0x1002#64, 0x123456789abcdef80fedcba98763210#128, 0x1000#64, false),
  (0x781ff020#32, 0x1#64, 0xfff#64, 0x123456789abcdef80fedcba98763210#128, 0x1000#64, false),
  (0x781fec20#32, 0x1#64, 0xffe#64, 0x123456789abcdef80fedcba98763210#128, 0xffe#64, true),
  (0x78002420#32, 0x1#64, 0x1000#64, 0x123456789abcdef80fedcba98763210#128, 0x1002#64, true),
  (0x78227820#32, 0x1#64, 0x1002#64, 0x123456789abcdef80fedcba98763210#128, 0x1000#64, false),
  (0xb9000420#32, 0x1#64, 0x1004#64, 0x123456789abcdef80fedcba76543210#128, 0x1000#64, false),
  (0xb81ff020#32, 0x1#64, 0xfff#64, 0x123456789abcdef80fedcba76543210#128, 0x1000#64, false),
  (0xb81fcc20#32, 0x1#64, 0xffc#64, 0x123456789abcdef80fedcba76543210#128, 0xffc#64, true),
  (0xb8004420#32, 0x1#64, 0x1000#64, 0x123456789abcdef80fedcba76543210#128, 0x1004#64, true),
  (0xb8227820#32, 0x1#64, 0x1004#64, 0x123456789abcdef80fedcba76543210#128, 0x1000#64, false),
  (0xf9000420#32, 0x1#64, 0x1008#64, 0x123456789abcdeffedcba9876543210#128, 0x1000#64, false),
  (0xf81ff020#32, 0x1#64, 0xfff#64, 0x123456789abcdeffedcba9876543210#128, 0x1000#64, false),
  (0xf81f8c20#32, 0x1#64, 0xff8#64, 0x123456789abcdeffedcba9876543210#128, 0xff8#64, true),
  (0xf8008420#32, 0x1#64, 0x1000#64, 0x123456789abcdeffedcba9876543210#128, 0x1008#64, true),
  (0xf8227820#32, 0x1#64, 0x1008#64, 0x123456789abcdeffedcba9876543210#128, 0x1000#64, false),
  (0xfd000420#32, 0x1#64, 0x1008#64, 0x123456789abcdef0011223344556677#128, 0x1000#64, false),
  (0xfc1ff020#32, 0x1#64, 0xfff#64, 0x123456789abcdef0011223344556677#128, 0x1000#64, false),
  (0xfc1f8c20#32, 0x1#64, 0xff8#64, 0x123456789abcdef0011223344556677#128, 0xff8#64, true),
  (0xfc008420#32, 0x1#64, 0x1000#64, 0x123456789abcdef0011223344556677#128, 0x1008#64, true),
  (0xfc227820#32, 0x1#64, 0x1008#64, 0x123456789abcdef0011223344556677#128, 0x1000#64, false),
  (0x3d800420#32, 0x1#64, 0x1010#64, 0x8899aabbccddeeff0011223344556677#128, 0x1000#64, false),
  (0x3c9ff020#32, 0x1#64, 0xfff#64, 0x8899aabbccddeeff0011223344556677#128, 0x1000#64, false),
  (0x3c9f0c20#32, 0x1#64, 0xff0#64, 0x8899aabbccddeeff0011223344556677#128, 0xff0#64, true),
  (0x3c810420#32, 0x1#64, 0x1000#64, 0x8899aabbccddeeff0011223344556677#128, 0x1010#64, true),
  (0x3ca27820#32, 0x1#64, 0x1010#64, 0x8899aabbccddeeff0011223344556677#128, 0x1000#64, false),
  (0xfc22d820#32, 0xffffffff#64, 0xff8#64, 0x123456789abcdef0011223344556677#128, 0x1000#64, false),
  (0x78225820#32, 0x100000001#64, 0x1002#64, 0x123456789abcdef80fedcba98763210#128, 0x1000#64, false),
  (0x3822683f#32, 0x1#64, 0x1001#64, 0x123456789abcdef80fedcba9876fe00#128, 0x1000#64, false)
] : List MemoryVector).all
    (fun (w, i, a, e, b, wb) => checkStore w i a e b wb) = true := by native_decide

private def refused (word : BitVec 32) (kind : Nat) (misaligned : Bool := false) : Bool :=
  let s := entry word 1#64 0x1000#64
  let s := if misaligned then write_gpr 64 31#5 0x1001#64 s else s
  let t := run 1 s
  let error := match read_err t with
    | .Fault _ => kind == 0 | .Illegal _ => kind == 1 | .Unimplemented _ => kind == 2 | _ => false
  error && read_pc t == 0#64 && frame s t [] [] && read_mem_bytes 16 0x1000#64 t == datum

-- Fault/illegal/unsupported paths do not advance PC or commit data/writeback.
example : refused 0xf94003e0#32 0 true = true := by native_decide
example : refused 0xf8408c21#32 1 = true := by native_decide
example : refused 0xf8622820#32 1 = true := by native_decide
example : refused 0xf9800020#32 2 = true := by native_decide

end SingleRegMemoryTest
