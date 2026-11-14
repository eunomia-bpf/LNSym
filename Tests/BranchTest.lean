/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Arm.Cfg.Cfg

/-!
Unit tests for the PC-relative immediate branches (B, BL, B.cond, CBZ/CBNZ).

The architecture computes the offset as `SignExtend(imm:'00', 64)`, i.e. the
two zero bits are appended *before* sign extension; these tests cover offsets
outside the window where shifting at the immediate's own width happens to
agree (|offset| ≥ 32 MiB for B/BL, ≥ 256 KiB for B.cond/CBZ/CBNZ), plus small
and negative offsets. See https://github.com/leanprover/LNSym/issues/250.
-/

section BranchTest

open BitVec

/-- PC after executing the single instruction `word` at PC 0 in the default
state (all registers and flags zero). -/
private def pcAfter (word : BitVec 32) : BitVec 64 :=
  read_pc (run 1 (set_program ArmState.default [(0#64, word)]))

-- B (imm26)
example : pcAfter 0x15000000#32 = 0x4000000#64 := by native_decide            -- b .+64MiB
example : pcAfter 0x14800000#32 = 0x2000000#64 := by native_decide            -- b .+32MiB
example : pcAfter 0x17000000#32 = 0xfffffffffc000000#64 := by native_decide   -- b .-64MiB
example : pcAfter 0x14000001#32 = 0x4#64 := by native_decide                  -- b .+4
example : pcAfter 0x17ffffff#32 = 0xfffffffffffffffc#64 := by native_decide   -- b .-4
-- BL (imm26): same target, and x30 gets the return address
example : pcAfter 0x95000000#32 = 0x4000000#64 := by native_decide            -- bl .+64MiB
example : read_gpr 64 30#5
    (run 1 (set_program ArmState.default [(0#64, 0x95000000#32)])) = 0x4#64 := by
  native_decide
-- B.cond (imm19); AL is always taken
example : pcAfter 0x5440000e#32 = 0x80000#64 := by native_decide              -- b.al .+512KiB
example : pcAfter 0x54c0000e#32 = 0xfffffffffff80000#64 := by native_decide   -- b.al .-512KiB
example : pcAfter 0x54ffffee#32 = 0xfffffffffffffffc#64 := by native_decide   -- b.al .-4
-- CBZ / CBNZ (imm19); x0 = 0 in the default state
example : pcAfter 0xb4400000#32 = 0x80000#64 := by native_decide              -- cbz x0, .+512KiB
example : pcAfter 0xb4c00000#32 = 0xfffffffffff80000#64 := by native_decide   -- cbz x0, .-512KiB
example : pcAfter 0xb5400000#32 = 0x4#64 := by native_decide                  -- cbnz x0 (not taken)


-- The new branch forms retain flags, SIMD, memory and effect histories.
-- CFG tests inspect predicates/edges; unresolved BR/BLR must not become RET.
private def entry (word : BitVec 32) (pc value : BitVec 64) : ArmState :=
  let s := (List.range 32).foldl (fun s n =>
    let r := BitVec.ofNat 5 n
    let s := write_gpr 64 r (0x10203040#64 + BitVec.ofNat 64 n) s
    write_sfp 128 r (0x112233445566778899aabbccddeeff00#128 + BitVec.ofNat 128 n) s) ArmState.default
  let s := write_gpr 64 0#5 value s
  let s := write_gpr 64 30#5 value s
  let s := write_gpr 64 31#5 0x123456789abcdef0#64 s
  let s := write_pstate { n := 1#1, z := 0#1, c := 1#1, v := 1#1 } s
  let s := write_mem_bytes 8 0x8000#64 0x1122334455667788#64 s
  let s := write_exclusive_state { monitor := some { physicalStart := 0x9000#64, bytes := 16 } } s
  let s := record_atomic_access
    { operation := .set, address := 0x8000#64, bytes := 1,
      oldValue := 1#64, newValue := 3#64, acquire := false, release := true } s
  let s := record_memory_access (.memory .read 0x8000#64 [0x88#8] true) s
  set_program (write_pc pc s) [(pc,word)]

private def frame (s t : ArmState) (link : Bool) : Bool :=
  read_err t == .None && read_pstate t == read_pstate s &&
  read_mem_bytes 8 0x8000#64 t == read_mem_bytes 8 0x8000#64 s && t.program == s.program &&
  read_atomic_accesses t == read_atomic_accesses s && read_exclusive_state t == read_exclusive_state s &&
  read_memory_accesses t == read_memory_accesses s && (read_memory_profile t).isNone &&
  (List.range 32).all (fun n =>
    let r := BitVec.ofNat 5 n
    read_gpr 64 r t == (if link && r == 30#5 then read_pc s + 4#64 else read_gpr 64 r s) &&
    read_sfp 128 r t == read_sfp 128 r s)

private def checkBit (word : BitVec 32) (value pc offset : BitVec 64) (taken : Bool) : Bool :=
  let s := entry word pc value
  let t := stepi_checked s
  frame s t false && read_pc t == (if taken then pc + offset else pc + 4#64) &&
  (match decode_raw_inst word with
    | some (.BR (.Test_branch inst)) =>
      inst.toBitVec32 == word &&
      (match Cfg.addArmInstToCfg pc word (.BR (.Test_branch inst)) { start_address := pc } with
        | .ok (halt, cfg) => !halt && cfg.maybe_modified_regs == #[] &&
          (match (Array.toList (α := Cfg.F_CFGentry) cfg.graph).head? with
            | some (.BrOrg origin pred, [.Seq next, .BrTgt target cond]) =>
              origin == pc && next == pc + 4#64 && target == pc + offset &&
              pred s == taken && cond s == taken
            | _ => false)
        | _ => false)
    | _ => false) && (match mayModifiedRegs word with | .ok [] => true | _ => false)

-- GNU-as encodes both forms independently for every bit position.
private def bitWords : List (BitVec 32 × BitVec 32 × BitVec 64) := [
  (0x36000040#32, 0x37000040#32, 0x1#64),
  (0x36080040#32, 0x37080040#32, 0x2#64),
  (0x36100040#32, 0x37100040#32, 0x4#64),
  (0x36180040#32, 0x37180040#32, 0x8#64),
  (0x36200040#32, 0x37200040#32, 0x10#64),
  (0x36280040#32, 0x37280040#32, 0x20#64),
  (0x36300040#32, 0x37300040#32, 0x40#64),
  (0x36380040#32, 0x37380040#32, 0x80#64),
  (0x36400040#32, 0x37400040#32, 0x100#64),
  (0x36480040#32, 0x37480040#32, 0x200#64),
  (0x36500040#32, 0x37500040#32, 0x400#64),
  (0x36580040#32, 0x37580040#32, 0x800#64),
  (0x36600040#32, 0x37600040#32, 0x1000#64),
  (0x36680040#32, 0x37680040#32, 0x2000#64),
  (0x36700040#32, 0x37700040#32, 0x4000#64),
  (0x36780040#32, 0x37780040#32, 0x8000#64),
  (0x36800040#32, 0x37800040#32, 0x10000#64),
  (0x36880040#32, 0x37880040#32, 0x20000#64),
  (0x36900040#32, 0x37900040#32, 0x40000#64),
  (0x36980040#32, 0x37980040#32, 0x80000#64),
  (0x36a00040#32, 0x37a00040#32, 0x100000#64),
  (0x36a80040#32, 0x37a80040#32, 0x200000#64),
  (0x36b00040#32, 0x37b00040#32, 0x400000#64),
  (0x36b80040#32, 0x37b80040#32, 0x800000#64),
  (0x36c00040#32, 0x37c00040#32, 0x1000000#64),
  (0x36c80040#32, 0x37c80040#32, 0x2000000#64),
  (0x36d00040#32, 0x37d00040#32, 0x4000000#64),
  (0x36d80040#32, 0x37d80040#32, 0x8000000#64),
  (0x36e00040#32, 0x37e00040#32, 0x10000000#64),
  (0x36e80040#32, 0x37e80040#32, 0x20000000#64),
  (0x36f00040#32, 0x37f00040#32, 0x40000000#64),
  (0x36f80040#32, 0x37f80040#32, 0x80000000#64),
  (0xb6000040#32, 0xb7000040#32, 0x100000000#64),
  (0xb6080040#32, 0xb7080040#32, 0x200000000#64),
  (0xb6100040#32, 0xb7100040#32, 0x400000000#64),
  (0xb6180040#32, 0xb7180040#32, 0x800000000#64),
  (0xb6200040#32, 0xb7200040#32, 0x1000000000#64),
  (0xb6280040#32, 0xb7280040#32, 0x2000000000#64),
  (0xb6300040#32, 0xb7300040#32, 0x4000000000#64),
  (0xb6380040#32, 0xb7380040#32, 0x8000000000#64),
  (0xb6400040#32, 0xb7400040#32, 0x10000000000#64),
  (0xb6480040#32, 0xb7480040#32, 0x20000000000#64),
  (0xb6500040#32, 0xb7500040#32, 0x40000000000#64),
  (0xb6580040#32, 0xb7580040#32, 0x80000000000#64),
  (0xb6600040#32, 0xb7600040#32, 0x100000000000#64),
  (0xb6680040#32, 0xb7680040#32, 0x200000000000#64),
  (0xb6700040#32, 0xb7700040#32, 0x400000000000#64),
  (0xb6780040#32, 0xb7780040#32, 0x800000000000#64),
  (0xb6800040#32, 0xb7800040#32, 0x1000000000000#64),
  (0xb6880040#32, 0xb7880040#32, 0x2000000000000#64),
  (0xb6900040#32, 0xb7900040#32, 0x4000000000000#64),
  (0xb6980040#32, 0xb7980040#32, 0x8000000000000#64),
  (0xb6a00040#32, 0xb7a00040#32, 0x10000000000000#64),
  (0xb6a80040#32, 0xb7a80040#32, 0x20000000000000#64),
  (0xb6b00040#32, 0xb7b00040#32, 0x40000000000000#64),
  (0xb6b80040#32, 0xb7b80040#32, 0x80000000000000#64),
  (0xb6c00040#32, 0xb7c00040#32, 0x100000000000000#64),
  (0xb6c80040#32, 0xb7c80040#32, 0x200000000000000#64),
  (0xb6d00040#32, 0xb7d00040#32, 0x400000000000000#64),
  (0xb6d80040#32, 0xb7d80040#32, 0x800000000000000#64),
  (0xb6e00040#32, 0xb7e00040#32, 0x1000000000000000#64),
  (0xb6e80040#32, 0xb7e80040#32, 0x2000000000000000#64),
  (0xb6f00040#32, 0xb7f00040#32, 0x4000000000000000#64),
  (0xb6f80040#32, 0xb7f80040#32, 0x8000000000000000#64)
]

example : bitWords.all (fun (zero, nonzero, mask) =>
    [0#64,0xfffffffffffffffc#64].all (fun pc =>
      checkBit zero 0#64 pc 8#64 true && checkBit zero mask pc 8#64 false &&
      checkBit zero (~~~mask) pc 8#64 true && checkBit nonzero 0#64 pc 8#64 false &&
      checkBit nonzero mask pc 8#64 true && checkBit nonzero (~~~mask) pc 8#64 false)) = true := by
  native_decide

-- Signed imm14 bounds, both widths and ZR/SP identity.
example : ([
  (0x36040000#32, 0x0#64, 0xffffffffffff8000#64, true),
  (0x36040000#32, 0x1#64, 0xffffffffffff8000#64, false),
  (0x3603ffe0#32, 0x0#64, 0x7ffc#64, true),
  (0x3603ffe0#32, 0x1#64, 0x7ffc#64, false),
  (0x37040000#32, 0x0#64, 0xffffffffffff8000#64, false),
  (0x37040000#32, 0x1#64, 0xffffffffffff8000#64, true),
  (0x3703ffe0#32, 0x0#64, 0x7ffc#64, false),
  (0x3703ffe0#32, 0x1#64, 0x7ffc#64, true),
  (0x36fc0000#32, 0x0#64, 0xffffffffffff8000#64, true),
  (0x36fc0000#32, 0x80000000#64, 0xffffffffffff8000#64, false),
  (0x36fbffe0#32, 0x0#64, 0x7ffc#64, true),
  (0x36fbffe0#32, 0x80000000#64, 0x7ffc#64, false),
  (0x37fc0000#32, 0x0#64, 0xffffffffffff8000#64, false),
  (0x37fc0000#32, 0x80000000#64, 0xffffffffffff8000#64, true),
  (0x37fbffe0#32, 0x0#64, 0x7ffc#64, false),
  (0x37fbffe0#32, 0x80000000#64, 0x7ffc#64, true),
  (0xb6040000#32, 0x0#64, 0xffffffffffff8000#64, true),
  (0xb6040000#32, 0x100000000#64, 0xffffffffffff8000#64, false),
  (0xb603ffe0#32, 0x0#64, 0x7ffc#64, true),
  (0xb603ffe0#32, 0x100000000#64, 0x7ffc#64, false),
  (0xb7040000#32, 0x0#64, 0xffffffffffff8000#64, false),
  (0xb7040000#32, 0x100000000#64, 0xffffffffffff8000#64, true),
  (0xb703ffe0#32, 0x0#64, 0x7ffc#64, false),
  (0xb703ffe0#32, 0x100000000#64, 0x7ffc#64, true),
  (0xb6fc0000#32, 0x0#64, 0xffffffffffff8000#64, true),
  (0xb6fc0000#32, 0x8000000000000000#64, 0xffffffffffff8000#64, false),
  (0xb6fbffe0#32, 0x0#64, 0x7ffc#64, true),
  (0xb6fbffe0#32, 0x8000000000000000#64, 0x7ffc#64, false),
  (0xb7fc0000#32, 0x0#64, 0xffffffffffff8000#64, false),
  (0xb7fc0000#32, 0x8000000000000000#64, 0xffffffffffff8000#64, true),
  (0xb7fbffe0#32, 0x0#64, 0x7ffc#64, false),
  (0xb7fbffe0#32, 0x8000000000000000#64, 0x7ffc#64, true),
  (0x3607ffff#32, 0xffffffffffffffff#64, 0xfffffffffffffffc#64, true),
  (0x3707ffff#32, 0xffffffffffffffff#64, 0xfffffffffffffffc#64, false),
  (0x36ffffff#32, 0xffffffffffffffff#64, 0xfffffffffffffffc#64, true),
  (0x37ffffff#32, 0xffffffffffffffff#64, 0xfffffffffffffffc#64, false),
  (0xb607ffff#32, 0xffffffffffffffff#64, 0xfffffffffffffffc#64, true),
  (0xb707ffff#32, 0xffffffffffffffff#64, 0xfffffffffffffffc#64, false),
  (0xb6ffffff#32, 0xffffffffffffffff#64, 0xfffffffffffffffc#64, true),
  (0xb7ffffff#32, 0xffffffffffffffff#64, 0xfffffffffffffffc#64, false)
] : List (BitVec 32 × BitVec 64 × BitVec 64 × Bool)).all (fun (word, value, offset, taken) =>
    checkBit word value 0x10000#64 offset taken) = true := by native_decide

private def checkIndirect (word : BitVec 32) (link ret : Bool) (pc target : BitVec 64) : Bool :=
  let s := entry word pc target
  let t := stepi_checked s
  frame s t link && read_pc t == (if extractLsb' 5 5 word == 31#5 then 0#64 else target) &&
  (match mayModifiedRegs word with
    | .ok regs => regs == (if link then [.GPR 30#5] else []) | _ => false) &&
  (match decode_raw_inst word with
    | some ai =>
      match Cfg.addArmInstToCfg pc word ai { start_address := pc } with
      | .error _ => !ret
      | .ok (halt,cfg) => ret && halt && cfg.maybe_modified_regs == #[] &&
        (match (Array.toList (α := Cfg.F_CFGentry) cfg.graph).head? with | some (.Ret p, [.Ret q]) => p == pc && q == pc | _ => false)
    | _ => false)

example : ([
  (0xd61f0000#32, false, false),
  (0xd61f03c0#32, false, false),
  (0xd61f03e0#32, false, false),
  (0xd63f0000#32, true, false),
  (0xd63f03c0#32, true, false),
  (0xd63f03e0#32, true, false),
  (0xd65f0000#32, false, true),
  (0xd65f03c0#32, false, true),
  (0xd65f03e0#32, false, true)
] : List (BitVec 32 × Bool × Bool)).all (fun (word,link,ret) =>
    [0#64,0xfffffffffffffffc#64].all (fun pc =>
      [0#64,0x8000000000000000#64,0x1003#64].all (fun target =>
        checkIndirect word link ret pc target))) = true := by native_decide

-- Unallocated, authenticated and exception-return neighbors are never plain
-- jumps. They neither change PC/LR nor receive a misleading static RET edge.
example : ([0xd67f0000#32,0xd69f03e0#32,0xd71f0800#32,0xd61f0001#32,
    0xd61e0000#32,0xd61f0400#32] : List (BitVec 32)).all (fun word =>
    let s := entry word 0x1000#64 0x2000#64
    let t := stepi_checked s
    (match read_err t with | .Unimplemented _ => true | _ => false) &&
    frame s (write_err .None t) false && read_pc t == read_pc s &&
    (match mayModifiedRegs word with | .error _ => true | _ => false) &&
    (match decode_raw_inst word with
      | some ai => match Cfg.addArmInstToCfg (read_pc s) word ai { start_address := read_pc s } with
        | .error _ => true | _ => false
      | _ => false)) = true := by native_decide

-- Existing BL also modifies LR in the static register footprint.
example : (match mayModifiedRegs 0x94000001#32 with
    | .ok regs => regs == [.GPR 30#5] | _ => false) = true := by native_decide
example : (match mayModifiedRegs 0x14000001#32 with
    | .ok [] => true | _ => false) = true := by native_decide

end BranchTest
