/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Cfg.Cfg

section ThreadPointerTest
open BitVec

private def entry (word : BitVec 32) (pc : BitVec 64) (inputs : Option ThreadPointerInputs) : ArmState :=
  let s := (List.range 32).foldl (fun s n =>
    let r := BitVec.ofNat 5 n
    let s := write_gpr 64 r (0x1234567800000000#64 + BitVec.ofNat 64 n) s
    write_sfp 128 r (0xfedcba98765432100123456789abcdef#128 + BitVec.ofNat 128 n) s) ArmState.default
  let s := write_pstate { n := 1#1, z := 1#1, c := 0#1, v := 1#1 } s
  let s := write_mem_bytes 8 0x8000#64 0x1122334455667788#64 s
  let s := write_exclusive_state { monitor := some { physicalStart := 0x9000#64, bytes := 16 } } s
  let s := record_atomic_access
    { operation := .add, address := 0x8000#64, bytes := 1,
      oldValue := 1#64, newValue := 3#64, acquire := true, release := false } s
  let s := record_memory_access (.memory .read 0x8000#64 [0x88#8] true) s
  set_program (write_thread_pointer_inputs inputs (write_pc pc s)) [(pc,word)]

private def frame (s t : ArmState) (dst : BitVec 5) (value : Option (BitVec 64)) : Bool :=
  read_pstate t == read_pstate s && t.program == s.program &&
  read_mem_bytes 8 0x8000#64 t == 0x1122334455667788#64 &&
  read_atomic_accesses t == read_atomic_accesses s && read_exclusive_state t == read_exclusive_state s &&
  read_memory_accesses t == read_memory_accesses s && (read_memory_profile t).isNone &&
  read_thread_pointer_inputs t == read_thread_pointer_inputs s &&
  (List.range 32).all (fun n =>
    let r := BitVec.ofNat 5 n
    read_gpr 64 r t == (if r == dst && dst != 31#5 then value.getD (read_gpr 64 r s)
      else read_gpr 64 r s) && read_sfp 128 r t == read_sfp 128 r s)

private def check (word : BitVec 32) (encoding : BitVec 16) (dst : BitVec 5)
    (value pc : BitVec 64) (ci : Nat) : Bool :=
  let inputs : Option ThreadPointerInputs := match ci with
    | 0 => none
    | 1 => some { el1 := some value, el2 := some (~~~value) }
    | 2 => some { el1 := none, el2 := some (~~~value) }
    | 3 => some { el1 := some value, el2 := none }
    | 4 => some { el1 := none, el2 := none }
    | _ => some { el1 := some (~~~value), el2 := some value }
  let expected := if encoding == 0xc684#16 then
      (if ci == 0 || ci == 2 || ci == 4 then none else some (if ci == 5 then ~~~value else value))
    else (if ci == 0 || ci == 3 || ci == 4 then none else some (if ci == 5 then value else ~~~value))
  let s := entry word pc inputs
  let t := stepi_checked s
  frame s t dst expected &&
  read_pc t == (if expected.isSome then pc + 4#64 else pc) &&
  (if ci == 0 then match read_err t with | .Unimplemented _ => true | _ => false
    else read_err t == (if expected.isSome then .None else .SystemRegisterDenied encoding)) &&
  (match decode_raw_inst word with
    | some (.BR (.Read_system_register inst)) =>
      inst.toBitVec32 == word && inst.encoding == encoding && inst.Rt == dst &&
      (match Cfg.addArmInstToCfg pc word (.BR (.Read_system_register inst)) { start_address := pc } with
        | .ok (halt,cfg) => !halt &&
          cfg.maybe_modified_regs == (if dst == 31#5 then #[] else #[.GPR dst]) &&
          (match (Array.toList (α := Cfg.F_CFGentry) cfg.graph).head? with
            | some (.Seq p,[.Seq q]) => p == pc && q == pc + 4#64 | _ => false)
        | _ => false)
    | _ => false) &&
  (match mayModifiedRegs word with
    | .ok regs => regs == (if dst == 31#5 then [] else [.GPR dst]) | _ => false)

-- Exact GNU-as words and register encodings are independent fixtures.
example : ([
  (0xd538d080#32, 0xc684#16, 0#5),
  (0xd538d09e#32, 0xc684#16, 30#5),
  (0xd538d09f#32, 0xc684#16, 31#5),
  (0xd53cd040#32, 0xe682#16, 0#5),
  (0xd53cd05e#32, 0xe682#16, 30#5),
  (0xd53cd05f#32, 0xe682#16, 31#5)
] : List (BitVec 32 × BitVec 16 × BitVec 5)).all (fun (word,encoding,dst) =>
    [0#64,0xfffffffffffffffc#64].all (fun pc =>
      [0#64,1#64,0x8000000000000000#64,0xffffffffffffffff#64].all (fun value =>
        (List.range 6).all (check word encoding dst value pc)))) = true := by
  native_decide

-- Other system registers remain explicitly unsupported, even with an input
-- binding. There is no fabricated default value or destination/PC update.
example : ([
  0xd53bd040#32,
  0xd53be040#32,
  0xd53b4200#32
] : List (BitVec 32)).all (fun word =>
    let s := entry word 0#64 (some { el1 := some 42#64, el2 := some 43#64 })
    let t := stepi_checked s
    (match read_err t with | .Unimplemented _ => true | _ => false) &&
    read_pc t == 0#64 && frame s t 0#5 none &&
    (match mayModifiedRegs word with | .error _ => true | _ => false)) = true := by native_decide

-- Profiles are per-step observations, not values cached at program entry.
example : (let s := entry 0xd538d080#32 0#64 (some { el1 := some 11#64, el2 := some 22#64 })
    let s := set_program s [(0#64,0xd538d080#32),(4#64,0xd53cd05e#32),(8#64,0xd538d09f#32)]
    let s := stepi_checked s
    let s := write_thread_pointer_inputs (some { el1 := none, el2 := some 33#64 }) s
    let s := stepi_checked s
    let t := stepi_checked s
    read_gpr 64 0#5 t == 11#64 && read_gpr 64 30#5 t == 33#64 &&
    read_pc t == 8#64 && read_err t == .SystemRegisterDenied 0xc684#16 &&
    read_gpr 64 31#5 t == read_gpr 64 31#5 s && frame s t 31#5 none) = true := by native_decide

-- Ordinary instructions retain an explicit system-input binding.
example : (let s := entry 0xd503201f#32 0#64 (some { el1 := none, el2 := some 0xffffffffffffffff#64 })
    let t := stepi_checked s
    read_err t == .None && read_pc t == 4#64 && frame s t 31#5 none) = true := by native_decide

end ThreadPointerTest
