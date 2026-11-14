/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arm.Decode
import Arm.State
import Arm.Insts.Common
import Arm.Insts.CosimM

namespace DPSFP
open BitVec

/-- Sum unsigned vector elements into a scalar twice their width (UADDLV). -/
def simd_unsigned_sum_long (esize : Nat) (operand : BitVec n) : BitVec (2 * esize) :=
  Id.run do
    let mut result := 0#(2 * esize)
    for e in [0:n / esize] do
      result := result + zeroExtend (2 * esize) (elem_get operand e esize)
    return result

@[state_simp_rules]
def exec_advanced_simd_across_lanes
    (inst : Advanced_simd_across_lanes_cls) (s : ArmState) : ArmState :=
  if inst.U = 1#1 && inst.opcode = 0b00011#5 then -- UADDLV
    if inst.size = 0b11#2 || (inst.size = 0b10#2 && inst.Q = 0#1) then
      write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
    else
      let esize := 8 <<< inst.size.toNat
      let datasize := if inst.Q = 1#1 then 128 else 64
      let result := simd_unsigned_sum_long esize (read_sfp datasize inst.Rn s)
      let s := write_sfp (2 * esize) inst.Rd result s
      write_pc (read_pc s + 4#64) s
  else
    write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s

def Advanced_simd_across_lanes_cls.uaddlv.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let size ← BitVec.rand 2 (hi := 2)
  let q ← if size = 2#2 then pure 1#1 else BitVec.rand 1
  let inst : Advanced_simd_across_lanes_cls :=
    { Q := q, U := 1#1, size := size, opcode := 0b00011#5,
      Rn := ← BitVec.rand 5, Rd := ← BitVec.rand 5 }
  pure (some inst.toBitVec32)

/-- Only the supported unsigned widening reduction is generated. -/
def Advanced_simd_across_lanes_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [Advanced_simd_across_lanes_cls.uaddlv.rand]

end DPSFP
