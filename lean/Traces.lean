/-
# Differential traces

Small circuits exercising every modelled operation, rendered with
`renderTrace`. `crates/tests/traces.rs` runs this file with
`lake env lean --run Traces.lean <dir>`, builds the same circuits with
`ark-r1cs-std`, and checks that the arkworks constraint matrices and
assignment match, so any divergence between the model and the Rust fails
`cargo test`.
-/
import ArkR1CS
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

open ArkR1CS

abbrev F17 := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

namespace Traces

def arith : CS F17 Unit := do
  let x ← FpVar.new_witness 3
  let y ← FpVar.new_witness 5
  let s := x + y
  let d := x - y
  let p ← x.mul y
  let t := (s + FpVar.Constant 7) - FpVar.Constant 2
  let u ← (FpVar.Constant 4).mul d
  let v ← (FpVar.Constant 1).mul d
  let w := d + FpVar.Constant 0
  let l := (FpVar.Constant 2 + x) + (FpVar.Constant 2 - y)
  let m ← x.mul_scalar 6
  let m0 ← x.mul_scalar 0
  let r := ((p + t) + (u + (v + w))) + (l + (m + m0))
  let z ← FpVar.new_witness r.value
  z.enforce_equal r

def field : CS F17 Unit := do
  let x ← FpVar.new_witness 3
  let d := x.double
  let n := -x
  let sq ← x.square
  let inv ← x.inverse
  let sc ← (FpVar.Constant (4 : F17)).square
  let ic ← (FpVar.Constant (4 : F17)).inverse
  let r := ((d + n) + (sq + inv)) + (sc + ic)
  let z ← FpVar.new_witness r.value
  z.enforce_equal r

def eq : CS F17 Unit := do
  let x ← FpVar.new_input 3
  let y ← FpVar.new_witness 3
  x.enforce_equal y
  x.enforce_equal (FpVar.Constant 3)
  (FpVar.Constant 3).enforce_equal y
  let _ ← x.is_eq y
  let b ← x.is_eq (FpVar.Constant 3)
  let c ← (FpVar.Constant 5).is_eq y
  let _ ← (FpVar.Constant (5 : F17)).is_eq (FpVar.Constant 5)
  let _ ← x.is_neq (FpVar.Constant 4)
  x.conditional_enforce_equal (FpVar.Constant 3) b
  x.conditional_enforce_not_equal (FpVar.Constant 4) b
  y.conditional_enforce_equal (FpVar.Constant 7) c
  y.conditional_enforce_not_equal (FpVar.Constant 3) c
  x.enforce_not_equal (FpVar.Constant 4)

/-- Boolean allocation and every constant/variable path of `&`, `|` and `!`. -/
def boolean : CS F17 Unit := do
  let x ← Boolean.new_witness true
  let y ← Boolean.new_witness false
  let _ ← x.and y
  let _ ← x.or y
  let _ ← x.and Boolean.TRUE
  let _ ← Boolean.FALSE.and y
  let _ ← x.or Boolean.FALSE
  let _ ← Boolean.TRUE.or y
  let n := x.not
  let _ ← n.or y
  pure ()

/-- `conditionally_select` on every constant/variable combination, and
`From<Boolean>`. -/
def select : CS F17 Unit := do
  let c ← Boolean.new_witness true
  let x ← FpVar.new_witness 3
  let y ← FpVar.new_witness 5
  let a ← FpVar.conditionally_select c x y
  let b ← FpVar.conditionally_select c (.Constant 7) y
  let d ← FpVar.conditionally_select c x (.Constant 9)
  let e ← FpVar.conditionally_select c (.Constant 7) (.Constant 9)
  let f ← FpVar.conditionally_select Boolean.FALSE x y
  let r := (a + b) + ((d + e) + (f + FpVar.ofBoolean c))
  let z ← FpVar.new_witness r.value
  z.enforce_equal r

/-- `to_bits_le_with_top_bits_zero`, `le_bits_to_fp` and `Sum`. -/
def bits : CS F17 Unit := do
  let x ← FpVar.new_witness 11
  let r ← x.to_bits_le_with_top_bits_zero 4
  let lo := Boolean.le_bits_to_fp (r.1.take 2)
  let hi := Boolean.le_bits_to_fp ([Boolean.TRUE] ++ r.1.drop 2)
  let k := Boolean.le_bits_to_fp [Boolean.TRUE, Boolean.FALSE, Boolean.TRUE]
  let s := FpVar.sum [lo, hi, k, .Constant 2]
  let z ← FpVar.new_witness s.value
  z.enforce_equal s

def cases : List (String × CS F17 Unit) :=
  [("arith", arith), ("field", field), ("eq", eq), ("boolean", boolean), ("select", select),
    ("bits", bits)]

def render (c : CS F17 Unit) : String :=
  renderTrace (fun x : F17 => toString x.val) (c.run Counters.new).2

end Traces

/-- Write every trace to `<dir>/<name>.trace`. -/
def main (args : List String) : IO Unit := do
  let some dir := args.head? | throw (IO.userError "usage: lean --run Traces.lean <dir>")
  for (name, c) in Traces.cases do
    IO.FS.writeFile s!"{dir}/{name}.trace" (Traces.render c)

-- Every case is satisfied by the prover's own assignment.
#eval show IO Unit from do
  for (name, c) in Traces.cases do
    unless isSatisfied (c.run Counters.new).2 do
      throw (IO.userError s!"{name} is not satisfied by the prover's assignment")
