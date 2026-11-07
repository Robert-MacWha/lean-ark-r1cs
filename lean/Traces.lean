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

/-- Linear and multiplicative operations through the `impl_ops!` dispatch,
including the `is_one()` / `is_zero()` shortcuts. -/
def arith : CS F17 Unit := do
  let x ← FpVar.new_witness 3
  let y ← FpVar.new_witness 5
  let s := x.add y
  let d := x.sub y
  let p ← x.mul y
  let t := (s.add (.Constant 7)).sub (.Constant 2)
  let u ← (FpVar.Constant 4).mul d
  let v ← (FpVar.Constant 1).mul d
  let w := d.add (.Constant 0)
  let r := (p.add t).add (u.add (v.add w))
  let z ← FpVar.new_witness r.value
  EqGadget.enforce_equal z r

/-- `double`, `negate`, `square` and `inverse`. -/
def field : CS F17 Unit := do
  let x ← FpVar.new_witness 3
  let d := x.double
  let n := x.negate
  let sq ← x.square
  let inv ← x.inverse
  let r := (d.add n).add (sq.add inv)
  let z ← FpVar.new_witness r.value
  EqGadget.enforce_equal z r

/-- Every `EqGadget` path: `enforce_equal` on each constant/variable
combination, `is_eq` (built on `is_neq`) and `enforce_not_equal`. -/
def eq : CS F17 Unit := do
  let x ← FpVar.new_input 3
  let y ← FpVar.new_witness 3
  EqGadget.enforce_equal x y
  EqGadget.enforce_equal x (FpVar.Constant 3)
  EqGadget.enforce_equal (FpVar.Constant 3) y
  let _ ← EqGadget.is_eq (F := F17) x y
  EqGadget.enforce_not_equal x (FpVar.Constant 4)

/-- The remaining dispatch branches: constant on the left of `+` / `-`,
`Mul<F>`, constant `square` / `inverse`, `is_eq` / `is_neq` against
constants, and the conditional `EqGadget` methods with an allocated
`should_enforce` that is true (`b`) and false (`c`). -/
def dispatch : CS F17 Unit := do
  let x ← FpVar.new_witness 3
  let b ← EqGadget.is_eq (F := F17) x (FpVar.Constant 3)
  let c ← EqGadget.is_eq (F := F17) (FpVar.Constant 5) x
  let _ ← EqGadget.is_eq (F := F17) (FpVar.Constant 5) (FpVar.Constant 5)
  let _ ← EqGadget.is_neq (F := F17) x (FpVar.Constant 4)
  let s := FpVar.Constant 2 + x
  let d := FpVar.Constant 2 - x
  let m ← x.mul_scalar 6
  let m0 ← x.mul_scalar 0
  let sc ← (FpVar.Constant 4).square
  let ic ← (FpVar.Constant 4).inverse
  EqGadget.conditional_enforce_equal x (FpVar.Constant 3) b
  EqGadget.conditional_enforce_not_equal x (FpVar.Constant 4) b
  EqGadget.conditional_enforce_equal x (FpVar.Constant 7) c
  EqGadget.conditional_enforce_not_equal x (FpVar.Constant 3) c
  let r := ((s + d) + (m + m0)) + (sc + ic)
  let z ← FpVar.new_witness r.value
  EqGadget.enforce_equal z r

def cases : List (String × CS F17 Unit) :=
  [("arith", arith), ("field", field), ("eq", eq), ("dispatch", dispatch)]

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
