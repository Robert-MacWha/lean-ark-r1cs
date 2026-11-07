/-
# Differential traces

Small circuits exercising every modelled operation, rendered with
`renderTrace` into `traces/*.trace`. `tests/arkworks` builds the same circuits
with `ark-r1cs-std` and checks that the arkworks constraint matrices and
assignment match these files, so any divergence between the model and the Rust
fails either `lake build` (this file checks the committed traces) or
`cargo test`.

Regenerate the files with `TRACES_REGEN=1 lake env lean --run Traces.lean`.
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

def cases : List (String × CS F17 Unit) := [("arith", arith), ("field", field), ("eq", eq)]

def render (c : CS F17 Unit) : String :=
  renderTrace (fun x : F17 => toString x.val) (c.run Counters.new).2

end Traces

/-- Regenerate `traces/*.trace`. -/
def main : IO Unit := do
  for (name, c) in Traces.cases do
    IO.FS.writeFile s!"traces/{name}.trace" (Traces.render c)

-- The committed traces must match the model (skipped while regenerating).
#eval show IO Unit from do
  if (← IO.getEnv "TRACES_REGEN").isSome then return
  for (name, c) in Traces.cases do
    let expected ← IO.FS.readFile s!"traces/{name}.trace"
    unless expected == Traces.render c do
      throw (IO.userError
        s!"traces/{name}.trace is out of date; run `TRACES_REGEN=1 lake env lean --run Traces.lean`")
    unless isSatisfied (c.run Counters.new).2 do
      throw (IO.userError s!"{name} is not satisfied by the prover's assignment")
