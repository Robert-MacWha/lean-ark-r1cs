/-
# Canonical constraint traces

Renders a gadget's operations in the shape of `ConstraintSystem::to_matrices()`
plus the prover's assignment, so the model can be differentially tested
against arkworks:

* columns as in arkworks: `One ↦ 0`, `Instance i ↦ i`,
  `Witness j ↦ num_instance_variables + j`; zero coefficients are dropped as
  `make_row` does;
* every row is compacted (duplicate columns merged, sorted by column);
* `instance:` lists the instance assignment without the leading one.
-/
import ArkR1CS.Relations.ConstraintSystem

namespace ArkR1CS

variable {F : Type} [Field F]

/-- Column index of a variable in arkworks' matrices. -/
def Variable.column (numInstance : Nat) : Variable → Nat
  | .One => 0
  | .Instance i => i
  | .Witness j => numInstance + j

/-- Insert into a list sorted by column. -/
def insertSorted (p : Nat × F) : List (Nat × F) → List (Nat × F)
  | [] => [p]
  | q :: rest => if p.1 ≤ q.1 then p :: q :: rest else q :: insertSorted p rest

/-- Merge a coefficient into an association list. -/
def mergeTerm [DecidableEq F] (p : Nat × F) : List (Nat × F) → List (Nat × F)
  | [] => [p]
  | q :: rest => if p.1 = q.1 then (q.1, q.2 + p.2) :: rest else q :: mergeTerm p rest

/-- Compact a linear combination the way `make_row` does. -/
def LinearCombination.canon [DecidableEq F] (numInstance : Nat) (lc : LinearCombination F) :
    List (Nat × F) :=
  let merged := lc.foldl (fun acc t => mergeTerm (t.2.column numInstance, t.1) acc) []
  let sorted := merged.foldl (fun acc p => insertSorted p acc) []
  sorted.filter fun p => decide (p.2 ≠ 0)

/-- Render a compacted linear combination as `col:coeff …`, or `-` if empty. -/
def renderLC [DecidableEq F] (showF : F → String) (numInstance : Nat) (lc : LinearCombination F) :
    String :=
  match LinearCombination.canon numInstance lc with
  | [] => "-"
  | terms => " ".intercalate (terms.map fun p => s!"{p.1}:{showF p.2}")

/-- Render rows `i: A | B | C`. -/
def renderRows [DecidableEq F] (showF : F → String) (numInstance : Nat) :
    Nat → List (Constraint F) → List String
  | _, [] => []
  | i, k :: rest =>
    s!"{i}: {renderLC showF numInstance k.a} | {renderLC showF numInstance k.b} | {renderLC showF numInstance k.c}"
      :: renderRows showF numInstance (i + 1) rest

/-- Canonical rendering of the trace of `ops`, run from a fresh constraint
system. -/
def renderTrace [DecidableEq F] (showF : F → String) (ops : List (Op F)) : String :=
  let inputs := Op.inputs ops
  let witnesses := Op.witnesses ops
  let header := s!"inputs={inputs.length} witnesses={witnesses.length} " ++
    s!"constraints={(Op.constraints ops).length}"
  let inst := "instance: " ++ " ".intercalate (inputs.map showF)
  let wit := "witness: " ++ " ".intercalate (witnesses.map showF)
  "\n".intercalate
    ([header, inst, wit] ++ renderRows showF (inputs.length + 1) 0 (Op.constraints ops)) ++ "\n"

end ArkR1CS
