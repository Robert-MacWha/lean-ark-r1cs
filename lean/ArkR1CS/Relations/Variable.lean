/-
# `ark_relations::gr1cs::Variable` and `LinearCombination`

`Variable::SymbolicLc` is not modelled: arkworks interns symbolic linear
combinations in an `lc_map` and inlines them in `finalize()`; here every
`new_lc` returns the linear combination itself, i.e. the inlined form.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import ArkR1CS.Attr

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace ArkR1CS

/-- Models `ark_relations::gr1cs::Variable`. `One` is instance variable 0, `Instance i` is the
`i`-th public input and `Witness i` is the `i`-th witness. `Variable::Zero` and
`Variable::SymbolicLc` are not modelled: the gadgets here never produce `Zero`, and symbolic
linear combinations are inlined. -/
inductive Variable
  | One
  | Instance (i : Nat)
  | Witness (i : Nat)
  deriving DecidableEq, Repr

/-- Models the `instance_assignment` and `witness_assignment` vectors of
`ark_relations::gr1cs::Assignments`, as total functions. Index 0 of the instance assignment is
the constant one and is never read. -/
structure Assignment (F : Type) where
  instance_assignment : Nat → F
  witness_assignment : Nat → F

variable {F : Type}

/-- The value of a variable under an assignment. No arkworks counterpart. -/
def Variable.eval [Field F] (a : Assignment F) : Variable → F
  | .One => 1
  | .Instance i => a.instance_assignment i
  | .Witness i => a.witness_assignment i

/-- The constant `One` evaluates to 1. -/
@[simp, cs_eval] theorem Variable.eval_One [Field F] (a : Assignment F) : Variable.eval a .One = 1 := rfl
/-- An instance variable evaluates to its entry in the instance assignment. -/
@[simp, cs_eval] theorem Variable.eval_Instance [Field F] (a : Assignment F) (i : Nat) :
    Variable.eval a (.Instance i) = a.instance_assignment i := rfl
/-- A witness variable evaluates to its entry in the witness assignment. -/
@[simp, cs_eval] theorem Variable.eval_Witness [Field F] (a : Assignment F) (i : Nat) :
    Variable.eval a (.Witness i) = a.witness_assignment i := rfl

/-- Models `ark_relations::gr1cs::LinearCombination`: a list of `(coefficient, variable)` terms,
read as `∑ cᵢ · vᵢ`. -/
abbrev LinearCombination (F : Type) := List (F × Variable)

namespace LinearCombination

/-- Models `lc!()`: the empty linear combination. -/
def zero : LinearCombination F := []

/-- Models `impl From<Variable> for LinearCombination` (`lc!() + v`): the single term `1 · v`. -/
def ofVar [Field F] (v : Variable) : LinearCombination F := [(1, v)]

/-- Models `impl From<(F, Variable)> for LinearCombination`: the single term `c · v`. -/
def ofTerm (c : F) (v : Variable) : LinearCombination F := [(c, v)]

/-- Models `impl Mul<F> for LinearCombination` (`lc * c`): every coefficient times `c`. -/
def mulScalar [Mul F] (lc : LinearCombination F) (c : F) : LinearCombination F :=
  lc.map fun t => (t.1 * c, t.2)

/-- Models `lc_diff!` / `LinearCombination::diff_vars`: `a - b`, with symbolic linear
combinations inlined. -/
def diff [Field F] (a b : LinearCombination F) : LinearCombination F := a ++ b.mulScalar (-1)

/-- The value of a linear combination under an assignment. No arkworks counterpart. -/
def eval [Field F] (a : Assignment F) (lc : LinearCombination F) : F :=
  (lc.map fun t => t.1 * t.2.eval a).sum

/-- The empty linear combination evaluates to 0. -/
@[simp, cs_eval] theorem eval_nil [Field F] (a : Assignment F) : eval a ([] : LinearCombination F) = 0 := rfl

/-- Prepending the term `c · v` adds `c` times the value of `v`. -/
@[simp, cs_eval] theorem eval_cons [Field F] (a : Assignment F) (t : F × Variable) (lc : LinearCombination F) :
    eval a (t :: lc) = t.1 * t.2.eval a + eval a lc := rfl

/-- Concatenating two linear combinations adds their values. -/
@[simp, cs_eval] theorem eval_append [Field F] (a : Assignment F) (l₁ l₂ : LinearCombination F) :
    eval a (l₁ ++ l₂) = eval a l₁ + eval a l₂ := by
  simp [eval, List.map_append, List.sum_append]

/-- `lc * c` evaluates to the value of `lc` times `c`. -/
@[simp, cs_eval] theorem eval_mulScalar [Field F] (a : Assignment F) (lc : LinearCombination F) (c : F) :
    eval a (lc.mulScalar c) = eval a lc * c := by
  induction lc with
  | nil => simp [mulScalar]
  | cons t lc ih =>
    simp only [mulScalar, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    ring

/-- `lc!()` evaluates to 0. -/
@[simp, cs_eval] theorem eval_zero [Field F] (a : Assignment F) : eval a (zero : LinearCombination F) = 0 := rfl

/-- `1 · v` evaluates to the value of `v`. -/
@[simp, cs_eval] theorem eval_ofVar [Field F] (a : Assignment F) (v : Variable) :
    eval a (ofVar v) = v.eval a := by simp [ofVar]

/-- `c · v` evaluates to `c` times the value of `v`. -/
@[simp, cs_eval] theorem eval_ofTerm [Field F] (a : Assignment F) (c : F) (v : Variable) :
    eval a (ofTerm c v) = c * v.eval a := by simp [ofTerm]

/-- `a - b` evaluates to the value of `a` minus the value of `b`. -/
@[simp, cs_eval] theorem eval_diff [Field F] (a : Assignment F) (l₁ l₂ : LinearCombination F) :
    eval a (diff l₁ l₂) = eval a l₁ - eval a l₂ := by
  simp [diff, sub_eq_add_neg]

end LinearCombination

end ArkR1CS
