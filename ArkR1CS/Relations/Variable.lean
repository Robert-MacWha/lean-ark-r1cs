/-
# `ark_relations::gr1cs::Variable` and `LinearCombination`

`Variable::SymbolicLc` is not modelled: arkworks interns symbolic linear
combinations in an `lc_map` and inlines them in `finalize()`; here every
`new_lc` returns the linear combination itself, i.e. the inlined form.
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring

set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace ArkR1CS

/-- `Variable`: the constant zero, the constant one (instance variable 0),
the `i`-th instance (public input) variable, or the `i`-th witness. -/
inductive Variable
  | Zero
  | One
  | Instance (i : Nat)
  | Witness (i : Nat)
  deriving DecidableEq, Repr

/-- `instance_assignment` / `witness_assignment`. Index 0 of the instance
assignment is the constant one and is never read. -/
structure Assignment (F : Type) where
  instance_assignment : Nat → F
  witness_assignment : Nat → F

variable {F : Type}

/-- Value of a variable under an assignment. -/
def Variable.eval [Field F] (a : Assignment F) : Variable → F
  | .Zero => 0
  | .One => 1
  | .Instance i => a.instance_assignment i
  | .Witness i => a.witness_assignment i

@[simp] theorem Variable.eval_Zero [Field F] (a : Assignment F) : Variable.eval a .Zero = 0 := rfl
@[simp] theorem Variable.eval_One [Field F] (a : Assignment F) : Variable.eval a .One = 1 := rfl
@[simp] theorem Variable.eval_Instance [Field F] (a : Assignment F) (i : Nat) :
    Variable.eval a (.Instance i) = a.instance_assignment i := rfl
@[simp] theorem Variable.eval_Witness [Field F] (a : Assignment F) (i : Nat) :
    Variable.eval a (.Witness i) = a.witness_assignment i := rfl

/-- `LinearCombination<F>`: `∑ cᵢ · vᵢ`. -/
abbrev LinearCombination (F : Type) := List (F × Variable)

namespace LinearCombination

/-- `lc!()`. -/
def zero : LinearCombination F := []

/-- `Variable::into()` / `lc!() + v`. -/
def ofVar [Field F] (v : Variable) : LinearCombination F := [(1, v)]

/-- `(c, v).into()`. -/
def ofTerm (c : F) (v : Variable) : LinearCombination F := [(c, v)]

/-- `lc * c`. -/
def mulScalar [Mul F] (lc : LinearCombination F) (c : F) : LinearCombination F :=
  lc.map fun t => (t.1 * c, t.2)

/-- `lc_diff![a, b]` / `LinearCombination::diff_vars`, with symbolic LCs inlined. -/
def diff [Field F] (a b : LinearCombination F) : LinearCombination F := a ++ b.mulScalar (-1)

/-- Value under an assignment. -/
def eval [Field F] (a : Assignment F) (lc : LinearCombination F) : F :=
  (lc.map fun t => t.1 * t.2.eval a).sum

@[simp] theorem eval_nil [Field F] (a : Assignment F) : eval a ([] : LinearCombination F) = 0 := rfl

@[simp] theorem eval_cons [Field F] (a : Assignment F) (t : F × Variable) (lc : LinearCombination F) :
    eval a (t :: lc) = t.1 * t.2.eval a + eval a lc := rfl

@[simp] theorem eval_append [Field F] (a : Assignment F) (l₁ l₂ : LinearCombination F) :
    eval a (l₁ ++ l₂) = eval a l₁ + eval a l₂ := by
  simp [eval, List.map_append, List.sum_append]

@[simp] theorem eval_mulScalar [Field F] (a : Assignment F) (lc : LinearCombination F) (c : F) :
    eval a (lc.mulScalar c) = eval a lc * c := by
  induction lc with
  | nil => simp [mulScalar]
  | cons t lc ih =>
    simp only [mulScalar, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    ring

@[simp] theorem eval_zero [Field F] (a : Assignment F) : eval a (zero : LinearCombination F) = 0 := rfl

@[simp] theorem eval_ofVar [Field F] (a : Assignment F) (v : Variable) :
    eval a (ofVar v) = v.eval a := by simp [ofVar]

@[simp] theorem eval_ofTerm [Field F] (a : Assignment F) (c : F) (v : Variable) :
    eval a (ofTerm c v) = c * v.eval a := by simp [ofTerm]

@[simp] theorem eval_diff [Field F] (a : Assignment F) (l₁ l₂ : LinearCombination F) :
    eval a (diff l₁ l₂) = eval a l₁ - eval a l₂ := by
  simp [diff, sub_eq_add_neg]

end LinearCombination

end ArkR1CS
