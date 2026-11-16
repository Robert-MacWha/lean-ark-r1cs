/-
# `ark_r1cs_std::boolean` (the parts other gadgets depend on)

Constants, `lc()`, `not`, `and`, `or`, and allocation with and without the
booleanity check.

The soundness lemmas of `not`, `and` and `or` hold for any satisfying
assignment, booleanity aside: they state the output's value as the polynomial
its constraint enforces (`1 - x`, `x * y`, `1 - (1 - x) * (1 - y)`). On inputs
that evaluate to `0` or `1` these are the boolean operations; booleanity comes
from allocation (`new_witness_sound`) or from the gadget that produced the bit.
-/
import ArkR1CS.Relations.ConstraintSystem
import Mathlib.Tactic.LinearCombination

namespace ArkR1CS

variable {F : Type}

/-- Models `ark_r1cs_std::boolean::AllocatedBool`: a variable meant to hold 0 or 1. -/
structure AllocatedBool (F : Type) where
  value : Bool
  /-- `variable` in arkworks (a `Variable`, here its inlined linear combination). -/
  lc : LinearCombination F

/-- Models `ark_r1cs_std::boolean::Boolean`: a constant bit or an allocated one. -/
inductive Boolean (F : Type)
  | Constant (b : Bool)
  | Var (v : AllocatedBool F)

namespace Boolean

/-- Models `Boolean::TRUE`. -/
def TRUE : Boolean F := Constant true
/-- Models `Boolean::FALSE`. -/
def FALSE : Boolean F := Constant false

/-- Models `GR1CSVar::value` for `Boolean`: the bit the prover assigned. -/
def value : Boolean F → Bool
  | Constant b => b
  | Var v => v.value

/-- Models `Boolean::lc`: `lc!()` for false, `One` for true, the variable otherwise. -/
def lc [Field F] : Boolean F → LinearCombination F
  | Constant false => LinearCombination.zero
  | Constant true => LinearCombination.ofVar .One
  | Var v => v.lc

/-- The value of the boolean's linear combination under an assignment. No arkworks counterpart. -/
def eval [Field F] (a : Assignment F) (b : Boolean F) : F := b.lc.eval a

/-- `TRUE` evaluates to 1. -/
@[simp, cs_eval] theorem eval_TRUE [Field F] (a : Assignment F) : eval a (TRUE : Boolean F) = 1 := by
  simp [eval, TRUE, lc]
/-- `FALSE` evaluates to 0. -/
@[simp, cs_eval] theorem eval_FALSE [Field F] (a : Assignment F) : eval a (FALSE : Boolean F) = 0 := by
  simp [eval, FALSE, lc]
/-- An allocated boolean evaluates to the value of its variable. -/
@[simp, cs_eval] theorem eval_Var [Field F] (a : Assignment F) (v : AllocatedBool F) :
    eval a (Var v) = v.lc.eval a := rfl

end Boolean

namespace AllocatedBool

/-- Models `AllocatedBool::not`: `new_lc(lc_diff![One, variable])`, i.e. `1 - v`, with no
constraint. -/
def not [Field F] (v : AllocatedBool F) : AllocatedBool F :=
  ⟨!v.value, LinearCombination.diff (LinearCombination.ofVar .One) v.lc⟩

/-- `v.not` evaluates to `1 - v`. -/
@[simp, cs_eval] theorem eval_not [Field F] (a : Assignment F) (v : AllocatedBool F) :
    v.not.lc.eval a = 1 - v.lc.eval a := by
  simp [not]

/-- Models `AllocatedBool::new_witness_without_booleanity_check`: allocates a witness holding
`b`, without enforcing that it is 0 or 1. -/
def new_witness_without_booleanity_check [Field F] (b : Bool) : CS F (AllocatedBool F) := do
  let v ← new_witness_variable (if b then (1 : F) else 0)
  pure ⟨b, LinearCombination.ofVar v⟩

/-- Returns the next witness variable and records one witness, 1 or 0. -/
@[simp, cs_run] theorem run_new_witness_without_booleanity_check [Field F] (b : Bool) (k : Counters) :
    (new_witness_without_booleanity_check b).run k =
      (⟨b, LinearCombination.ofVar (.Witness k.num_witness_variables)⟩,
        [.witness (if b then (1 : F) else 0)]) := rfl

end AllocatedBool

attribute [cs_eval] Boolean.eval

/-- Models `impl Not for Boolean` (`Boolean::not_in_place`): flips a constant, otherwise
`AllocatedBool::not`. -/
def Boolean.not [Field F] : Boolean F → Boolean F
  | .Constant b => .Constant (!b)
  | .Var v => .Var v.not

/-- `!b` evaluates to `1 - b`. -/
theorem Boolean.eval_not [Field F] (a : Assignment F) (b : Boolean F) :
    b.not.eval a = 1 - b.eval a := by
  cases b with
  | Constant b => cases b <;> simp [Boolean.not, Boolean.eval, Boolean.lc, LinearCombination.zero]
  | Var v => simp [Boolean.not, Boolean.eval, Boolean.lc]

attribute [simp, cs_eval] Boolean.eval_not

namespace AllocatedBool

variable [Field F]

/-- `AllocatedBool::and`: `self * b = result`. -/
def and (x y : AllocatedBool F) : CS F (AllocatedBool F) := do
  let result ← new_witness_without_booleanity_check (x.value && y.value)
  enforce_r1cs_constraint x.lc y.lc result.lc
  pure result

/-- `AllocatedBool::or`: `(1 - self) * (1 - b) = 1 - result`. -/
def or (x y : AllocatedBool F) : CS F (AllocatedBool F) := do
  let result ← new_witness_without_booleanity_check (x.value || y.value)
  enforce_r1cs_constraint x.not.lc y.not.lc result.not.lc
  pure result

/-- `AllocVar::new_variable` with `AllocationMode::Witness`: allocates the bit
and enforces `(1 - v) * v = 0`. -/
def new_witness (b : Bool) : CS F (AllocatedBool F) := do
  let v ← new_witness_variable (if b then (1 : F) else 0)
  enforce_r1cs_constraint (LinearCombination.diff (LinearCombination.ofVar .One)
    (LinearCombination.ofVar v)) (LinearCombination.ofVar v) LinearCombination.zero
  pure ⟨b, LinearCombination.ofVar v⟩

end AllocatedBool

namespace Boolean

variable [Field F]

/-- `Boolean::_and` (`&`). -/
def and : Boolean F → Boolean F → CS F (Boolean F)
  | Constant false, _ | _, Constant false => pure FALSE
  | Constant true, x | x, Constant true => pure x
  | Var x, Var y => do
    let r ← x.and y
    pure (Var r)

/-- `Boolean::_or` (`|`). -/
def or : Boolean F → Boolean F → CS F (Boolean F)
  | Constant false, x | x, Constant false => pure x
  | Constant true, _ | _, Constant true => pure TRUE
  | Var x, Var y => do
    let r ← x.or y
    pure (Var r)

/-- `Boolean::new_witness`. -/
def new_witness (b : Bool) : CS F (Boolean F) := do
  let v ← AllocatedBool.new_witness b
  pure (Var v)

/-- `Boolean::new_variable`: `AllocationMode::Constant` allocates nothing. -/
def new_constant (b : Bool) : Boolean F := Constant b

@[simp, cs_eval] theorem eval_Constant (a : Assignment F) (b : Bool) :
    eval a (Constant b : Boolean F) = if b then 1 else 0 := by
  cases b <;> simp [eval, lc, LinearCombination.zero]

theorem and_sound (x y : Boolean F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((x.and y).run k).2) :
    ((x.and y).run k).1.eval a = x.eval a * y.eval a := by
  rcases x with (_ | _) | x <;> rcases y with (_ | _) | y <;>
    simp [Boolean.and, FALSE, AllocatedBool.and, cs_run] at h ⊢
  exact h.symm

theorem or_sound (x y : Boolean F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((x.or y).run k).2) :
    ((x.or y).run k).1.eval a = 1 - (1 - x.eval a) * (1 - y.eval a) := by
  rcases x with (_ | _) | x <;> rcases y with (_ | _) | y <;>
    simp [Boolean.or, TRUE, AllocatedBool.or, cs_run] at h ⊢
  linear_combination h

/-- A freshly allocated witness bit is `0` or `1`. -/
theorem new_witness_sound (b : Bool) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((new_witness b).run k).2) :
    ((new_witness b).run k).1.eval a = 0 ∨ ((new_witness b).run k).1.eval a = 1 := by
  simp [new_witness, AllocatedBool.new_witness, cs_run, LinearCombination.zero] at h ⊢
  rcases h with h | h
  · exact .inr (sub_eq_zero.mp h).symm
  · exact .inl h

end Boolean

/-! ### Bits as propositions

`IsBit a b P` says the boolean `b` evaluates to 1 when `P` holds and to 0
otherwise. Restated on bits, `and` is `∧`, `or` is `∨` and `not` is `¬`, so a
circuit proof can reason in logic instead of field arithmetic. -/

section IsBit

variable [Field F] {a : Assignment F} {k : Counters}

/-- `b` evaluates to the bit of `P`. No arkworks counterpart. -/
abbrev IsBit (a : Assignment F) (b : Boolean F) (P : Prop) [Decidable P] : Prop :=
  b.eval a = if P then 1 else 0

/-- The bit of `P` is the bit of any `Q` equivalent to it. -/
theorem IsBit.congr {b : Boolean F} {P Q : Prop} [Decidable P] [Decidable Q] (hb : IsBit a b P)
    (h : P ↔ Q) : IsBit a b Q := by
  rw [IsBit, hb]; exact if_congr h rfl rfl

/-- `FALSE` is the bit of `False`. -/
theorem IsBit.false : IsBit a (Boolean.FALSE : Boolean F) False := by
  rw [IsBit, Boolean.eval_FALSE]; simp

/-- `!b` is the bit of `¬ P`. -/
theorem Boolean.not_bit {b : Boolean F} {P : Prop} [Decidable P] (hb : IsBit a b P) :
    IsBit a b.not (¬ P) := by
  rw [IsBit, Boolean.eval_not, hb]; split_ifs <;> simp_all

/-- `x & y` is the bit of `P ∧ Q`. -/
theorem Boolean.and_bit {x y : Boolean F} {P Q : Prop} [Decidable P] [Decidable Q]
    (hx : IsBit a x P) (hy : IsBit a y Q) (h : ConstraintsHold a ((x.and y).run k).2) :
    IsBit a ((x.and y).run k).1 (P ∧ Q) := by
  rw [IsBit, Boolean.and_sound x y k a h, hx, hy]; split_ifs <;> simp_all

/-- `x | y` is the bit of `P ∨ Q`. -/
theorem Boolean.or_bit {x y : Boolean F} {P Q : Prop} [Decidable P] [Decidable Q]
    (hx : IsBit a x P) (hy : IsBit a y Q) (h : ConstraintsHold a ((x.or y).run k).2) :
    IsBit a ((x.or y).run k).1 (P ∨ Q) := by
  rw [IsBit, Boolean.or_sound x y k a h, hx, hy]; split_ifs <;> simp_all

end IsBit

end ArkR1CS
