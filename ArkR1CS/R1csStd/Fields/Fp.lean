/-
# `ark_r1cs_std::fields::fp` — `AllocatedFp<F>` and `FpVar<F>`

Mirrored method by method from `ark-r1cs-std` 0.6 (`src/fields/fp/mod.rs`):

* `AllocatedFp { value, variable }`: `value: Option<F>` is modelled as always
  present (proving mode); `variable: Variable` is the inlined linear
  combination (see `ArkR1CS.Relations.Variable`).
* `FpVar::{Constant, Var}` with the `impl_ops!` dispatch for `Add`, `Sub`,
  `Mul`, the `is_one()` / `is_zero()` shortcuts, and the `EqGadget`
  implementation (including `is_neq`, which is what `is_eq` is built from).

Every operation that emits constraints has a soundness lemma stated for an
arbitrary satisfying assignment.
-/
import ArkR1CS.R1csStd.Eq
import Mathlib.Tactic.LinearCombination

-- `[DecidableEq F]` is needed by the `is_one()` / `is_zero()` shortcuts and by
-- `is_neq`; it is kept in scope for the whole file for uniformity.
set_option linter.unusedSectionVars false

namespace ArkR1CS

variable {F : Type} [Field F] [DecidableEq F]

/-- `AllocatedFp<F>`. -/
structure AllocatedFp (F : Type) where
  value : F
  /-- `variable` in arkworks (a `Variable`, here its inlined linear combination). -/
  lc : LinearCombination F
  deriving Repr

namespace AllocatedFp

/-- `AllocatedFp::new(value, variable, cs)`. -/
def new (value : F) (lc : LinearCombination F) : AllocatedFp F := ⟨value, lc⟩

/-- Value under an arbitrary assignment (ignores the cached `value`). -/
def eval (a : Assignment F) (x : AllocatedFp F) : F := x.lc.eval a

@[simp] theorem eval_new (a : Assignment F) (v : F) (lc : LinearCombination F) :
    (new v lc).eval a = lc.eval a := rfl

@[simp] theorem lc_new (v : F) (lc : LinearCombination F) : (new v lc).lc = lc := rfl

@[simp] theorem value_new (v : F) (lc : LinearCombination F) : (new v lc).value = v := rfl

/-! ### `AllocVar` -/

/-- `AllocVar::new_variable` with `AllocationMode::Constant`:
`cs.new_lc((v, Variable::One))`. -/
def new_constant (c : F) : AllocatedFp F := new c (LinearCombination.ofTerm c .One)

/-- `AllocationMode::Input`. -/
def new_input (v : F) : CS F (AllocatedFp F) := do
  let var ← new_input_variable v
  pure (new v (LinearCombination.ofVar var))

/-- `AllocationMode::Witness`. -/
def new_witness (v : F) : CS F (AllocatedFp F) := do
  let var ← new_witness_variable v
  pure (new v (LinearCombination.ofVar var))

@[simp] theorem eval_new_constant (a : Assignment F) (c : F) : (new_constant c).eval a = c := by
  simp [new_constant]

@[simp] theorem run_new_input (v : F) (k : Counters) :
    (new_input v).run k =
      (new v (LinearCombination.ofVar (.Instance k.num_instance_variables)), [.input v]) := rfl

@[simp] theorem run_new_witness (v : F) (k : Counters) :
    (new_witness v).run k =
      (new v (LinearCombination.ofVar (.Witness k.num_witness_variables)), [.witness v]) := rfl

/-! ### Linear operations (no constraints) -/

/-- `AllocatedFp::add`: `lc![self.lc, other.lc]`. -/
def add (x y : AllocatedFp F) : AllocatedFp F :=
  new (x.value + y.value) (x.lc ++ y.lc)

/-- `AllocatedFp::sub`: `lc_diff![self.lc, other.lc]`. -/
def sub (x y : AllocatedFp F) : AllocatedFp F :=
  new (x.value - y.value) (LinearCombination.diff x.lc y.lc)

/-- `AllocatedFp::add_constant`: returns `self` when `other.is_zero()`. -/
def add_constant (x : AllocatedFp F) (c : F) : AllocatedFp F :=
  if c = 0 then x else new (x.value + c) (x.lc ++ LinearCombination.ofTerm c .One)

/-- `AllocatedFp::sub_constant`: `self.add_constant(-other)`. -/
def sub_constant (x : AllocatedFp F) (c : F) : AllocatedFp F := x.add_constant (-c)

/-- `AllocatedFp::mul_constant`: returns `self` when `other.is_one()`. -/
def mul_constant (x : AllocatedFp F) (c : F) : AllocatedFp F :=
  if c = 1 then x else new (x.value * c) (x.lc.mulScalar c)

/-- `AllocatedFp::double`: `(F::ONE.double(), self.lc)`. -/
def double (x : AllocatedFp F) : AllocatedFp F :=
  new (x.value + x.value) (x.lc.mulScalar 2)

/-- `AllocatedFp::negate`: `lc!() - self.lc`. -/
def negate (x : AllocatedFp F) : AllocatedFp F :=
  new (-x.value) (LinearCombination.diff LinearCombination.zero x.lc)

@[simp] theorem eval_add (a : Assignment F) (x y : AllocatedFp F) :
    (x.add y).eval a = x.eval a + y.eval a := by simp [add, eval]

@[simp] theorem eval_sub (a : Assignment F) (x y : AllocatedFp F) :
    (x.sub y).eval a = x.eval a - y.eval a := by simp [sub, eval]

@[simp] theorem eval_add_constant (a : Assignment F) (x : AllocatedFp F) (c : F) :
    (x.add_constant c).eval a = x.eval a + c := by
  unfold add_constant
  split_ifs with h
  · simp [h]
  · simp [eval]

@[simp] theorem eval_sub_constant (a : Assignment F) (x : AllocatedFp F) (c : F) :
    (x.sub_constant c).eval a = x.eval a - c := by
  simp [sub_constant, sub_eq_add_neg]

@[simp] theorem eval_mul_constant (a : Assignment F) (x : AllocatedFp F) (c : F) :
    (x.mul_constant c).eval a = x.eval a * c := by
  unfold mul_constant
  split_ifs with h
  · simp [h]
  · simp [eval]

@[simp] theorem eval_double (a : Assignment F) (x : AllocatedFp F) :
    x.double.eval a = x.eval a + x.eval a := by
  simp [double, eval]
  ring

@[simp] theorem eval_negate (a : Assignment F) (x : AllocatedFp F) :
    x.negate.eval a = -x.eval a := by simp [negate, eval]

/-! ### Multiplicative operations (one constraint each) -/

/-- `AllocatedFp::mul`: allocates the product and enforces `self * other = product`. -/
def mul (x y : AllocatedFp F) : CS F (AllocatedFp F) := do
  let product ← new_witness (x.value * y.value)
  enforce_r1cs_constraint x.lc y.lc product.lc
  pure product

/-- `AllocatedFp::square`: `self.mul(self)`. -/
def square (x : AllocatedFp F) : CS F (AllocatedFp F) := x.mul x

/-- `AllocatedFp::inverse`: allocates `self⁻¹` and enforces `self * inverse = 1`. -/
def inverse (x : AllocatedFp F) : CS F (AllocatedFp F) := do
  let inv ← new_witness x.value⁻¹
  enforce_r1cs_constraint x.lc inv.lc (LinearCombination.ofVar .One)
  pure inv

theorem mul_sound (x y : AllocatedFp F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((x.mul y).run k).2) :
    ((x.mul y).run k).1.eval a = x.eval a * y.eval a := by
  simp only [mul, CS.run_bind, CS.run_pure, run_new_witness, run_enforce_r1cs_constraint,
    List.singleton_append, List.append_nil, constraintsHold_witness, constraintsHold_constrain,
    constraintsHold_nil, and_true, Constraint.holds] at h ⊢
  simp [eval, h]

theorem square_sound (x : AllocatedFp F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a (x.square.run k).2) :
    (x.square.run k).1.eval a = x.eval a * x.eval a :=
  mul_sound x x k a h

theorem inverse_sound (x : AllocatedFp F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a (x.inverse.run k).2) :
    x.eval a * (x.inverse.run k).1.eval a = 1 := by
  simp only [inverse, CS.run_bind, CS.run_pure, run_new_witness, run_enforce_r1cs_constraint,
    List.singleton_append, List.append_nil, constraintsHold_witness, constraintsHold_constrain,
    constraintsHold_nil, and_true, Constraint.holds] at h ⊢
  simpa [eval] using h

/-! ### Equality -/

/-- `AllocatedFp::is_neq`: two constraints,
`(self - other) * multiplier = is_not_equal` and
`(self - other) * !is_not_equal = 0`. -/
def is_neq (x y : AllocatedFp F) : CS F (Boolean F) := do
  let is_not_equal ← AllocatedBool.new_witness_without_booleanity_check (decide (x.value ≠ y.value))
  let multiplier ← new_witness_variable
    (if x.value ≠ y.value then (x.value - y.value)⁻¹ else 1)
  let difference ← new_lc (LinearCombination.diff x.lc y.lc)
  enforce_r1cs_constraint difference (LinearCombination.ofVar multiplier) (Boolean.Var is_not_equal).lc
  let is_equal := (Boolean.Var is_not_equal).not
  enforce_r1cs_constraint difference is_equal.lc LinearCombination.zero
  pure (Boolean.Var is_not_equal)

/-- `AllocatedFp::is_eq`: `self.is_neq(other).not()`. -/
def is_eq (x y : AllocatedFp F) : CS F (Boolean F) := do
  let b ← x.is_neq y
  pure b.not

/-- `AllocatedFp::conditional_enforce_equal`:
`(self - other) * should_enforce = 0`. -/
def conditional_enforce_equal (x y : AllocatedFp F) (should_enforce : Boolean F) : CS F Unit :=
  enforce_r1cs_constraint (LinearCombination.diff x.lc y.lc) should_enforce.lc
    LinearCombination.zero

/-- `AllocatedFp::conditional_enforce_not_equal`:
`(self - other) * multiplier = should_enforce`. -/
def conditional_enforce_not_equal (x y : AllocatedFp F) (should_enforce : Boolean F) :
    CS F Unit := do
  let multiplier ← new_witness (if should_enforce.value then (x.value - y.value)⁻¹ else 0)
  enforce_r1cs_constraint (LinearCombination.diff x.lc y.lc) multiplier.lc
    should_enforce.lc

/-- Soundness of `is_neq`: the returned bit is the indicator of `self ≠ other`. -/
theorem is_neq_sound (x y : AllocatedFp F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((x.is_neq y).run k).2) :
    ((x.is_neq y).run k).1.eval a = if x.eval a = y.eval a then 0 else 1 := by
  simp only [is_neq, CS.run_bind, CS.run_pure, run_new_witness_variable, run_new_lc,
    run_enforce_r1cs_constraint, AllocatedBool.run_new_witness_without_booleanity_check,
    List.singleton_append, List.append_nil, List.nil_append, constraintsHold_witness,
    constraintsHold_constrain, constraintsHold_nil, and_true, Constraint.holds, Boolean.lc,
    Boolean.not, AllocatedBool.not, LinearCombination.eval_diff, LinearCombination.eval_ofVar,
    LinearCombination.eval_zero, Variable.eval_Witness, Variable.eval_One] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  simp only [Boolean.eval, Boolean.lc, LinearCombination.eval_ofVar, Variable.eval_Witness]
  by_cases hxy : x.eval a = y.eval a
  · simp only [hxy, ↓reduceIte]
    simp only [eval] at hxy
    rw [show x.lc.eval a - y.lc.eval a = 0 from sub_eq_zero.mpr hxy, zero_mul] at h₁
    exact h₁.symm
  · simp only [hxy, ↓reduceIte]
    simp only [eval] at hxy
    have hd : x.lc.eval a - y.lc.eval a ≠ 0 := sub_ne_zero.mpr hxy
    rcases mul_eq_zero.mp h₂ with h | h
    · exact absurd h hd
    · linear_combination -h

/-- Soundness of `is_eq`: the returned bit is the indicator of `self = other`. -/
theorem is_eq_sound (x y : AllocatedFp F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((x.is_eq y).run k).2) :
    ((x.is_eq y).run k).1.eval a = if x.eval a = y.eval a then 1 else 0 := by
  simp only [is_eq, CS.run_bind, CS.run_pure, List.append_nil] at h ⊢
  have := is_neq_sound x y k a h
  have hr : ((x.is_neq y).run k).1 = Boolean.Var ⟨decide (x.value ≠ y.value),
      LinearCombination.ofVar (.Witness k.num_witness_variables)⟩ := rfl
  rw [hr] at this ⊢
  simp only [Boolean.eval, Boolean.lc, Boolean.not, AllocatedBool.not,
    LinearCombination.eval_diff, LinearCombination.eval_ofVar, Variable.eval_One,
    Variable.eval_Witness] at this ⊢
  rw [this]
  split_ifs <;> simp

theorem conditional_enforce_equal_sound (x y : AllocatedFp F) (b : Boolean F) (k : Counters)
    (a : Assignment F) (hb : b.eval a = 1)
    (h : ConstraintsHold a ((x.conditional_enforce_equal y b).run k).2) :
    x.eval a = y.eval a := by
  simp only [conditional_enforce_equal, run_enforce_r1cs_constraint, constraintsHold_constrain,
    constraintsHold_nil, and_true, Constraint.holds, LinearCombination.eval_diff,
    LinearCombination.eval_zero] at h
  rw [Boolean.eval] at hb
  rw [hb, mul_one] at h
  exact sub_eq_zero.mp h

theorem conditional_enforce_not_equal_sound (x y : AllocatedFp F) (b : Boolean F) (k : Counters)
    (a : Assignment F) (hb : b.eval a = 1)
    (h : ConstraintsHold a ((x.conditional_enforce_not_equal y b).run k).2) :
    x.eval a ≠ y.eval a := by
  simp only [conditional_enforce_not_equal, CS.run_bind, run_new_witness,
    run_enforce_r1cs_constraint, List.singleton_append, constraintsHold_witness,
    constraintsHold_constrain, constraintsHold_nil, and_true, Constraint.holds,
    LinearCombination.eval_diff] at h
  rw [Boolean.eval] at hb
  rw [hb] at h
  intro hxy
  simp only [eval] at hxy
  rw [hxy, sub_self, zero_mul] at h
  exact zero_ne_one h

end AllocatedFp

/-! ## `FpVar<F>` -/

/-- `FpVar<F>`. -/
inductive FpVar (F : Type)
  | Constant (c : F)
  | Var (v : AllocatedFp F)
  deriving Repr

namespace FpVar

/-- Value under an arbitrary assignment. -/
def eval (a : Assignment F) : FpVar F → F
  | Constant c => c
  | Var v => v.eval a

/-- `FpVar::value()`. -/
def value : FpVar F → F
  | Constant c => c
  | Var v => v.value

/-- `FpVar::is_constant()`. -/
def isConstant : FpVar F → Prop
  | Constant _ => True
  | Var _ => False

@[simp] theorem eval_Constant (a : Assignment F) (c : F) : eval a (Constant c) = c := rfl
@[simp] theorem eval_Var (a : Assignment F) (v : AllocatedFp F) : eval a (Var v) = v.eval a := rfl
omit [Field F] [DecidableEq F] in
@[simp] theorem value_Constant (c : F) : value (Constant c : FpVar F) = c := rfl
omit [Field F] [DecidableEq F] in
@[simp] theorem value_Var (v : AllocatedFp F) : value (Var v) = v.value := rfl

/-! ### Constants and allocation -/

/-- `FpVar::zero()`. -/
def zero : FpVar F := Constant 0
/-- `FpVar::one()`. -/
def one : FpVar F := Constant 1
/-- `FpVar::constant(c)` / `AllocationMode::Constant`. -/
def constant (c : F) : FpVar F := Constant c

/-- `FpVar::new_input`. -/
def new_input (v : F) : CS F (FpVar F) := do
  let x ← AllocatedFp.new_input v
  pure (Var x)

/-- `FpVar::new_witness`. -/
def new_witness (v : F) : CS F (FpVar F) := do
  let x ← AllocatedFp.new_witness v
  pure (Var x)

@[simp] theorem run_new_input (v : F) (k : Counters) :
    (new_input v).run k =
      (Var (AllocatedFp.new v (LinearCombination.ofVar (.Instance k.num_instance_variables))),
        [.input v]) := rfl

@[simp] theorem run_new_witness (v : F) (k : Counters) :
    (new_witness v).run k =
      (Var (AllocatedFp.new v (LinearCombination.ofVar (.Witness k.num_witness_variables))),
        [.witness v]) := rfl

@[simp] theorem eval_zero (a : Assignment F) : eval a (zero : FpVar F) = 0 := rfl
@[simp] theorem eval_one (a : Assignment F) : eval a (one : FpVar F) = 1 := rfl

/-! ### `impl_ops!` dispatch -/

/-- `impl Add for FpVar`. -/
def add : FpVar F → FpVar F → FpVar F
  | Constant c₁, Constant c₂ => Constant (c₁ + c₂)
  | Constant c, Var v | Var v, Constant c => Var (v.add_constant c)
  | Var v₁, Var v₂ => Var (v₁.add v₂)

/-- `impl Sub for FpVar`. -/
def sub : FpVar F → FpVar F → FpVar F
  | Constant c₁, Constant c₂ => Constant (c₁ - c₂)
  | Var v, Constant c => Var (v.sub_constant c)
  | Constant c, Var v => Var (v.sub_constant c).negate
  | Var v₁, Var v₂ => Var (v₁.sub v₂)

/-- `impl Mul for FpVar`. -/
def mul : FpVar F → FpVar F → CS F (FpVar F)
  | Constant c₁, Constant c₂ => pure (Constant (c₁ * c₂))
  | Constant c, Var v | Var v, Constant c => pure (Var (v.mul_constant c))
  | Var v₁, Var v₂ => do
    let p ← v₁.mul v₂
    pure (Var p)

/-- `impl Mul<F> for FpVar`: `if other.is_zero() { zero } else { this * Constant(other) }`. -/
def mul_scalar (x : FpVar F) (c : F) : CS F (FpVar F) :=
  if c = 0 then pure zero else x.mul (Constant c)

/-- `FieldVar::negate`. -/
def negate : FpVar F → FpVar F
  | Constant c => Constant (-c)
  | Var v => Var v.negate

/-- `FieldVar::double`. -/
def double : FpVar F → FpVar F
  | Constant c => Constant (c + c)
  | Var v => Var v.double

/-- `FieldVar::square`. -/
def square : FpVar F → CS F (FpVar F)
  | Constant c => pure (Constant (c * c))
  | Var v => do
    let p ← v.square
    pure (Var p)

@[simp] theorem eval_add (a : Assignment F) (x y : FpVar F) :
    (x.add y).eval a = x.eval a + y.eval a := by
  cases x <;> cases y <;> simp [add, add_comm]

@[simp] theorem eval_sub (a : Assignment F) (x y : FpVar F) :
    (x.sub y).eval a = x.eval a - y.eval a := by
  cases x <;> cases y <;> simp [sub]

@[simp] theorem eval_negate (a : Assignment F) (x : FpVar F) : x.negate.eval a = -x.eval a := by
  cases x <;> simp [negate]

@[simp] theorem eval_double (a : Assignment F) (x : FpVar F) :
    x.double.eval a = x.eval a + x.eval a := by
  cases x <;> simp [double]

theorem mul_sound (x y : FpVar F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((x.mul y).run k).2) :
    ((x.mul y).run k).1.eval a = x.eval a * y.eval a := by
  cases x with
  | Constant c₁ =>
    cases y with
    | Constant c₂ => simp [mul]
    | Var v => simp [mul, mul_comm]
  | Var v₁ =>
    cases y with
    | Constant c => simp [mul]
    | Var v₂ =>
      simp only [mul, CS.run_bind, CS.run_pure, List.append_nil] at h ⊢
      exact AllocatedFp.mul_sound v₁ v₂ k a h

theorem square_sound (x : FpVar F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a (x.square.run k).2) :
    (x.square.run k).1.eval a = x.eval a * x.eval a := by
  cases x with
  | Constant c => simp [square]
  | Var v =>
    simp only [square, CS.run_bind, CS.run_pure, List.append_nil] at h ⊢
    exact AllocatedFp.square_sound v k a h

theorem mul_inputCount (x y : FpVar F) (k : Counters) :
    Op.inputCount ((x.mul y).run k).2 = 0 := by
  cases x <;> cases y <;> simp [mul, AllocatedFp.mul, Op.inputCount]

/-! ### `impl EqGadget for FpVar` -/

/-- `FpVar::is_eq`. -/
def is_eq : FpVar F → FpVar F → CS F (Boolean F)
  | Constant c₁, Constant c₂ => pure (Boolean.Constant (decide (c₁ = c₂)))
  | Constant c, Var v | Var v, Constant c => (AllocatedFp.new_constant c).is_eq v
  | Var v₁, Var v₂ => v₁.is_eq v₂

/-- `FpVar::conditional_enforce_equal`. Note the `(Constant, Constant)` case
emits nothing, even if the constants differ. -/
def conditional_enforce_equal : FpVar F → FpVar F → Boolean F → CS F Unit
  | Constant _, Constant _, _ => pure ()
  | Constant c, Var v, b | Var v, Constant c, b =>
    (AllocatedFp.new_constant c).conditional_enforce_equal v b
  | Var v₁, Var v₂, b => v₁.conditional_enforce_equal v₂ b

/-- `FpVar::conditional_enforce_not_equal`. -/
def conditional_enforce_not_equal : FpVar F → FpVar F → Boolean F → CS F Unit
  | Constant _, Constant _, _ => pure ()
  | Constant c, Var v, b | Var v, Constant c, b =>
    (AllocatedFp.new_constant c).conditional_enforce_not_equal v b
  | Var v₁, Var v₂, b => v₁.conditional_enforce_not_equal v₂ b

instance : EqGadget F (FpVar F) where
  is_eq := is_eq
  conditional_enforce_equal := conditional_enforce_equal
  conditional_enforce_not_equal := conditional_enforce_not_equal

@[simp] theorem EqGadget_enforce_equal (x y : FpVar F) :
    EqGadget.enforce_equal x y = conditional_enforce_equal x y Boolean.TRUE := rfl

/-- Soundness of `enforce_equal`, except in the `(Constant, Constant)` case,
where arkworks emits no constraint at all. -/
theorem enforce_equal_sound (x y : FpVar F) (hc : ¬ (x.isConstant ∧ y.isConstant))
    (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((EqGadget.enforce_equal x y).run k).2) :
    x.eval a = y.eval a := by
  rw [EqGadget_enforce_equal] at h
  cases x with
  | Constant c₁ =>
    cases y with
    | Constant c₂ => exact absurd ⟨trivial, trivial⟩ hc
    | Var v =>
      have := AllocatedFp.conditional_enforce_equal_sound _ _ _ k a (Boolean.eval_TRUE a) h
      simpa using this
  | Var v₁ =>
    cases y with
    | Constant c =>
      have := AllocatedFp.conditional_enforce_equal_sound _ _ _ k a (Boolean.eval_TRUE a) h
      simpa using this.symm
    | Var v₂ =>
      exact AllocatedFp.conditional_enforce_equal_sound _ _ _ k a (Boolean.eval_TRUE a) h

theorem enforce_equal_inputCount (x y : FpVar F) (k : Counters) :
    Op.inputCount ((EqGadget.enforce_equal x y).run k).2 = 0 := by
  cases x <;> cases y <;>
    simp [conditional_enforce_equal, AllocatedFp.conditional_enforce_equal, Op.inputCount]

/-- Soundness of `is_eq`: the returned bit is the indicator of equality. -/
theorem is_eq_sound (x y : FpVar F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((EqGadget.is_eq (F := F) x y).run k).2) :
    (EqGadget.is_eq (F := F) x y).run k |>.1.eval a = if x.eval a = y.eval a then 1 else 0 := by
  show ((is_eq x y).run k).1.eval a = _
  cases x with
  | Constant c₁ =>
    cases y with
    | Constant c₂ =>
      simp only [is_eq, CS.run_pure, eval_Constant, Boolean.eval, Boolean.lc]
      by_cases hc : c₁ = c₂ <;> simp [hc, LinearCombination.zero]
    | Var v =>
      have := AllocatedFp.is_eq_sound (AllocatedFp.new_constant c₁) v k a h
      rw [AllocatedFp.eval_new_constant] at this
      simp only [is_eq, eval_Constant, eval_Var]
      rw [this]
      exact if_congr Iff.rfl rfl rfl
  | Var v₁ =>
    cases y with
    | Constant c =>
      have := AllocatedFp.is_eq_sound (AllocatedFp.new_constant c) v₁ k a h
      rw [AllocatedFp.eval_new_constant] at this
      simp only [is_eq, eval_Constant, eval_Var]
      rw [this]
      exact if_congr eq_comm rfl rfl
    | Var v₂ => exact AllocatedFp.is_eq_sound v₁ v₂ k a h

end FpVar

end ArkR1CS
