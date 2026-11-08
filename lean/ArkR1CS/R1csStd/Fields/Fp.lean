/-
# `ark_r1cs_std::fields::fp` — `AllocatedFp<F>` and `FpVar<F>`

Mirrored method by method from `ark-r1cs-std` 0.6 (`src/fields/fp/mod.rs`):

* `AllocatedFp { value, variable }`: `value: Option<F>` is modelled as always
  present (proving mode); `variable: Variable` is the inlined linear
  combination (see `ArkR1CS.Relations.Variable`).
* `FpVar::{Constant, Var}` with the `impl_ops!` dispatch for `Add`, `Sub`,
  `Mul`, the `is_one()` / `is_zero()` shortcuts, and the `EqGadget`
  implementation (including `is_neq`, which is what `is_eq` is built from).
* `From<Boolean>`, `Sum`, `CondSelectGadget`, `Boolean::le_bits_to_fp` and
  `FpVar::to_bits_le_with_top_bits_zero`.

Every operation that emits constraints has a soundness lemma stated for an
arbitrary satisfying assignment.
-/
import ArkR1CS.R1csStd.Eq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

-- `[DecidableEq F]` is needed by the `is_one()` / `is_zero()` shortcuts and by
-- `is_neq`; it is kept in scope for the whole file for uniformity.
set_option linter.unusedSectionVars false

namespace ArkR1CS

/-- `PrimeField::into_bigint`, read as a natural number. Only the prover's
values depend on it (`to_bits_le_with_top_bits_zero`), never the constraints. -/
class IntoBigInt (F : Type) where
  into_bigint : F → Nat

instance (n : Nat) : IntoBigInt (ZMod n) := ⟨ZMod.val⟩

/-- The value of little-endian bits `xs`: `∑ xs[i] * 2^i`. -/
def leBitsValue {F : Type} [Field F] (xs : List F) : F := xs.foldr (fun x acc => x + 2 * acc) 0

@[simp, cs_eval] theorem leBitsValue_nil {F : Type} [Field F] : leBitsValue ([] : List F) = 0 := rfl

@[simp, cs_eval] theorem leBitsValue_cons {F : Type} [Field F] (x : F) (xs : List F) :
    leBitsValue (x :: xs) = x + 2 * leBitsValue xs := rfl

variable {F : Type} [Field F] [DecidableEq F]

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp`: an allocated field element. `value` is always
present (proving mode), and `variable` is kept as its inlined linear combination `lc`. -/
structure AllocatedFp (F : Type) where
  value : F
  /-- `variable` in arkworks (a `Variable`, here its inlined linear combination). -/
  lc : LinearCombination F
  deriving Repr

namespace AllocatedFp

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::new`. -/
def new (value : F) (lc : LinearCombination F) : AllocatedFp F := ⟨value, lc⟩

/-- The value of the variable under an arbitrary assignment (ignores the cached `value`). No
arkworks counterpart. -/
def eval (a : Assignment F) (x : AllocatedFp F) : F := x.lc.eval a

/-- `new v lc` evaluates to the value of `lc`. -/
@[simp, cs_eval] theorem eval_new (a : Assignment F) (v : F) (lc : LinearCombination F) :
    (new v lc).eval a = lc.eval a := rfl

/-- The linear combination of `new v lc` is `lc`. -/
@[simp, cs_eval] theorem lc_new (v : F) (lc : LinearCombination F) : (new v lc).lc = lc := rfl

/-! ### `AllocVar` -/

/-- Models `AllocVar::new_variable` for `ark_r1cs_std::fields::fp::AllocatedFp` with
`AllocationMode::Constant`: the term `c · One`, allocating nothing. -/
def new_constant (c : F) : AllocatedFp F := new c (LinearCombination.ofTerm c .One)

/-- Models `AllocVar::new_input` for `ark_r1cs_std::fields::fp::AllocatedFp`: allocates an
instance variable. -/
def new_input (v : F) : CS F (AllocatedFp F) := do
  let var ← new_input_variable v
  pure (new v (LinearCombination.ofVar var))

/-- Models `AllocVar::new_witness` for `ark_r1cs_std::fields::fp::AllocatedFp`: allocates a
witness variable. -/
def new_witness (v : F) : CS F (AllocatedFp F) := do
  let var ← new_witness_variable v
  pure (new v (LinearCombination.ofVar var))

/-- A constant evaluates to itself. -/
@[simp, cs_eval] theorem eval_new_constant (a : Assignment F) (c : F) : (new_constant c).eval a = c := by
  simp [new_constant]

/-- `new_input v` returns the next instance variable and records one input. -/
@[simp, cs_run] theorem run_new_input (v : F) (k : Counters) :
    (new_input v).run k =
      (new v (LinearCombination.ofVar (.Instance k.num_instance_variables)), [.input v]) := rfl

/-- `new_witness v` returns the next witness variable and records one witness. -/
@[simp, cs_run] theorem run_new_witness (v : F) (k : Counters) :
    (new_witness v).run k =
      (new v (LinearCombination.ofVar (.Witness k.num_witness_variables)), [.witness v]) := rfl

/-! ### Linear operations (no constraints) -/

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::add`: `x + y` as a linear combination, with no
constraint. -/
def add (x y : AllocatedFp F) : AllocatedFp F :=
  new (x.value + y.value) (x.lc ++ y.lc)

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::sub`: `x - y` as a linear combination, with no
constraint. -/
def sub (x y : AllocatedFp F) : AllocatedFp F :=
  new (x.value - y.value) (LinearCombination.diff x.lc y.lc)

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::add_constant`: `x + c`, returning `x`
unchanged when `c = 0`. -/
def add_constant (x : AllocatedFp F) (c : F) : AllocatedFp F :=
  if c = 0 then x else new (x.value + c) (x.lc ++ LinearCombination.ofTerm c .One)

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::sub_constant`: `x.add_constant(-c)`. -/
def sub_constant (x : AllocatedFp F) (c : F) : AllocatedFp F := x.add_constant (-c)

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::mul_constant`: `x * c`, returning `x`
unchanged when `c = 1`. -/
def mul_constant (x : AllocatedFp F) (c : F) : AllocatedFp F :=
  if c = 1 then x else new (x.value * c) (x.lc.mulScalar c)

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::double`: `2 * x`, with no constraint. -/
def double (x : AllocatedFp F) : AllocatedFp F :=
  new (x.value + x.value) (x.lc.mulScalar 2)

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::negate`: `-x`, with no constraint. -/
def negate (x : AllocatedFp F) : AllocatedFp F :=
  new (-x.value) (LinearCombination.diff LinearCombination.zero x.lc)

/-- `x.add y` evaluates to `x + y`. -/
@[simp, cs_eval] theorem eval_add (a : Assignment F) (x y : AllocatedFp F) :
    (x.add y).eval a = x.eval a + y.eval a := by simp [add, eval]

/-- `x.sub y` evaluates to `x - y`. -/
@[simp, cs_eval] theorem eval_sub (a : Assignment F) (x y : AllocatedFp F) :
    (x.sub y).eval a = x.eval a - y.eval a := by simp [sub, eval]

/-- `x.add_constant c` evaluates to `x + c`. -/
@[simp, cs_eval] theorem eval_add_constant (a : Assignment F) (x : AllocatedFp F) (c : F) :
    (x.add_constant c).eval a = x.eval a + c := by
  unfold add_constant
  split_ifs with h
  · simp [h]
  · simp [eval]

/-- `x.sub_constant c` evaluates to `x - c`. -/
@[simp, cs_eval] theorem eval_sub_constant (a : Assignment F) (x : AllocatedFp F) (c : F) :
    (x.sub_constant c).eval a = x.eval a - c := by
  simp [sub_constant, sub_eq_add_neg]

/-- `x.mul_constant c` evaluates to `x * c`. -/
@[simp, cs_eval] theorem eval_mul_constant (a : Assignment F) (x : AllocatedFp F) (c : F) :
    (x.mul_constant c).eval a = x.eval a * c := by
  unfold mul_constant
  split_ifs with h
  · simp [h]
  · simp [eval]

/-- `x.double` evaluates to `x + x`. -/
@[simp, cs_eval] theorem eval_double (a : Assignment F) (x : AllocatedFp F) :
    x.double.eval a = x.eval a + x.eval a := by
  simp [double, eval]
  ring

/-- `x.negate` evaluates to `-x`. -/
@[simp, cs_eval] theorem eval_negate (a : Assignment F) (x : AllocatedFp F) :
    x.negate.eval a = -x.eval a := by simp [negate, eval]

/-! ### Multiplicative operations (one constraint each) -/

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::mul`: allocates the product as a witness and
enforces `x * y = product`. -/
def mul (x y : AllocatedFp F) : CS F (AllocatedFp F) := do
  let product ← new_witness (x.value * y.value)
  enforce_r1cs_constraint x.lc y.lc product.lc
  pure product

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::square`: `x.mul(x)`. -/
def square (x : AllocatedFp F) : CS F (AllocatedFp F) := x.mul x

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::inverse`: allocates `x⁻¹` as a witness and
enforces `x * inverse = 1`. -/
def inverse (x : AllocatedFp F) : CS F (AllocatedFp F) := do
  let inv ← new_witness x.value⁻¹
  enforce_r1cs_constraint x.lc inv.lc (LinearCombination.ofVar .One)
  pure inv

/-- If the constraints hold, the output equals `x * y`. -/
theorem mul_sound (x y : AllocatedFp F) :
    Sound (x.mul y) fun a r => r.eval a = x.eval a * y.eval a := by
  intro k a h
  simp only [mul, cs_run] at h ⊢
  simp [eval, h]

/-- If the constraints hold, the output equals `x * x`. -/
theorem square_sound (x : AllocatedFp F) :
    Sound x.square fun a r => r.eval a = x.eval a * x.eval a :=
  mul_sound x x

/-- If the constraints hold, `x` times the output is 1 (so `x ≠ 0` and the output is `x⁻¹`). -/
theorem inverse_sound (x : AllocatedFp F) :
    Sound x.inverse fun a r => x.eval a * r.eval a = 1 := by
  intro k a h
  simp only [inverse, cs_run] at h ⊢
  simpa [eval] using h

/-! ### Equality -/

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::is_neq`: allocates the bit `x ≠ y` and a
multiplier, and enforces `(x - y) * multiplier = is_not_equal` and
`(x - y) * (1 - is_not_equal) = 0`. -/
def is_neq (x y : AllocatedFp F) : CS F (Boolean F) := do
  let is_not_equal ← AllocatedBool.new_witness_without_booleanity_check (decide (x.value ≠ y.value))
  let multiplier ← new_witness_variable
    (if x.value ≠ y.value then (x.value - y.value)⁻¹ else 1)
  let difference ← new_lc (LinearCombination.diff x.lc y.lc)
  enforce_r1cs_constraint difference (LinearCombination.ofVar multiplier) (Boolean.Var is_not_equal).lc
  let is_equal := (Boolean.Var is_not_equal).not
  enforce_r1cs_constraint difference is_equal.lc LinearCombination.zero
  pure (Boolean.Var is_not_equal)

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::is_eq`: `!x.is_neq(y)`. -/
def is_eq (x y : AllocatedFp F) : CS F (Boolean F) := do
  let b ← x.is_neq y
  pure b.not

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::conditional_enforce_equal`: enforces
`(x - y) * should_enforce = 0`. -/
def conditional_enforce_equal (x y : AllocatedFp F) (should_enforce : Boolean F) : CS F Unit :=
  enforce_r1cs_constraint (LinearCombination.diff x.lc y.lc) should_enforce.lc
    LinearCombination.zero

/-- Models `ark_r1cs_std::fields::fp::AllocatedFp::conditional_enforce_not_equal`: allocates a
multiplier and enforces `(x - y) * multiplier = should_enforce`. -/
def conditional_enforce_not_equal (x y : AllocatedFp F) (should_enforce : Boolean F) :
    CS F Unit := do
  let multiplier ← new_witness (if should_enforce.value then (x.value - y.value)⁻¹ else 0)
  enforce_r1cs_constraint (LinearCombination.diff x.lc y.lc) multiplier.lc
    should_enforce.lc

/-- If the constraints hold, the output is 0 when `x = y` and 1 otherwise. -/
theorem is_neq_sound (x y : AllocatedFp F) :
    Sound (x.is_neq y) fun a r => r.eval a = if x.eval a = y.eval a then 0 else 1 := by
  intro k a h
  simp only [is_neq, cs_run, cs_eval, Boolean.lc, Boolean.not, AllocatedBool.not] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
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

/-- If the constraints hold, the output is 1 when `x = y` and 0 otherwise. -/
theorem is_eq_sound (x y : AllocatedFp F) :
    Sound (x.is_eq y) fun a r => r.eval a = if x.eval a = y.eval a then 1 else 0 := by
  intro k a h
  simp only [is_eq, cs_run] at h ⊢
  have := is_neq_sound x y k a h
  have hr : ((x.is_neq y).run k).1 = Boolean.Var ⟨decide (x.value ≠ y.value),
      LinearCombination.ofVar (.Witness k.num_witness_variables)⟩ := rfl
  rw [hr] at this ⊢
  simp only [cs_eval, Boolean.lc, Boolean.not, AllocatedBool.not] at this ⊢
  rw [this]
  split_ifs <;> simp

/-- If the constraints hold and `should_enforce` is 1, then `x = y`. -/
theorem conditional_enforce_equal_sound (x y : AllocatedFp F) (b : Boolean F) :
    Sound (x.conditional_enforce_equal y b) fun a _ => b.eval a = 1 → x.eval a = y.eval a := by
  intro k a h hb
  simp only [conditional_enforce_equal, cs_run, cs_eval] at h
  rw [Boolean.eval] at hb
  rw [hb, mul_one] at h
  exact sub_eq_zero.mp h

/-- If the constraints hold and `should_enforce` is 1, then `x ≠ y`. -/
theorem conditional_enforce_not_equal_sound (x y : AllocatedFp F) (b : Boolean F) :
    Sound (x.conditional_enforce_not_equal y b) fun a _ => b.eval a = 1 → x.eval a ≠ y.eval a := by
  intro k a h hb
  simp only [conditional_enforce_not_equal, cs_run, cs_eval] at h
  rw [Boolean.eval] at hb
  rw [hb] at h
  intro hxy
  simp only [eval] at hxy
  rw [hxy, sub_self, zero_mul] at h
  exact zero_ne_one h

end AllocatedFp

/-! ## `FpVar<F>` -/

/-- Models `ark_r1cs_std::fields::fp::FpVar`: a constant or an allocated variable. -/
inductive FpVar (F : Type)
  | Constant (c : F)
  | Var (v : AllocatedFp F)
  deriving Repr

namespace FpVar

/-- The value under an arbitrary assignment. No arkworks counterpart. -/
def eval (a : Assignment F) : FpVar F → F
  | Constant c => c
  | Var v => v.eval a

/-- Models `GR1CSVar::value` for `ark_r1cs_std::fields::fp::FpVar`: the value the prover
assigned. -/
def value : FpVar F → F
  | Constant c => c
  | Var v => v.value

/-- Models `GR1CSVar::is_constant` for `ark_r1cs_std::fields::fp::FpVar`. -/
def isConstant : FpVar F → Prop
  | Constant _ => True
  | Var _ => False

/-- A constant evaluates to itself. -/
@[simp, cs_eval] theorem eval_Constant (a : Assignment F) (c : F) : eval a (Constant c) = c := rfl
/-- A variable evaluates to the value of its `AllocatedFp`. -/
@[simp, cs_eval] theorem eval_Var (a : Assignment F) (v : AllocatedFp F) : eval a (Var v) = v.eval a := rfl

/-! ### Constants and allocation -/

/-- Models `FieldVar::zero`: the constant 0. -/
def zero : FpVar F := Constant 0
/-- Models `FieldVar::one`: the constant 1. -/
def one : FpVar F := Constant 1

/-- Models `AllocVar::new_input` for `ark_r1cs_std::fields::fp::FpVar`: allocates an instance
variable. -/
def new_input (v : F) : CS F (FpVar F) := do
  let x ← AllocatedFp.new_input v
  pure (Var x)

/-- Models `AllocVar::new_witness` for `ark_r1cs_std::fields::fp::FpVar`: allocates a witness
variable. -/
def new_witness (v : F) : CS F (FpVar F) := do
  let x ← AllocatedFp.new_witness v
  pure (Var x)

/-- `new_input v` returns the next instance variable and records one input. -/
@[simp, cs_run] theorem run_new_input (v : F) (k : Counters) :
    (new_input v).run k =
      (Var (AllocatedFp.new v (LinearCombination.ofVar (.Instance k.num_instance_variables))),
        [.input v]) := rfl

/-- `new_witness v` returns the next witness variable and records one witness. -/
@[simp, cs_run] theorem run_new_witness (v : F) (k : Counters) :
    (new_witness v).run k =
      (Var (AllocatedFp.new v (LinearCombination.ofVar (.Witness k.num_witness_variables))),
        [.witness v]) := rfl

/-- `zero` evaluates to 0. -/
@[simp, cs_eval] theorem eval_zero (a : Assignment F) : eval a (zero : FpVar F) = 0 := rfl
/-- `one` evaluates to 1. -/
@[simp, cs_eval] theorem eval_one (a : Assignment F) : eval a (one : FpVar F) = 1 := rfl

/-! ### `impl_ops!` dispatch -/

/-- Models `impl Add for ark_r1cs_std::fields::fp::FpVar`: constant-folds, otherwise
`AllocatedFp::add` / `add_constant`. No constraint. -/
def add : FpVar F → FpVar F → FpVar F
  | Constant c₁, Constant c₂ => Constant (c₁ + c₂)
  | Constant c, Var v | Var v, Constant c => Var (v.add_constant c)
  | Var v₁, Var v₂ => Var (v₁.add v₂)

/-- Models `impl Sub for ark_r1cs_std::fields::fp::FpVar`: constant-folds, otherwise
`AllocatedFp::sub` / `sub_constant`. No constraint. -/
def sub : FpVar F → FpVar F → FpVar F
  | Constant c₁, Constant c₂ => Constant (c₁ - c₂)
  | Var v, Constant c => Var (v.sub_constant c)
  | Constant c, Var v => Var (v.sub_constant c).negate
  | Var v₁, Var v₂ => Var (v₁.sub v₂)

/-- Models `FieldVar::negate` / `impl Neg for ark_r1cs_std::fields::fp::FpVar`. No constraint. -/
def negate : FpVar F → FpVar F
  | Constant c => Constant (-c)
  | Var v => Var v.negate

/-- `x + y`, `x - y` and `-x`, as in Rust (`&x + &y`, …). Multiplication
emits a constraint, so it stays monadic (`x.mul y`). -/
instance : Add (FpVar F) := ⟨add⟩
instance : Sub (FpVar F) := ⟨sub⟩
instance : Neg (FpVar F) := ⟨negate⟩

/-- Models `impl Mul for ark_r1cs_std::fields::fp::FpVar`: constant-folds, uses `mul_constant`
when one side is constant, and otherwise `AllocatedFp::mul` (one constraint). -/
def mul : FpVar F → FpVar F → CS F (FpVar F)
  | Constant c₁, Constant c₂ => pure (Constant (c₁ * c₂))
  | Constant c, Var v | Var v, Constant c => pure (Var (v.mul_constant c))
  | Var v₁, Var v₂ => do
    let p ← v₁.mul v₂
    pure (Var p)

/-- Models `impl Mul<F> for ark_r1cs_std::fields::fp::FpVar`: zero when `c = 0`, otherwise
`x * Constant(c)`. -/
def mul_scalar (x : FpVar F) (c : F) : CS F (FpVar F) :=
  if c = 0 then pure zero else x.mul (Constant c)

/-- Models `FieldVar::double`. No constraint. -/
def double : FpVar F → FpVar F
  | Constant c => Constant (c + c)
  | Var v => Var v.double

/-- Models `FieldVar::square`: constant-folds, otherwise `AllocatedFp::square` (one constraint). -/
def square : FpVar F → CS F (FpVar F)
  | Constant c => pure (Constant (c * c))
  | Var v => do
    let p ← v.square
    pure (Var p)

/-- Models `FieldVar::inverse`: constant-folds, otherwise `AllocatedFp::inverse` (one
constraint). For `Constant 0` arkworks returns an error; the model returns `Constant 0`. -/
def inverse : FpVar F → CS F (FpVar F)
  | Constant c => pure (Constant c⁻¹)
  | Var v => do
    let inv ← v.inverse
    pure (Var inv)

/-- `x + y` evaluates to the sum of the values. -/
@[simp, cs_eval] theorem eval_hAdd (a : Assignment F) (x y : FpVar F) :
    (x + y).eval a = x.eval a + y.eval a := by
  show (add x y).eval a = _
  cases x <;> cases y <;> simp [add, add_comm]

/-- `x - y` evaluates to the difference of the values. -/
@[simp, cs_eval] theorem eval_hSub (a : Assignment F) (x y : FpVar F) :
    (x - y).eval a = x.eval a - y.eval a := by
  show (sub x y).eval a = _
  cases x <;> cases y <;> simp [sub, sub_eq_add_neg]

/-- `-x` evaluates to the negated value. -/
@[simp, cs_eval] theorem eval_neg (a : Assignment F) (x : FpVar F) : (-x).eval a = -x.eval a := by
  show (negate x).eval a = _
  cases x <;> simp [negate]

/-- `x.double` evaluates to `x + x`. -/
@[simp, cs_eval] theorem eval_double (a : Assignment F) (x : FpVar F) :
    x.double.eval a = x.eval a + x.eval a := by
  cases x <;> simp [double]

/-- If the constraints hold, the output equals `x * y`. -/
theorem mul_sound (x y : FpVar F) :
    Sound (x.mul y) fun a r => r.eval a = x.eval a * y.eval a := by
  intro k a h
  cases x with
  | Constant c₁ =>
    cases y with
    | Constant c₂ => simp [mul]
    | Var v => simp [mul, mul_comm]
  | Var v₁ =>
    cases y with
    | Constant c => simp [mul]
    | Var v₂ =>
      simp only [mul, cs_run] at h ⊢
      exact AllocatedFp.mul_sound v₁ v₂ k a h

/-- If the constraints hold, the output equals `x * x`. -/
theorem square_sound (x : FpVar F) :
    Sound x.square fun a r => r.eval a = x.eval a * x.eval a := by
  intro k a h
  cases x with
  | Constant c => simp [square]
  | Var v =>
    simp only [square, cs_run] at h ⊢
    exact AllocatedFp.square_sound v k a h

/-- If the constraints hold, the output equals `x * c`. -/
theorem mul_scalar_sound (x : FpVar F) (c : F) :
    Sound (x.mul_scalar c) fun a r => r.eval a = x.eval a * c := by
  intro k a h
  by_cases hc : c = 0
  · simp [mul_scalar, hc]
  · simp only [mul_scalar, hc, ↓reduceIte] at h ⊢
    exact mul_sound x (Constant c) k a h

/-- If the constraints hold and `x ≠ 0`, the output equals `x⁻¹`. -/
theorem inverse_sound (x : FpVar F) :
    Sound x.inverse fun a r => x.eval a ≠ 0 → r.eval a = (x.eval a)⁻¹ := by
  intro k a h hx
  cases x with
  | Constant c => simp [inverse]
  | Var v =>
    simp only [inverse, cs_run] at h ⊢
    have := AllocatedFp.inverse_sound v k a h
    simp only [eval_Var] at hx
    exact eq_inv_of_mul_eq_one_right this

/-- `x.mul y` allocates no public inputs. -/
theorem mul_inputs (x y : FpVar F) (k : Counters) : Op.inputs ((x.mul y).run k).2 = [] := by
  cases x <;> cases y <;> simp [mul, AllocatedFp.mul, cs_run]

/-! ### `impl EqGadget for FpVar` -/

/-- Models `EqGadget::is_eq` for `ark_r1cs_std::fields::fp::FpVar`: constant-folds, otherwise
`AllocatedFp::is_eq`, treating a constant side as `new_constant`. -/
def is_eq : FpVar F → FpVar F → CS F (Boolean F)
  | Constant c₁, Constant c₂ => pure (Boolean.Constant (decide (c₁ = c₂)))
  | Constant c, Var v | Var v, Constant c => (AllocatedFp.new_constant c).is_eq v
  | Var v₁, Var v₂ => v₁.is_eq v₂

/-- Models `EqGadget::conditional_enforce_equal` for `ark_r1cs_std::fields::fp::FpVar`. The
`(Constant, Constant)` case emits nothing, even if the constants differ. -/
def conditional_enforce_equal : FpVar F → FpVar F → Boolean F → CS F Unit
  | Constant _, Constant _, _ => pure ()
  | Constant c, Var v, b | Var v, Constant c, b =>
    (AllocatedFp.new_constant c).conditional_enforce_equal v b
  | Var v₁, Var v₂, b => v₁.conditional_enforce_equal v₂ b

/-- Models `EqGadget::conditional_enforce_not_equal` for `ark_r1cs_std::fields::fp::FpVar`. The
`(Constant, Constant)` case emits nothing. -/
def conditional_enforce_not_equal : FpVar F → FpVar F → Boolean F → CS F Unit
  | Constant _, Constant _, _ => pure ()
  | Constant c, Var v, b | Var v, Constant c, b =>
    (AllocatedFp.new_constant c).conditional_enforce_not_equal v b
  | Var v₁, Var v₂, b => v₁.conditional_enforce_not_equal v₂ b

instance : EqGadget F (FpVar F) where
  is_eq := is_eq
  conditional_enforce_equal := conditional_enforce_equal
  conditional_enforce_not_equal := conditional_enforce_not_equal

/-- Models `EqGadget::enforce_equal` (default method), so `x.enforce_equal y` works as in Rust. -/
abbrev enforce_equal (x y : FpVar F) : CS F Unit := EqGadget.enforce_equal x y
/-- Models `EqGadget::enforce_not_equal` (default method). -/
abbrev enforce_not_equal (x y : FpVar F) : CS F Unit := EqGadget.enforce_not_equal x y
/-- Models `EqGadget::is_neq` (default method). -/
abbrev is_neq (x y : FpVar F) : CS F (Boolean F) := EqGadget.is_neq (F := F) x y

/-- `enforce_equal` is `conditional_enforce_equal` with `Boolean::TRUE`. -/
@[simp] theorem EqGadget_enforce_equal (x y : FpVar F) :
    EqGadget.enforce_equal x y = conditional_enforce_equal x y Boolean.TRUE := rfl

/-- `enforce_not_equal` is `conditional_enforce_not_equal` with `Boolean::TRUE`. -/
@[simp] theorem EqGadget_enforce_not_equal (x y : FpVar F) :
    EqGadget.enforce_not_equal x y = conditional_enforce_not_equal x y Boolean.TRUE := rfl

/-- If the constraints hold and `should_enforce` is 1, then `x = y`. Excludes
`(Constant, Constant)`, where arkworks emits no constraint. -/
theorem conditional_enforce_equal_sound (x y : FpVar F) (b : Boolean F)
    (hc : ¬ (x.isConstant ∧ y.isConstant)) :
    Sound (conditional_enforce_equal x y b) fun a _ => b.eval a = 1 → x.eval a = y.eval a := by
  intro k a h hb
  cases x <;> cases y
  · exact absurd ⟨trivial, trivial⟩ hc
  · simpa using AllocatedFp.conditional_enforce_equal_sound _ _ _ k a h hb
  · simpa using (AllocatedFp.conditional_enforce_equal_sound _ _ _ k a h hb).symm
  · exact AllocatedFp.conditional_enforce_equal_sound _ _ _ k a h hb

/-- If the constraints hold and `should_enforce` is 1, then `x ≠ y`. Excludes
`(Constant, Constant)`. -/
theorem conditional_enforce_not_equal_sound (x y : FpVar F) (b : Boolean F)
    (hc : ¬ (x.isConstant ∧ y.isConstant)) :
    Sound (conditional_enforce_not_equal x y b) fun a _ => b.eval a = 1 → x.eval a ≠ y.eval a := by
  intro k a h hb
  cases x <;> cases y
  · exact absurd ⟨trivial, trivial⟩ hc
  · simpa using AllocatedFp.conditional_enforce_not_equal_sound _ _ _ k a h hb
  · simpa using (AllocatedFp.conditional_enforce_not_equal_sound _ _ _ k a h hb).symm
  · exact AllocatedFp.conditional_enforce_not_equal_sound _ _ _ k a h hb

/-- If the constraints hold, then `x = y`. Excludes `(Constant, Constant)`. -/
theorem enforce_equal_sound (x y : FpVar F) (hc : ¬ (x.isConstant ∧ y.isConstant)) :
    Sound (EqGadget.enforce_equal x y) fun a _ => x.eval a = y.eval a :=
  fun k a h => conditional_enforce_equal_sound x y _ hc k a h (Boolean.eval_TRUE a)

/-- If the constraints hold, then `x ≠ y`. Excludes `(Constant, Constant)`. -/
theorem enforce_not_equal_sound (x y : FpVar F) (hc : ¬ (x.isConstant ∧ y.isConstant)) :
    Sound (EqGadget.enforce_not_equal x y) fun a _ => x.eval a ≠ y.eval a :=
  fun k a h => conditional_enforce_not_equal_sound x y _ hc k a h (Boolean.eval_TRUE a)

/-- `x.enforce_equal y` allocates no public inputs. -/
theorem enforce_equal_inputs (x y : FpVar F) (k : Counters) :
    Op.inputs ((EqGadget.enforce_equal x y).run k).2 = [] := by
  cases x <;> cases y <;>
    simp [conditional_enforce_equal, AllocatedFp.conditional_enforce_equal, cs_run]

/-- If the constraints hold, the output is 1 when `x = y` and 0 otherwise. -/
theorem is_eq_sound (x y : FpVar F) :
    Sound (EqGadget.is_eq (F := F) x y) fun a r =>
      r.eval a = if x.eval a = y.eval a then 1 else 0 := by
  intro k a h
  show ((is_eq x y).run k).1.eval a = _
  cases x with
  | Constant c₁ =>
    cases y with
    | Constant c₂ =>
      simp only [is_eq, cs_run, cs_eval, Boolean.lc]
      by_cases hc : c₁ = c₂ <;> simp [hc, LinearCombination.zero]
    | Var v =>
      have := AllocatedFp.is_eq_sound (AllocatedFp.new_constant c₁) v k a h
      beta_reduce at this
      rw [AllocatedFp.eval_new_constant] at this
      simp only [is_eq, eval_Constant, eval_Var]
      rw [this]
      exact if_congr Iff.rfl rfl rfl
  | Var v₁ =>
    cases y with
    | Constant c =>
      have := AllocatedFp.is_eq_sound (AllocatedFp.new_constant c) v₁ k a h
      beta_reduce at this
      rw [AllocatedFp.eval_new_constant] at this
      simp only [is_eq, eval_Constant, eval_Var]
      rw [this]
      exact if_congr eq_comm rfl rfl
    | Var v₂ => exact AllocatedFp.is_eq_sound v₁ v₂ k a h

/-- If the constraints hold, the output is 0 when `x = y` and 1 otherwise. -/
theorem is_neq_sound (x y : FpVar F) :
    Sound (EqGadget.is_neq (F := F) x y) fun a r =>
      r.eval a = if x.eval a = y.eval a then 0 else 1 := by
  intro k a h
  simp only [EqGadget.is_neq, cs_run] at h ⊢
  rw [Boolean.eval_not, is_eq_sound x y k a h]
  split_ifs <;> simp

/-! ### Conversion from `Boolean`, sums, selection -/

/-- `impl From<Boolean<F>> for FpVar<F>`. -/
def ofBoolean : Boolean F → FpVar F
  | .Constant b => Constant (if b then 1 else 0)
  | .Var v => Var (AllocatedFp.new (if v.value then 1 else 0) v.lc)

@[simp, cs_eval] theorem eval_ofBoolean (a : Assignment F) (b : Boolean F) :
    (ofBoolean b).eval a = b.eval a := by
  cases b <;> simp [ofBoolean, AllocatedFp.eval]

/-- `impl Mul<F> for FpVar`: zero when `other.is_zero()`, otherwise
`self * FpVar::Constant(other)`, which emits no constraints. -/
def mul_by_constant (x : FpVar F) (c : F) : FpVar F :=
  if c = 0 then zero else
    match x with
    | Constant c' => Constant (c' * c)
    | Var v => Var (v.mul_constant c)

@[simp, cs_eval] theorem eval_mul_by_constant (a : Assignment F) (x : FpVar F) (c : F) :
    (x.mul_by_constant c).eval a = x.eval a * c := by
  unfold mul_by_constant
  split_ifs with h
  · simp [h]
  · cases x <;> simp

/-- `AllocatedFp::add_many` on a non-empty list: one linear combination, no
constraints. -/
def _root_.ArkR1CS.AllocatedFp.add_many (xs : List (AllocatedFp F)) : AllocatedFp F :=
  AllocatedFp.new (xs.map (·.value)).sum (xs.flatMap (·.lc))

theorem _root_.ArkR1CS.AllocatedFp.eval_add_many (a : Assignment F) (xs : List (AllocatedFp F)) :
    (AllocatedFp.add_many xs).eval a = (xs.map (·.eval a)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [AllocatedFp.add_many, AllocatedFp.eval_new, List.flatMap_cons,
      LinearCombination.eval_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; rfl

/-- The constant part of a sum. -/
def constPart : FpVar F → F
  | Constant c => c
  | Var _ => 0

/-- The variable part of a sum. -/
def varPart : FpVar F → Option (AllocatedFp F)
  | Constant _ => none
  | Var v => some v

/-- `impl Sum for FpVar`: the constants are added up apart, and the variables
joined by `AllocatedFp::add_many`. -/
def sum (xs : List (FpVar F)) : FpVar F :=
  match xs.filterMap varPart with
  | [] => Constant (xs.map constPart).sum
  | vs => (Var (AllocatedFp.add_many vs)).add (Constant (xs.map constPart).sum)

@[simp, cs_eval] theorem eval_sum (a : Assignment F) (xs : List (FpVar F)) :
    (sum xs).eval a = (xs.map (·.eval a)).sum := by
  have split : (xs.map (·.eval a)).sum =
      ((xs.filterMap varPart).map (·.eval a)).sum + (xs.map constPart).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      cases x <;> simp [varPart, constPart, List.filterMap_cons, ih] <;> ring
  rw [split, sum]
  split
  · next h => simp [h]
  · simp [AllocatedFp.eval_add_many]

/-- `AllocatedFp::conditionally_select`: allocates the result and enforces
`cond * (true_val - false_val) = result - false_val`. -/
def _root_.ArkR1CS.AllocatedFp.conditionally_select (cond : Boolean F)
    (t f : AllocatedFp F) : CS F (AllocatedFp F) :=
  match cond with
  | .Constant true => pure t
  | .Constant false => pure f
  | .Var _ => do
    let result ← AllocatedFp.new_witness (if cond.value then t.value else f.value)
    enforce_r1cs_constraint cond.lc (LinearCombination.diff t.lc f.lc)
      (LinearCombination.diff result.lc f.lc)
    pure result

/-- `AllocatedFp::from(Boolean)`. -/
def _root_.ArkR1CS.AllocatedFp.ofBoolean (b : Boolean F) : AllocatedFp F :=
  AllocatedFp.new (if b.value then 1 else 0) b.lc

/-- An `FpVar` as an `AllocatedFp`, constants through `AllocatedFp::new_constant`. -/
def toAllocated : FpVar F → AllocatedFp F
  | Constant c => AllocatedFp.new_constant c
  | Var v => v

@[simp, cs_eval] theorem eval_toAllocated (a : Assignment F) (x : FpVar F) :
    x.toAllocated.eval a = x.eval a := by
  cases x <;> simp [toAllocated]

/-- `FpVar::conditionally_select` (what `Boolean::select` calls). -/
def conditionally_select (cond : Boolean F) (t f : FpVar F) : CS F (FpVar F) :=
  match cond, t, f with
  | .Constant true, t, _ => pure t
  | .Constant false, _, f => pure f
  | cond, Constant ct, Constant cf =>
    let is := AllocatedFp.ofBoolean cond
    let not := AllocatedFp.ofBoolean cond.not
    pure (Var ((is.mul_constant ct).add (not.mul_constant cf)))
  | cond, t, f => do
    let r ← AllocatedFp.conditionally_select cond t.toAllocated f.toAllocated
    pure (Var r)

theorem _root_.ArkR1CS.AllocatedFp.eval_ofBoolean (a : Assignment F) (b : Boolean F) :
    (AllocatedFp.ofBoolean b).eval a = b.eval a := rfl

theorem _root_.ArkR1CS.AllocatedFp.conditionally_select_sound (c : AllocatedBool F)
    (t f : AllocatedFp F) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((AllocatedFp.conditionally_select (.Var c) t f).run k).2) :
    ((AllocatedFp.conditionally_select (.Var c) t f).run k).1.eval a =
      f.eval a + c.lc.eval a * (t.eval a - f.eval a) := by
  simp only [AllocatedFp.conditionally_select, cs_run] at h ⊢
  simp only [AllocatedFp.eval, Boolean.lc, cs_eval] at h ⊢
  linear_combination -h

/-- Soundness of `conditionally_select`: `false_val + cond * (true_val - false_val)`,
which is `true_val` or `false_val` when `cond` is a bit. -/
theorem conditionally_select_sound (cond : Boolean F) (t f : FpVar F) (k : Counters)
    (a : Assignment F) (h : ConstraintsHold a ((conditionally_select cond t f).run k).2) :
    ((conditionally_select cond t f).run k).1.eval a =
      f.eval a + cond.eval a * (t.eval a - f.eval a) := by
  rcases cond with (_ | _) | c
  · simp [conditionally_select]
  · simp [conditionally_select]
  · have key := fun t f => AllocatedFp.conditionally_select_sound c t f k a
    cases t <;> cases f <;> simp only [conditionally_select, cs_run] at h key ⊢
    · simp [AllocatedFp.eval_ofBoolean]; ring
    all_goals rw [eval_Var, key _ _ h]; simp

/-! ### Bits -/

/-- `Boolean::is_constant()`. -/
def _root_.ArkR1CS.Boolean.is_constant : Boolean F → Bool
  | .Constant _ => true
  | .Var _ => false

/-- The summands of `Boolean::le_bits_to_fp`: each bit times its power of two,
the power doubled in place after each bit. -/
def le_bits_terms : F → List (Boolean F) → List (FpVar F)
  | _, [] => []
  | power, b :: bs => (ofBoolean b).mul_by_constant power :: le_bits_terms (power + power) bs

/-- `Boolean::le_bits_to_fp`, for fewer bits than `F::MODULUS_BIT_SIZE` (so
without `enforce_in_field_le`): no constraints. -/
def _root_.ArkR1CS.Boolean.le_bits_to_fp (bits : List (Boolean F)) : FpVar F :=
  if bits.all Boolean.is_constant then
    Constant (leBitsValue (bits.map fun b => if b.value then 1 else 0))
  else
    sum (le_bits_terms 1 bits)

theorem eval_le_bits_terms (a : Assignment F) (power : F) (bits : List (Boolean F)) :
    ((le_bits_terms power bits).map (·.eval a)).sum = power * leBitsValue (bits.map (·.eval a)) := by
  induction bits generalizing power with
  | nil => simp [le_bits_terms]
  | cons b bs ih => simp [le_bits_terms, ih]; ring

@[simp, cs_eval] theorem _root_.ArkR1CS.Boolean.eval_le_bits_to_fp (a : Assignment F)
    (bits : List (Boolean F)) :
    (Boolean.le_bits_to_fp bits).eval a = leBitsValue (bits.map (·.eval a)) := by
  unfold Boolean.le_bits_to_fp
  split_ifs with h
  · simp only [eval_Constant]
    congr 1
    apply List.map_congr_left
    intro b hb
    have := List.all_eq_true.mp h b hb
    rcases b with b | v
    · cases b <;> simp [Boolean.value]
    · simp [Boolean.is_constant] at this
  · simp [eval_le_bits_terms]

private theorem not_isConstant_sub (v : AllocatedFp F) (y : FpVar F) :
    ¬ (((Var v).sub y).isConstant ∧ (zero : FpVar F).isConstant) := fun ⟨h, _⟩ => by
  cases y <;> simp [sub, isConstant] at h

omit [Field F] [DecidableEq F] in
private theorem forall₂_forall_mem_right {α β : Type} {P : β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ (fun _ y => P y) xs ys → ∀ y ∈ ys, P y
  | _, _, .nil => by simp
  | _, _, .cons hp hs => by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hp
    · exact forall₂_forall_mem_right hs y hy

/-- `FpVar::to_bits_le_with_top_bits_zero(size)`: `size` boolean-checked bits
whose value is enforced to be `self`, i.e. `self < 2^size`. -/
def to_bits_le_with_top_bits_zero [IntoBigInt F] (x : FpVar F) (size : Nat) :
    CS F (List (Boolean F) × FpVar F) := do
  let v := IntoBigInt.into_bigint x.value
  let lower_bits ← (List.range size).mapM fun i =>
    match x with
    | Constant _ => pure (Boolean.new_constant (v.testBit i))
    | Var _ => Boolean.new_witness (v.testBit i)
  let lower_bits_fp := Boolean.le_bits_to_fp lower_bits
  let rest := x.sub lower_bits_fp
  EqGadget.enforce_equal rest zero
  pure (lower_bits, rest)

/-- Soundness of `to_bits_le_with_top_bits_zero` on a variable (on a constant,
arkworks emits no constraint): `size` bits, each `0` or `1`, whose value is
`self`. -/
theorem to_bits_le_with_top_bits_zero_sound [IntoBigInt F] (x : FpVar F) (hx : ¬ x.isConstant)
    (size : Nat) (k : Counters) (a : Assignment F)
    (h : ConstraintsHold a ((x.to_bits_le_with_top_bits_zero size).run k).2) :
    let bits := ((x.to_bits_le_with_top_bits_zero size).run k).1.1
    bits.length = size ∧ (∀ b ∈ bits, b.eval a = 0 ∨ b.eval a = 1) ∧
      x.eval a = leBitsValue (bits.map (·.eval a)) := by
  cases x with
  | Constant c => exact absurd trivial hx
  | Var v =>
    simp only [to_bits_le_with_top_bits_zero, CS.run_bind, CS.run_pure,
      constraintsHold_append, constraintsHold_nil, and_true] at h ⊢
    obtain ⟨hbits, heq⟩ := h
    have hall := CS.mapM_sound _ (fun _ b => b.eval a = 0 ∨ b.eval a = 1) a
      (fun i k' h' => Boolean.new_witness_sound _ k' a h') _ _ hbits
    refine ⟨by simpa using hall.length_eq.symm, ?_, ?_⟩
    · exact forall₂_forall_mem_right hall
    · have := enforce_equal_sound _ zero (not_isConstant_sub v _) _ a heq
      simp only [eval_sub, eval_zero, sub_eq_zero] at this
      simpa using this

end FpVar

end ArkR1CS
