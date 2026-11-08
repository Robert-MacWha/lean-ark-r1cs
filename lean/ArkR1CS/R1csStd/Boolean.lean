/-
# `ark_r1cs_std::boolean` (the parts other gadgets depend on)

Only what `EqGadget` and `FpVar::is_neq` need: constants, `lc()`, `not`, and
`AllocatedBool::new_witness_without_booleanity_check`.
-/
import ArkR1CS.Relations.ConstraintSystem

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

end ArkR1CS
