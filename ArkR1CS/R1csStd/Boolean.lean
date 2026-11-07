/-
# `ark_r1cs_std::boolean` (the parts other gadgets depend on)

Only what `EqGadget` and `FpVar::is_neq` need: constants, `lc()`, `not`, and
`AllocatedBool::new_witness_without_booleanity_check`.
-/
import ArkR1CS.Relations.ConstraintSystem

namespace ArkR1CS

variable {F : Type}

/-- `AllocatedBool<F>`: a variable holding `0` or `1`. -/
structure AllocatedBool (F : Type) where
  value : Bool
  /-- `variable` in arkworks (a `Variable`, here its inlined linear combination). -/
  lc : LinearCombination F

/-- `Boolean<F>`. -/
inductive Boolean (F : Type)
  | Constant (b : Bool)
  | Var (v : AllocatedBool F)

namespace Boolean

/-- `Boolean::TRUE`. -/
def TRUE : Boolean F := Constant true
/-- `Boolean::FALSE`. -/
def FALSE : Boolean F := Constant false

/-- `Boolean::value()`. -/
def value : Boolean F → Bool
  | Constant b => b
  | Var v => v.value

/-- `Boolean::lc()`. -/
def lc [Field F] : Boolean F → LinearCombination F
  | Constant false => LinearCombination.zero
  | Constant true => LinearCombination.ofVar .One
  | Var v => v.lc

/-- Value of the boolean's linear combination. -/
def eval [Field F] (a : Assignment F) (b : Boolean F) : F := b.lc.eval a

@[simp] theorem eval_TRUE [Field F] (a : Assignment F) : eval a (TRUE : Boolean F) = 1 := by
  simp [eval, TRUE, lc]
@[simp] theorem eval_FALSE [Field F] (a : Assignment F) : eval a (FALSE : Boolean F) = 0 := by
  simp [eval, FALSE, lc]
@[simp] theorem eval_Var [Field F] (a : Assignment F) (v : AllocatedBool F) :
    eval a (Var v) = v.lc.eval a := rfl

end Boolean

namespace AllocatedBool

/-- `AllocatedBool::not`: `lc_diff![One, self.lc]`. -/
def not [Field F] (v : AllocatedBool F) : AllocatedBool F :=
  ⟨!v.value, LinearCombination.diff (LinearCombination.ofVar .One) v.lc⟩

@[simp] theorem eval_not [Field F] (a : Assignment F) (v : AllocatedBool F) :
    v.not.lc.eval a = 1 - v.lc.eval a := by
  simp [not]

/-- `AllocatedBool::new_witness_without_booleanity_check`. -/
def new_witness_without_booleanity_check [Field F] (b : Bool) : CS F (AllocatedBool F) := do
  let v ← new_witness_variable (if b then (1 : F) else 0)
  pure ⟨b, LinearCombination.ofVar v⟩

@[simp] theorem run_new_witness_without_booleanity_check [Field F] (b : Bool) (k : Counters) :
    (new_witness_without_booleanity_check b).run k =
      (⟨b, LinearCombination.ofVar (.Witness k.num_witness_variables)⟩,
        [.witness (if b then (1 : F) else 0)]) := rfl

end AllocatedBool

/-- `impl Not for Boolean`. -/
def Boolean.not [Field F] : Boolean F → Boolean F
  | .Constant b => .Constant (!b)
  | .Var v => .Var v.not

end ArkR1CS
