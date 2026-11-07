/-
# `ark_r1cs_std::eq::EqGadget`

`enforce_equal` and `enforce_not_equal` are the trait's default
implementations: `conditional_enforce_equal(other, &Boolean::TRUE)`.
-/
import ArkR1CS.R1csStd.Boolean

namespace ArkR1CS

variable {F : Type} [Field F]

/-- `EqGadget<F>`. -/
class EqGadget (F : outParam Type) [Field F] (T : Type) where
  is_eq : T → T → CS F (Boolean F)
  conditional_enforce_equal : T → T → Boolean F → CS F Unit
  conditional_enforce_not_equal : T → T → Boolean F → CS F Unit

namespace EqGadget

variable {T : Type} [EqGadget F T]

/-- Default `is_neq`: `is_eq(other)?.not()`. -/
def is_neq (x y : T) : CS F (Boolean F) := do
  let b ← is_eq (F := F) x y
  pure b.not

/-- Default `enforce_equal`. -/
def enforce_equal (x y : T) : CS F Unit :=
  conditional_enforce_equal x y Boolean.TRUE

/-- Default `enforce_not_equal`. -/
def enforce_not_equal (x y : T) : CS F Unit :=
  conditional_enforce_not_equal x y Boolean.TRUE

end EqGadget

end ArkR1CS
