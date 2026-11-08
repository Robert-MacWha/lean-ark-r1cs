/-
# `ark_r1cs_std::eq::EqGadget`

`enforce_equal` and `enforce_not_equal` are the trait's default
implementations: `conditional_enforce_equal(other, &Boolean::TRUE)`.
-/
import ArkR1CS.R1csStd.Boolean

namespace ArkR1CS

variable {F : Type} [Field F]

/-- Models `ark_r1cs_std::eq::EqGadget`: the required methods `is_eq`,
`conditional_enforce_equal` and `conditional_enforce_not_equal`. -/
class EqGadget (F : outParam Type) [Field F] (T : Type) where
  is_eq : T → T → CS F (Boolean F)
  conditional_enforce_equal : T → T → Boolean F → CS F Unit
  conditional_enforce_not_equal : T → T → Boolean F → CS F Unit

namespace EqGadget

variable {T : Type} [EqGadget F T]

/-- Models the default `EqGadget::is_neq`: `!is_eq(other)`. -/
def is_neq (x y : T) : CS F (Boolean F) := do
  let b ← is_eq (F := F) x y
  pure b.not

/-- Models the default `EqGadget::enforce_equal`:
`conditional_enforce_equal(other, &Boolean::TRUE)`. -/
def enforce_equal (x y : T) : CS F Unit :=
  conditional_enforce_equal x y Boolean.TRUE

/-- Models the default `EqGadget::enforce_not_equal`:
`conditional_enforce_not_equal(other, &Boolean::TRUE)`. -/
def enforce_not_equal (x y : T) : CS F Unit :=
  conditional_enforce_not_equal x y Boolean.TRUE

end EqGadget

end ArkR1CS
