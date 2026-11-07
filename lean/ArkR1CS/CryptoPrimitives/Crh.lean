/-
# `ark_crypto_primitives::crh` (black-box interface)

A `CRHScheme` with `Input = [F]`, `Output = F` together with its
`CRHSchemeGadget` with `InputVar = [FpVar<F>]`, `OutputVar = FpVar<F>`.
Parameters are baked into the functions. The only assumptions made about a
hash are `sound` (any satisfying assignment evaluates the gadget output to the
native hash of the evaluated inputs) and `noInputs` (the gadget allocates no
public inputs, as Poseidon's does not).
-/
import ArkR1CS.R1csStd.Fields.Fp

namespace ArkR1CS

variable {F : Type} [Field F] [DecidableEq F]

/-- A native hash with a sound in-circuit gadget. -/
structure CRHSchemeGadget (F : Type) [Field F] [DecidableEq F] where
  /-- `CRHScheme::evaluate`. -/
  evaluate_native : List F → F
  /-- `CRHSchemeGadget::evaluate`. -/
  evaluate : List (FpVar F) → CS F (FpVar F)
  sound : ∀ (xs : List (FpVar F)) (k : Counters) (a : Assignment F),
    ConstraintsHold a ((evaluate xs).run k).2 →
      ((evaluate xs).run k).1.eval a = evaluate_native (xs.map (·.eval a))
  noInputs : ∀ (xs : List (FpVar F)) (k : Counters), Op.inputCount ((evaluate xs).run k).2 = 0

end ArkR1CS
