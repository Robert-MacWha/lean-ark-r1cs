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

/-- Models a hash from `ark_crypto_primitives::crh` with `Input = [F]` and `Output = F`: the
native `CRHScheme` together with its `CRHSchemeGadget`, parameters baked in. Treated as a black
box: `sound` and `noInputs` are assumptions. -/
structure CRHSchemeGadget (F : Type) [Field F] [DecidableEq F] where
  /-- Models `CRHScheme::evaluate`. -/
  evaluate_native : List F → F
  /-- Models `CRHSchemeGadget::evaluate`. -/
  evaluate : List (FpVar F) → CS F (FpVar F)
  /-- If the gadget's constraints hold, its output equals the native hash of the inputs' values. -/
  sound : ∀ xs, Sound (evaluate xs) fun a r => r.eval a = evaluate_native (xs.map (·.eval a))
  /-- The gadget allocates no public inputs (as for Poseidon). -/
  noInputs : ∀ xs k, Op.inputs ((evaluate xs).run k).2 = []

end ArkR1CS
