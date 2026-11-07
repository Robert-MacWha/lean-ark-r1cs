/-
# Simp sets

Two simp sets so that gadget proofs don't repeat the same lemma lists:

* `cs_run` unfolds gadget runs: `CS.run_bind`, the allocation and constraint
  primitives, the list plumbing they produce, `ConstraintsHold` over those
  lists, and the counter arithmetic. Typical use: `simp only [cs_run, myGadget]
  at h ⊢`, after which `h` is a conjunction of the constraints of each step.
* `cs_eval` evaluates variables, linear combinations, `FpVar`s and `Boolean`s
  under an assignment.
-/
import Lean.Meta.Tactic.Simp.RegisterCommand

register_simp_attr cs_run
register_simp_attr cs_eval
