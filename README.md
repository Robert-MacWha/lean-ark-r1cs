# lean-ark-r1cs

A Lean 4 model of arkworks R1CS gadgets, with soundness proofs, for formally verifying arkworks circuits.

## Background

Circuits written with [ark-r1cs-std](https://github.com/arkworks-rs/r1cs-std) on top of [ark-relations](https://github.com/arkworks-rs/snark) can't be checked by Lean directly. This package re-implements the gadgets in Lean, following the Rust method by method and keeping the Rust names, so that a circuit can be written against the model and proved sound: for every assignment that satisfies the constraints a gadget emits, its output has the value the gadget is supposed to compute. Completeness is not proved; tests cover it.

A model is only as good as its fidelity to the Rust, so the package can also render a gadget's constraint matrices in the same form as `ConstraintSystem::to_matrices()`, for comparison against the real arkworks output.

## Install

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "ark-r1cs"
git = "https://github.com/Robert-MacWha/lean-ark-r1cs"
subDir = "lean"
rev = "main"
```

For the differential test, add the Rust crate as a dev-dependency:

```toml
[dev-dependencies]
ark-r1cs-trace = { git = "https://github.com/Robert-MacWha/lean-ark-r1cs" }
```

## Usage

Write the gadget in `CS F` with the `FpVar` operations, keeping the structure of the Rust, then prove its soundness lemma from the lemmas of the operations it uses. The `cs_run` simp set unfolds a gadget's run into the constraints of each step, and `cs_eval` evaluates variables and linear combinations:

```lean
import ArkR1CS
open ArkR1CS

def squarePlusOne {F : Type} [Field F] [DecidableEq F] (x : FpVar F) : CS F (FpVar F) := do
  let sq ← x.square
  pure (sq.add FpVar.one)

theorem squarePlusOne_sound {F : Type} [Field F] [DecidableEq F] (x : FpVar F) (k : Counters)
    (a : Assignment F) (h : ConstraintsHold a ((squarePlusOne x).run k).2) :
    ((squarePlusOne x).run k).1.eval a = x.eval a * x.eval a + 1 := by
  simp only [squarePlusOne, cs_run] at h ⊢
  rw [FpVar.eval_add, FpVar.square_sound x k a h, FpVar.eval_one]
```

`renderTrace` prints the constraint matrices and the prover's assignment of a gadget run. The Rust crate in `crates/` (`ark-r1cs-trace`) renders an arkworks constraint system the same way and can run a Lean file that writes the model's traces, so a test can build the same circuit with `ark-r1cs-std` and compare; its own integration test does this for every modelled operation (`cargo test --manifest-path crates/Cargo.toml`, with `lake` on the `PATH`). See [ark-hybrid-compression](https://github.com/Robert-MacWha/ark-hybrid-compression) for a full circuit.

Build with `lake exe cache get` followed by `lake build` in `lean/`.
