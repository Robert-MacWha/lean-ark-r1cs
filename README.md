# lean-ark-r1cs

A Lean 4 model of arkworks R1CS gadgets, with soundness proofs, for formally verifying arkworks circuits.

## Background

Circuits written with [ark-r1cs-std](https://github.com/arkworks-rs/r1cs-std) on top of [ark-relations](https://github.com/arkworks-rs/snark) can't be checked by Lean directly. This package re-implements the gadgets in Lean, following the Rust method by method and keeping the Rust names, so that a circuit can be written against the model and proved sound: for every assignment that satisfies the constraints a gadget emits, its output has the value the gadget is supposed to compute. Completeness is not proved; tests cover it.

A model is only as good as its fidelity to the Rust, so the package also renders a gadget's constraint matrices in the same form as `ConstraintSystem::to_matrices()`, and ships a small Rust crate that renders real arkworks constraint systems the same way, so the two can be compared.

## Install

Add the Lean package to your `lakefile.toml`:

```toml
[[require]]
name = "ark-r1cs"
git = "https://github.com/Robert-MacWha/lean-ark-r1cs"
subDir = "lean"
rev = "main"
```

For the comparison against arkworks, add the Rust crate as a dev-dependency:

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

To check a gadget against arkworks, write a Lean file whose `main` renders it with `renderTrace` into a directory, run it with `lake env lean --run`, and compare in a Rust test:

```rust
use ark_r1cs_trace::{F17, read_traces, render_trace};

let expected = read_traces("target/traces").unwrap();
let cs = ConstraintSystem::<F17>::new_ref();
square_plus_one(cs.clone()).unwrap(); // the same gadget, built with ark-r1cs-std
assert_eq!(render_trace(&cs).unwrap(), expected["square_plus_one"]);
```

`lean/Traces.lean` and `crates/tests/traces.rs` do this for every modelled operation; `just test` builds the model, renders the traces and runs the comparison. See [ark-hybrid-compression](https://github.com/Robert-MacWha/ark-hybrid-compression) for a full circuit.
