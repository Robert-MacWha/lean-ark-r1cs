# lean-ark-r1cs

A Lean 4 model of arkworks R1CS gadgets, with soundness proofs, for formally verifying arkworks circuits.

This package re-implements the [ark-r1cs-std](https://github.com/arkworks-rs/r1cs-std) gadgets in Lean, following the Rust method by method and keeping the Rust names. Provides basic gadgets for proving the soundness of a circuit. Does not provide completeness.

## Usage

Add the package to your `lakefile.toml`:

```toml
[[require]]
name = "ark-r1cs"
git = "https://github.com/Robert-MacWha/lean-ark-r1cs"
subDir = "lean"
rev = "main"
```

Write the gadget in `CS F` with the `FpVar` operations, keeping the structure of the Rust, then prove its soundness lemma, `Sound gadget spec`, from the lemmas of the operations it uses. `Sound c P` says that every assignment satisfying the constraints `c` emits satisfies `P` of its output. The `cs_run` simp set unfolds a gadget's run into the constraints of each step, and `cs_eval` evaluates variables and linear combinations:

```lean
import ArkR1CS
open ArkR1CS

def squarePlusOne {F : Type} [Field F] [DecidableEq F] (x : FpVar F) : CS F (FpVar F) := do
  let sq ← x.square
  pure (sq + FpVar.one)

theorem squarePlusOne_sound {F : Type} [Field F] [DecidableEq F] (x : FpVar F) :
    Sound (squarePlusOne x) fun a r => r.eval a = x.eval a * x.eval a + 1 := by
  intro k a h
  simp only [squarePlusOne, cs_run] at h ⊢
  rw [FpVar.eval_hAdd, FpVar.square_sound x k a h, FpVar.eval_one]
```

To check a gadget against arkworks, render it with `renderTrace` from a Lean file run with `lake env lean --run`. Then build the same gadget with `ark-r1cs-std` and compare with `render_trace` from the `ark-r1cs-trace` crate in `crates/`:

```toml
[dev-dependencies]
ark-r1cs-trace = { git = "https://github.com/Robert-MacWha/lean-ark-r1cs" }
```

```rust
use ark_r1cs_trace::{F17, read_traces, render_trace};
use ark_relations::gr1cs::ConstraintSystem;

#[test]
fn square_plus_one_matches() {
    let expected = read_traces("target/traces").unwrap();
    let cs = ConstraintSystem::<F17>::new_ref();
    square_plus_one(cs.clone()).unwrap(); // the same gadget, built with ark-r1cs-std
    assert_eq!(render_trace(&cs).unwrap(), expected["square_plus_one"]);
}
```

See [`lean/Traces.lean`](lean/Traces.lean) and [`crates/tests/traces.rs`](crates/tests/traces.rs) for the comparison test of every modelled operation. `just test` renders the traces and runs it.
