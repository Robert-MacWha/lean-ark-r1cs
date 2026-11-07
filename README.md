# lean-ark-r1cs

A Lean 4 / Mathlib model of [`ark-relations`](https://github.com/arkworks-rs/snark) and [`ark-r1cs-std`](https://github.com/arkworks-rs/r1cs-std) for formally verifying arkworks circuits. The model is written method by method against the Rust crates, keeping their names, and every constraint-emitting operation comes with a soundness lemma: whatever assignment satisfies the constraints a gadget emits, its output evaluates to the specified value. Soundness only; completeness is left to tests.

## What is modelled

`ArkR1CS.Relations` covers `ark_relations::gr1cs`: `Variable` (`Zero`, `One`, `Instance i`, `Witness i`; `One` is instance variable 0 and `ConstraintSystem::new()` starts at `num_instance_variables = 1`), `LinearCombination`, and the constraint system. A gadget is a `CS F α`: given the allocation counters, its output and the list of operations it performs (`new_input_variable`, `new_witness_variable`, `enforce_r1cs_constraint`), so `do` notation threads the counters like a `ConstraintSystemRef`. `Variable::SymbolicLc` is not modelled: `new_lc` returns the linear combination itself, i.e. the form `finalize()` inlines to.

`ArkR1CS.R1csStd` covers `ark_r1cs_std`: `AllocatedFp` / `FpVar` with the `impl_ops!` dispatch for `Add`, `Sub`, `Mul`, the `is_zero()` / `is_one()` shortcuts, `double`, `negate`, `square`, `inverse`, `is_neq` (two constraints; `is_eq` is its negation), `conditional_enforce_equal`, `conditional_enforce_not_equal`, and `EqGadget` with its default `enforce_equal = conditional_enforce_equal(_, TRUE)`; `Boolean` as far as those need it. `value: Option<F>` is modelled as always present (proving mode).

`ArkR1CS.CryptoPrimitives` provides the black-box `CRHSchemeGadget` interface: a native hash with a gadget assumed sound.

`ArkR1CS.Trace` renders a gadget's operations in the shape of `ConstraintSystem::to_matrices()` plus the prover's assignment, so a model can be differentially tested against the real constraint system.

Two arkworks quirks the mirror makes visible: `enforce_equal` on two `Constant`s emits nothing, so `FpVar.enforce_equal_sound` requires one side to be a variable, and `is_neq` allocates its bit without a booleanity check (its soundness lemma still pins the bit to the indicator).

## Using it

Require it from a Lake project:

```toml
[[require]]
name = "ark-r1cs"
git = "https://github.com/Robert-MacWha/lean-ark-r1cs"
rev = "main"
```

Write the gadget in `CS F` with the `FpVar` operations, keeping the same structure as the Rust, and prove its `*_sound` lemma by unfolding with `simp only [gadget, CS.run_bind, CS.run_pure, constraintsHold_append, …]` and applying the `*_sound` lemmas of the operations used. If the gadget has an arkworks counterpart, render both with `renderTrace` and `to_matrices()` and compare. See [ark-hybrid-compression](https://github.com/Robert-MacWha/ark-hybrid-compression) for a complete example, including the differential test.

## Building

```bash
lake exe cache get
lake build
```
