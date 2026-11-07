//! Builds the circuits of `Traces.lean` with `ark-r1cs-std` and checks that
//! the arkworks constraint matrices and assignment match `traces/*.trace`,
//! rendered by the Lean model.

use std::{collections::BTreeMap, fmt::Write};

use ark_ff::{Fp64, MontBackend, MontConfig, PrimeField, Zero};
use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{FieldVar, fp::FpVar},
    prelude::GR1CSVar,
};
use ark_relations::gr1cs::{
    ConstraintSystem, ConstraintSystemRef, OptimizationGoal, R1CS_PREDICATE_LABEL, SynthesisError,
};

/// `ZMod 17` in the Lean traces.
#[derive(MontConfig)]
#[modulus = "17"]
#[generator = "3"]
pub struct F17Config;
pub type F17 = Fp64<MontBackend<F17Config, 1>>;

fn f(n: u64) -> F17 {
    F17::from(n)
}

/// `Traces.arith`.
fn arith(cs: ConstraintSystemRef<F17>) -> Result<(), SynthesisError> {
    let x = FpVar::new_witness(cs.clone(), || Ok(f(3)))?;
    let y = FpVar::new_witness(cs.clone(), || Ok(f(5)))?;
    let s = &x + &y;
    let d = &x - &y;
    let p = &x * &y;
    let t = &(&s + FpVar::constant(f(7))) - FpVar::constant(f(2));
    let u = FpVar::constant(f(4)) * &d;
    let v = FpVar::constant(f(1)) * &d;
    let w = &d + FpVar::constant(f(0));
    let r = &(&p + &t) + &(&u + &(&v + &w));
    let z = FpVar::new_witness(cs, || r.value())?;
    z.enforce_equal(&r)
}

/// `Traces.field`.
fn field(cs: ConstraintSystemRef<F17>) -> Result<(), SynthesisError> {
    let x = FpVar::new_witness(cs.clone(), || Ok(f(3)))?;
    let d = x.double()?;
    let n = x.negate()?;
    let sq = x.square()?;
    let inv = x.inverse()?;
    let r = &(&d + &n) + &(&sq + &inv);
    let z = FpVar::new_witness(cs, || r.value())?;
    z.enforce_equal(&r)
}

/// `Traces.eq`.
fn eq(cs: ConstraintSystemRef<F17>) -> Result<(), SynthesisError> {
    let x = FpVar::new_input(cs.clone(), || Ok(f(3)))?;
    let y = FpVar::new_witness(cs, || Ok(f(3)))?;
    x.enforce_equal(&y)?;
    x.enforce_equal(&FpVar::constant(f(3)))?;
    FpVar::constant(f(3)).enforce_equal(&y)?;
    let _ = x.is_eq(&y)?;
    x.enforce_not_equal(&FpVar::constant(f(4)))
}

fn render_lc(row: &[(F17, usize)]) -> String {
    let mut merged: BTreeMap<usize, F17> = BTreeMap::new();
    for (coeff, col) in row {
        *merged.entry(*col).or_insert_with(F17::zero) += coeff;
    }
    let terms: Vec<String> = merged
        .iter()
        .filter(|(_, c)| !c.is_zero())
        .map(|(col, c)| format!("{col}:{}", c.into_bigint()))
        .collect();
    if terms.is_empty() {
        "-".to_string()
    } else {
        terms.join(" ")
    }
}

fn render_values(values: &[F17]) -> String {
    values
        .iter()
        .map(|v| v.into_bigint().to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Renders a finalized constraint system like `ArkR1CS.renderTrace`.
fn render_trace(cs: &ConstraintSystemRef<F17>) -> String {
    let matrices = cs.to_matrices().unwrap();
    let r1cs = &matrices[R1CS_PREDICATE_LABEL];
    let (a, b, c) = (&r1cs[0], &r1cs[1], &r1cs[2]);

    // `instance_assignment` starts with the constant one, which the model
    // does not count as an input.
    let instance = cs.instance_assignment().unwrap();
    let witness = cs.witness_assignment().unwrap();

    let mut out = String::new();
    writeln!(
        out,
        "inputs={} witnesses={} constraints={}",
        instance.len() - 1,
        witness.len(),
        a.len()
    )
    .unwrap();
    writeln!(out, "instance: {}", render_values(&instance[1..])).unwrap();
    writeln!(out, "witness: {}", render_values(&witness)).unwrap();
    for i in 0..a.len() {
        writeln!(
            out,
            "{i}: {} | {} | {}",
            render_lc(&a[i]),
            render_lc(&b[i]),
            render_lc(&c[i])
        )
        .unwrap();
    }
    out
}

fn check(name: &str, circuit: fn(ConstraintSystemRef<F17>) -> Result<(), SynthesisError>) {
    let cs = ConstraintSystem::<F17>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    circuit(cs.clone()).unwrap();
    cs.finalize();
    assert!(cs.is_satisfied().unwrap(), "{name}: not satisfied");

    let expected = std::fs::read_to_string(format!(
        "{}/../../traces/{name}.trace",
        env!("CARGO_MANIFEST_DIR")
    ))
    .expect("trace rendered by the Lean model");
    assert_eq!(
        render_trace(&cs),
        expected,
        "{name}: arkworks trace differs from the Lean model"
    );
}

#[test]
fn arith_matches() {
    check("arith", arith);
}

#[test]
fn field_matches() {
    check("field", field);
}

#[test]
fn eq_matches() {
    check("eq", eq);
}
