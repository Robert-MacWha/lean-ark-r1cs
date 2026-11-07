//! Builds the circuits of `lean/Traces.lean` with `ark-r1cs-std` and checks that
//! the arkworks constraint matrices and assignment match the traces rendered by
//! the Lean model into `target/traces` (`just test`).

use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::{FieldVar, fp::FpVar},
    prelude::GR1CSVar,
};
use ark_r1cs_trace::{F17, read_traces, render_trace};
use ark_relations::gr1cs::{
    ConstraintSystem, ConstraintSystemRef, OptimizationGoal, SynthesisError,
};

type Circuit = fn(ConstraintSystemRef<F17>) -> Result<(), SynthesisError>;

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

#[test]
fn traces_match_lean_model() {
    let expected = read_traces(concat!(env!("CARGO_MANIFEST_DIR"), "/target/traces"))
        .expect("traces written by `lake env lean --run Traces.lean` (see `just test`)");
    let circuits: [(&str, Circuit); 3] = [("arith", arith), ("field", field), ("eq", eq)];
    assert_eq!(
        expected.len(),
        circuits.len(),
        "trace set differs from the Lean cases"
    );

    for (name, circuit) in circuits {
        let cs = ConstraintSystem::<F17>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);
        circuit(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap(), "{name}: not satisfied");
        assert_eq!(
            render_trace(&cs).unwrap(),
            expected[name],
            "{name}: arkworks trace differs from the Lean model"
        );
    }
}
