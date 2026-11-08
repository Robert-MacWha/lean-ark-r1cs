//! Builds the circuits of `lean/Traces.lean` with `ark-r1cs-std` and checks that
//! the arkworks constraint matrices and assignment match the traces rendered by
//! the Lean model into `target/traces` (`just test`).

use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
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
    let l = &(FpVar::constant(f(2)) + &x) + &(FpVar::constant(f(2)) - &y);
    let m = &x * f(6);
    let m0 = &x * f(0);
    let r = &(&(&p + &t) + &(&u + &(&v + &w))) + &(&l + &(&m + &m0));
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
    let sc = FpVar::constant(f(4)).square()?;
    let ic = FpVar::constant(f(4)).inverse()?;
    let r = &(&(&d + &n) + &(&sq + &inv)) + &(&sc + &ic);
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
    let b = x.is_eq(&FpVar::constant(f(3)))?;
    let c = FpVar::constant(f(5)).is_eq(&y)?;
    let _ = FpVar::constant(f(5)).is_eq(&FpVar::constant(f(5)))?;
    let _ = x.is_neq(&FpVar::constant(f(4)))?;
    x.conditional_enforce_equal(&FpVar::constant(f(3)), &b)?;
    x.conditional_enforce_not_equal(&FpVar::constant(f(4)), &b)?;
    y.conditional_enforce_equal(&FpVar::constant(f(7)), &c)?;
    y.conditional_enforce_not_equal(&FpVar::constant(f(3)), &c)?;
    x.enforce_not_equal(&FpVar::constant(f(4)))
}

/// `Traces.boolean`.
fn boolean(cs: ConstraintSystemRef<F17>) -> Result<(), SynthesisError> {
    let x = Boolean::new_witness(cs.clone(), || Ok(true))?;
    let y = Boolean::new_witness(cs, || Ok(false))?;
    let _ = &x & &y;
    let _ = &x | &y;
    let _ = &x & &Boolean::TRUE;
    let _ = &Boolean::FALSE & &y;
    let _ = &x | &Boolean::FALSE;
    let _ = &Boolean::TRUE | &y;
    let n = !&x;
    let _ = &n | &y;
    Ok(())
}

/// `Traces.select`.
fn select(cs: ConstraintSystemRef<F17>) -> Result<(), SynthesisError> {
    let c = Boolean::new_witness(cs.clone(), || Ok(true))?;
    let x = FpVar::new_witness(cs.clone(), || Ok(f(3)))?;
    let y = FpVar::new_witness(cs.clone(), || Ok(f(5)))?;
    let a = c.select(&x, &y)?;
    let b = c.select(&FpVar::constant(f(7)), &y)?;
    let d = c.select(&x, &FpVar::constant(f(9)))?;
    let e = c.select(&FpVar::constant(f(7)), &FpVar::constant(f(9)))?;
    let g = Boolean::FALSE.select(&x, &y)?;
    let r = &(&a + &b) + &(&(&d + &e) + &(&g + &FpVar::from(c)));
    let z = FpVar::new_witness(cs, || r.value())?;
    z.enforce_equal(&r)
}

/// `Traces.bits`.
fn bits(cs: ConstraintSystemRef<F17>) -> Result<(), SynthesisError> {
    let x = FpVar::new_witness(cs.clone(), || Ok(f(11)))?;
    let (bits, _) = x.to_bits_le_with_top_bits_zero(4)?;
    let lo = Boolean::le_bits_to_fp(&bits[..2])?;
    let hi = Boolean::le_bits_to_fp(&[&[Boolean::TRUE], &bits[2..]].concat())?;
    let k = Boolean::le_bits_to_fp(&[Boolean::TRUE, Boolean::FALSE, Boolean::TRUE])?;
    let s: FpVar<F17> = [lo, hi, k, FpVar::constant(f(2))].into_iter().sum();
    let z = FpVar::new_witness(cs, || s.value())?;
    z.enforce_equal(&s)
}

#[test]
fn traces_match_lean_model() {
    let expected = read_traces(concat!(env!("CARGO_MANIFEST_DIR"), "/target/traces"))
        .expect("traces written by `lake env lean --run Traces.lean` (see `just test`)");
    let circuits: [(&str, Circuit); 6] = [
        ("arith", arith),
        ("field", field),
        ("eq", eq),
        ("boolean", boolean),
        ("select", select),
        ("bits", bits),
    ];
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
