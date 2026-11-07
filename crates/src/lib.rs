//! Canonical traces of arkworks constraint systems, for differential testing
//! against the ArkR1CS Lean model.
//!
//! [`render_trace`] renders a constraint system in the same form as the Lean
//! `renderTrace`, and [`lean_traces`] runs a Lean file that writes the model's
//! traces, so a test can build the same circuit with `ark-r1cs-std` and
//! compare the two strings.

use std::{collections::BTreeMap, fmt::Write, path::Path, process::Command};

use ark_ff::{Fp64, MontBackend, MontConfig, PrimeField};
use ark_relations::gr1cs::{ConstraintSystemRef, R1CS_PREDICATE_LABEL};

/// The small prime field the Lean traces use (`ZMod 17`).
#[derive(MontConfig)]
#[modulus = "17"]
#[generator = "3"]
pub struct F17Config;
/// The small prime field the Lean traces use (`ZMod 17`).
pub type F17 = Fp64<MontBackend<F17Config, 1>>;

fn render_lc<F: PrimeField>(row: &[(F, usize)]) -> String {
    let mut merged: BTreeMap<usize, F> = BTreeMap::new();
    for (coeff, col) in row {
        *merged.entry(*col).or_insert_with(F::zero) += coeff;
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

fn render_values<F: PrimeField>(values: &[F]) -> String {
    values
        .iter()
        .map(|v| v.into_bigint().to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

/// Renders a constraint system like the Lean `ArkR1CS.renderTrace`: a header
/// with the counts, the instance assignment without the leading one, the
/// witness assignment, and one `i: A | B | C` line per R1CS row with each
/// linear combination compacted and sorted by column.
///
/// The system is finalized first, so symbolic linear combinations are inlined.
pub fn render_trace<F: PrimeField>(cs: &ConstraintSystemRef<F>) -> String {
    cs.finalize();
    let matrices = cs.to_matrices().expect("constraint system is finalized");
    let r1cs = &matrices[R1CS_PREDICATE_LABEL];
    let (a, b, c) = (&r1cs[0], &r1cs[1], &r1cs[2]);

    let instance = cs.instance_assignment().expect("proving mode");
    let witness = cs.witness_assignment().expect("proving mode");

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

/// Runs `lake env lean --run <file> <dir>` in the Lake project at `lean_dir`
/// and returns the `<name>.trace` files it wrote, keyed by name.
///
/// `file` must define `main (args : List String) : IO Unit` that writes the
/// traces into the directory given as its argument. Panics with the Lean
/// output if the run fails, and if `lake` is not on the `PATH`.
pub fn lean_traces(lean_dir: impl AsRef<Path>, file: &str) -> BTreeMap<String, String> {
    let dir = tempdir();
    let output = Command::new("lake")
        .args(["env", "lean", "--run", file])
        .arg(&dir)
        .current_dir(lean_dir.as_ref())
        .output()
        .expect("`lake` on the PATH (install elan and build the Lean project first)");
    assert!(
        output.status.success(),
        "lean --run {file} failed:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let mut traces = BTreeMap::new();
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "trace") {
            let name = path.file_stem().unwrap().to_string_lossy().into_owned();
            traces.insert(name, std::fs::read_to_string(&path).unwrap());
        }
    }
    std::fs::remove_dir_all(&dir).ok();
    traces
}

fn tempdir() -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "ark-r1cs-trace-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}
