//! Canonical renderings of arkworks constraint systems, for differential
//! testing against the ArkR1CS Lean model.

use std::{collections::BTreeMap, io, path::Path};

use ark_ff::{Fp64, MontBackend, MontConfig, PrimeField};
use ark_relations::gr1cs::{ConstraintSystemRef, R1CS_PREDICATE_LABEL, SynthesisError};

/// Configuration of [`F17`].
#[derive(MontConfig)]
#[modulus = "17"]
#[generator = "3"]
pub struct F17Config;

/// The prime field of order 17, which the Lean traces use (`ZMod 17`).
pub type F17 = Fp64<MontBackend<F17Config, 1>>;

/// Renders a constraint system in the form of the Lean `ArkR1CS.renderTrace`.
///
/// The output is a header with the numbers of inputs, witnesses and
/// constraints, the instance assignment without the leading one, the witness
/// assignment, and one `i: A | B | C` line per R1CS row with every linear
/// combination compacted and sorted by column. The system is finalized first,
/// so symbolic linear combinations are inlined.
///
/// # Errors
///
/// Returns an error if the system is in setup mode, since it then has no
/// assignment.
pub fn render_trace<F: PrimeField>(cs: &ConstraintSystemRef<F>) -> Result<String, SynthesisError> {
    cs.finalize();
    let matrices = cs.to_matrices()?;
    let instance = cs.instance_assignment()?;
    let witness = cs.witness_assignment()?;

    let empty = Vec::new();
    let (a, b, c) = match matrices.get(R1CS_PREDICATE_LABEL) {
        Some(m) if m.len() == 3 => (&m[0], &m[1], &m[2]),
        _ => (&empty, &empty, &empty),
    };

    let mut out = format!(
        "inputs={} witnesses={} constraints={}\n",
        instance.len().saturating_sub(1),
        witness.len(),
        a.len()
    );
    out.push_str(&format!(
        "instance: {}\n",
        render_values(instance.get(1..).unwrap_or_default())
    ));
    out.push_str(&format!("witness: {}\n", render_values(&witness)));
    for (i, ((a, b), c)) in a.iter().zip(b).zip(c).enumerate() {
        out.push_str(&format!(
            "{i}: {} | {} | {}\n",
            render_lc(a),
            render_lc(b),
            render_lc(c)
        ));
    }
    Ok(out)
}

/// Reads the `<name>.trace` files in `dir`, keyed by name.
///
/// # Errors
///
/// Returns an error if the directory or one of the files cannot be read.
pub fn read_traces(dir: impl AsRef<Path>) -> io::Result<BTreeMap<String, String>> {
    let mut traces = BTreeMap::new();
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if path.extension().is_some_and(|e| e == "trace") {
            let name = path
                .file_stem()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_default();
            traces.insert(name, std::fs::read_to_string(&path)?);
        }
    }
    Ok(traces)
}

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
