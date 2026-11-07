# Build the Lean model and proofs.
lean:
    cd lean && lake build

# Render the model's traces and check them against arkworks.
test: lean
    mkdir -p crates/target/traces
    cd lean && lake env lean --run Traces.lean ../crates/target/traces
    cd crates && cargo test

check:
    cd crates && cargo fmt --all -- --check
    cd crates && cargo clippy --all-targets -- -D warnings
