# Contributing

BulkSketch is a Rust set-reconciliation library with Lean 4 proofs of its
arithmetic and decoder contracts. Changes should preserve deterministic results,
bounded work and the stated source-to-proof relationship.

## Build and test

Use Rust through `rustup` so Cargo selects the version pinned in
[`rust-toolchain.toml`](rust-toolchain.toml). Run commands from the repository
root unless stated otherwise. Formatting uses nightly Rustfmt for the options
in `rustfmt.toml`; native builds use the pinned production toolchain.

```sh
cargo +nightly fmt --all -- --check
cargo test --release --locked -p bulksketch
```

Run the relevant test target while developing, then run the complete native
suite before submitting a change. For example:

```sh
cargo test --release --locked -p bulksketch --lib
cargo test --release --locked -p bulksketch --test readme_example
cargo test --release --locked -p bulksketch --test ownership
```

The tests include fixed vectors in `tests/vectors/` and a compile-fail check of
decode-job borrowing. The ownership check needs Python 3 and `rustc`.

Use fixed inputs and seeds for regression cases. Add tests that exercise a
changed contract, boundary or failure path. Keep expected results independent
of the implementation where practical.

## Implementation changes

- Preserve decoded sets, output ordering, error behavior and work accounting
  for equivalent inputs. Portable and accelerated backends must agree under
  their documented contracts.
- Keep overflow checks, slice bounds, scratch requirements and zero-ID handling
  explicit. A successful decode must satisfy the documented capacity and input
  conditions.
- Avoid unnecessary allocations and steady-state work. Keep memory ownership
  and aliasing requirements explicit, particularly around `unsafe` backends.
- Separate native functional behavior from compiler, runtime, allocator and ISA
  assumptions. A test or component proof should be described at its actual
  scope.

For a performance change, report a baseline and the changed version using the
same release configuration, inputs and resulting state. Include capacity,
difference size, backend, CPU and relevant compiler settings. Explain any
tradeoff in allocations, scratch size or worst-case work. Local microbenchmarks
do not establish production network throughput.

## Lean proofs and source fingerprints

The [verification guide](verification/lean/README.md) describes the exact
theorem statements, source inventory and trust assumptions. Install Python 3
and `elan`, and use the Lean version pinned in
[`verification/lean/lean-toolchain`](verification/lean/lean-toolchain). Its
distribution must provide `leanexport`, `leanchecker` and `nanoda_bin`.

To set up the pinned Aeneas Lean runtime and run the complete verification:

```sh
cd verification/lean
python3 tooling/setup_lean_runtime.py
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```

Setup fetches the pinned runtime and Lean dependencies. Regenerating Rust
extraction requires the separate pinned Charon/Aeneas producer toolchains.
Follow the source-regeneration instructions in the verification guide.

Keep propositions fixed while constructing their proofs. Do not weaken a
statement, add a correctness assumption or remove an obligation to make a check
pass. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
Application correctness must not be supplied by an axiom or a proof hole.

When source, build inputs or generated artifacts change, update their source
associations and dependent fingerprints deliberately. Record intentional frozen
input changes in `input_revisions`. Preserve the native source inventory and
distinguish mathematical models from refinements of original function bodies.
Hash updates alone do not establish correctness.

Keep generated bodies tied to the pinned extraction and document any translator
variant or runtime model involved. State new assumptions explicitly and run the
full verification command after changing proof inputs, contracts or validators.

Before running the aggregate verifier, stage the exact files intended for the
commit. Its publication check reads staged Git blobs, including symlink targets.
Use neutral workspace paths in committed extraction evidence; exclude personal
home-directory paths, temporary-machine paths and credentials. Keep generated
build caches and proof-output logs in their ignored directories.

## Submitting changes

Use a fork and open a pull request against `main`. Keep each change focused and
explain the concrete problem, resulting behavior and validation performed.
Include reproduction commands and matched baseline results for performance
changes. Identify any platform-specific test that could not run.

Discuss changes to public APIs, wire formats, field representations, work
schedules or proof assumptions before implementation. Document compatibility
effects and preserve existing callers unless an interface change is intended.

Contributions are made under the repository's [MIT License](LICENSE).
Preserve applicable copyright and license notices.
