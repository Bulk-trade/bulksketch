# Source-derived proof artifacts

The pinned native source is `0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`.
Source validation uses exact production-file/build-input hashes so proof-only
commits do not invalidate it.

## Narrow GF64 expression

```sh
python3 extraction/regenerate.py
```

This builds the locked `tooling/ast-extractor` utility with Rust `1.96.1`, parses
the actual native GF64 reduction branch and emits its XOR/shift syntax tree.
It validates `Gf64::BITS = 64`, `RawProduct`'s two u64 fields, and only accepts
the required immutable bindings, identifiers, fields, XOR and literal shifts
below 64. The entire source body and generated expression are hashed.

The parser/translator is unverified. It is not Aeneas output, a replacement Rust
crate, or a Rust semantic-refinement theorem. The corresponding Lean expression
has universal polynomial-division proofs, while its source semantic link remains
an open obligation.

## Actual WorkMeter extraction

The bridge's committed generated files were produced with:

| Component | Pin |
| --- | --- |
| Charon | `7b462d9159db2ed3015162352183906a30bfafc6` |
| Aeneas | `ab34bd28458a08c150b7cbf1873e59af74588138` |
| Charon Rust toolchain | `nightly-2026-09-17` with host rustc-dev/rust-src/LLVM tools |
| OCaml used for Aeneas | `5.3.0` |
| Lean runtime | `4.35.0`, with the exact dependency manifest in pinned Aeneas |

To reproduce extraction, build that exact Charon/Aeneas pair using their pinned
upstream instructions. From the native repository root, invoke the pinned
binaries as follows, choosing an output directory outside the committed files:

```sh
charon cargo --preset=aeneas --sysroot=default \
  --dest-file=/path/to/output/workmeter.llbc \
  '--start-from=bulksketch::types::_::new' \
  '--start-from=bulksketch::types::_::charge' \
  '--start-from=bulksketch::types::_::used' \
  -- --manifest-path Cargo.toml -p bulksketch --lib --locked

aeneas -backend lean -split-files -dest /path/to/output/workmeter-lean \
  /path/to/output/workmeter.llbc
```

The Charon environment must select `RUSTUP_TOOLCHAIN=nightly-2026-09-17` and an
isolated `CARGO_TARGET_DIR`. Check `has_errors=false` in the LLBC as well as the
process exit status. The original charge closure must remain present. Compare
the generated Types/Funs with the committed copies; do not edit generated bodies.

The committed LLBC, generated files and [linkage metadata](../bridge/source-linkage.json)
retain exact source spans, source-fragment hashes and IR hashes. One missing
standard-library `Option::is_none_or` operation has a concrete separately
documented adapter. Its original template is not used as an axiom premise.

Checking the committed bridge needs only its pinned Lean runtime and dependencies.
OCaml and the extraction compiler are regeneration prerequisites, not proof
checking prerequisites. The runtime adapter, frontend correctness, source/compiler
correspondence and machine execution remain explicit trust boundaries.

## Canonical actual arithmetic extraction

The successful arithmetic extraction selects the original `square` and the real
source `Gf64` trait implementation. It reaches unchanged `reduce`, `spread`,
`square` and the actual constants/trait dictionary. The fallback reduction loops
remain present. From this Lean directory:

```sh
python3 extraction/canonical-arithmetic/run.py \
  --charon /path/to/pinned/charon \
  --aeneas /path/to/pinned/aeneas --label regenerated
```

The trait selector is
`{impl bulksketch::field::BinaryField for bulksketch::field::Gf64}`.
It starts at the first path segment, without a crate prefix. The runner checks
all native/build-input fingerprints and tool source pins, rejects incomplete
LLBC and preserves tool commands, logs, binary hashes and generated files.

The committed canonical Types/Funs are copied byte-for-byte into
`bridge/Arithmetic`. Its missing standard array iterator primitives use concrete
remaining-sequence models, with source correspondence and ownership/drop
semantics explicitly trusted. Generic BITS=64 refinement and the unconditional
actual-Gf64 refinement refer to the same source body. The canonical extraction
avoids duplicate generated declaration names across separate spread/reduce
packages; [migration-receipt.json](canonical-arithmetic/migration-receipt.json)
records exact-name body comparisons and the pinned import-only migration.

The initial full-native extraction remains incomplete and is not a successful
certificate. The earlier monomorphization experiment encountered incompatible
Charon/Aeneas preset requirements; the canonical route keeps the original generic
body and uses its actual extracted instance instead. No source branches or IR
metadata were removed to bypass a limitation.
