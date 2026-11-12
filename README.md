# bulksketch

A set-reconciliation sketch in pure Rust: PinSketch (the BCH-code construction
used by [minisketch](https://github.com/sipa/minisketch)) over GF(2^64).

Two parties each build a small sketch of their set of 64-bit IDs. From one
sketch of capacity `c` and its own set, the other party recovers the symmetric
difference of the two sets, as long as it has at most `c` elements.

- **Pure Rust, no dependencies.** The library's `[dependencies]` list is empty.
  Minisketch is used only by the test and benchmark crate in `oracle/`.
- **Bounded work per decode.** Every decode runs under a checked work budget
  (`DecodeLimits::max_work`); a decode that would exceed it stops with
  `WorkLimitExceeded`. `DecodePlan::complete_bound` computes a budget and a
  scratch size meant to cover any input of the given shape. The budget counts
  logical operations; it is not a wall-clock bound. It is also conservative:
  by our operation-count model, the complete budget is over 100 times the work
  of an honest full-capacity decode at capacity 18, and several hundred times
  at capacity 89. It caps the cost of a hostile row; it does not make that cost
  small.
- **Verified output.** A decoded row is checked against every stored syndrome
  before it is returned. A row that cannot be decoded within its budget is
  reported as `Failed`; no partial result of that row escapes.
- **Per-bucket decode.** A sketch can have many buckets (an ID goes to bucket
  `id % buckets`). Each bucket decodes or fails on its own.
- **Runtime-selected arithmetic.** A portable backend, a PCLMUL backend and a
  VPCLMUL/AVX-512 backend on x86-64, chosen at runtime (`BackendRequest::Auto`).
  The tests check that forced backends give the same results and work counts.
  `unsafe` code is confined to the two x86-64 backend files. Other targets,
  including AArch64, use the portable backend only.
- **Minisketch's row bytes, for now.** Today the syndrome payload of a
  one-bucket sketch is byte-for-byte a serialized 64-bit minisketch of the same
  capacity, and `decode_rows_into` accepts such rows directly. This is a current
  property, not a promise: the field, layout or wire format may change in a
  later version if that makes decoding faster or sketches smaller. The full
  encoding (`FrozenSketch::encoded_v1`) already adds its own header and is not
  minisketch's format.

License: TBD. `Cargo.toml` sets no `license` and `publish = false`. The vendored
minisketch sources in `oracle/` keep their own licenses (see
[Repository layout](#repository-layout)).

## Example

From `tests/readme_example.rs`:

```rust
use {
    bulksketch::{
        BackendRequest, DecodeLimits, DecodeOutcome, DecodePlan, DecodeRequest, DecodeScratch,
        Decoder, Gf64, MutableSketch, ParseLimits, ShapeLimits, SketchShape, SketchView,
        decode_into,
    },
    std::sync::Arc,
};

// One bucket of capacity 18: up to 18 differences can be recovered.
let capacity = 18;
let shape = Arc::new(
    SketchShape::<Gf64>::new(
        &[capacity],
        &ShapeLimits {
            max_wire_bytes: 1024,
            max_buckets: 1,
            max_capacity_per_bucket: capacity,
            max_total_syndrome_words: capacity,
        },
    )
    .unwrap(),
);

// Each side adds its IDs (nonzero u64 hashes) to its own sketch.
let mut alice = MutableSketch::new(shape.clone(), BackendRequest::Auto).unwrap();
let mut bob = MutableSketch::new(shape, BackendRequest::Auto).unwrap();
for id in [11, 22, 33, 44] {
    alice.toggle(id);
}
for id in [11, 22, 55] {
    bob.toggle(id);
}
let alice = alice.freeze();
let bob = bob.freeze();

// Bob sends his encoded sketch; Alice parses it under her own limits.
let wire = bob.encoded_v1().unwrap();
let remote = SketchView::parse(
    wire,
    &ParseLimits {
        max_wire_bytes: 1024,
        max_buckets: 1,
        max_capacity_per_bucket: capacity,
        max_total_syndrome_words: capacity,
    },
)
.unwrap();

// The plan computes a work budget and a scratch size that cover any input.
let plan = DecodePlan::v3();
let (max_work, layout) = plan
    .complete_bound(&[capacity as u16], &[Some(capacity)], capacity, 0)
    .unwrap();
let limits = DecodeLimits {
    max_output_per_bucket: capacity,
    max_candidate_inputs: 0,
    max_work,
    max_scratch_bytes: layout.total_bytes(),
};
// Use a secret splitter seed in production, a fixed one in tests and simulations.
let decoder = Decoder::new(BackendRequest::Auto, 0x1234_5678).unwrap();
let mut scratch = DecodeScratch::new(&layout).unwrap();

let report = decode_into(
    DecodeRequest {
        local: &alice,
        remote,
        candidates: &[],
        plan: &plan,
        limits: &limits,
    },
    &decoder,
    &mut scratch,
)
.unwrap();
// The symmetric difference, ascending and verified against every syndrome.
assert_eq!(
    report.outcome(0),
    Some(DecodeOutcome::Decoded { ids: &[33, 44, 55] })
);
```

Other entry points:

- `decode_rows_into` decodes a batch of independent one-bucket rows, each given
  as raw syndrome bytes (minisketch's serialized form), with one scratch arena.
- `DecodeJob` runs a decode one stage at a time (`next_stage`, `run_next`,
  `finish`), for callers that interleave decoding with other work.
- `candidates` passes IDs the caller expects in the difference; they can save
  work but never make the decoder accept an unverified result.

### Why the splitter seed should be secret

Root finding splits the locator polynomial along directions derived from the
`Decoder` seed. An attacker who knows the seed can choose IDs whose roots resist
those directions, so many split attempts fail. By our operation-count model,
such a crafted row costs around 20 to 25 times the work of an honest
full-capacity decode, in minisketch's algorithm and on our seeded root-finding
path. The work budget still caps it. With a secret seed, the worst an attacker
can easily force is about one honest full-capacity decode per row. Fixed seeds
are fine for tests and deterministic simulation.

### Beyond capacity

When a row holds more than `c` differences, the sketch no longer identifies the
set. Usually the decode fails. Sometimes another set of at most `c` IDs has
exactly the same syndromes (an alias). No decoder can tell that set from the
real one. In the oracle tests, random 64-bit IDs produced aliases only at
capacities 1 to 3, while small consecutive integers (which span small GF(2)
subspaces) produced them in 60 of 267 cases, up to capacity 89.

bulksketch returns only sets that reproduce every syndrome of the input, so it
never returns a set that is inconsistent with the sketch. The oracle tests check
this for every capacity from 1 to 89, and check that bulksketch returns the same
set whenever minisketch finds a consistent one.

## Tests

```sh
cargo test --workspace --release
```

This runs the library's own tests (unit tests, frozen vectors in
`tests/vectors/`, and a compile-fail check of the decode job's borrow rules
through `tools/check-ownership.py`, which needs `python3` and `rustc`) and the
minisketch comparisons in `oracle/tests/`:

- the payload of a one-bucket sketch equals minisketch's serialized bytes, for
  every capacity from 1 to 89 and sets below, at and above capacity;
- decoding matches minisketch impl 0 and impl 1 and the true difference for
  every capacity from 1 to 89 and every difference size up to the capacity, both
  with remote bytes made by minisketch and by bulksketch;
- beyond capacity, every returned set reproduces the sketch, and whenever
  minisketch finds a consistent set, bulksketch returns the same set;
- degree-3 and degree-4 rows on the closed-form path match minisketch.

The `oracle` crate builds minisketch from C++ source, so it needs a C++ compiler
and libclang (for `bindgen`). The library itself needs neither.

## Proofs

This repository contains Lean 4 proofs of the sketch mathematics and an
end-to-end correctness theorem for the original Portable GF64 decoder.
For two valid in-memory sketches representing finite ID sets `A` and `B`,
the theorem proves that the decoded IDs are distinct and form exactly
the symmetric difference `A △ B`, including ID zero.

### Theorem and assumptions

The [whole-sketch theorem](verification/lean/bridge/BulksketchBridge/PortableSketchEndToEnd.lean)
uses the original `FrozenSketch` payloads and assumes the following.

- Both sketches have the same shape with a positive bucket count, the required
  flattened storage length, and nonempty zero-word storage. Their odd syndromes
  and zero membership bits correctly represent their routed ID sets.
- Each bucket has positive capacity `c` within the format's 16-bit bound.
  Its difference contains at most `β` IDs, where `β ≤ c`. ID zero consumes
  an output slot when its membership differs.
- Each row has scratch storage satisfying the native workspace admission
  conditions and a live work meter with the explicit `rowWork` reserve.

The proof follows the original Portable XOR, `BinaryDecoder::begin`, and
`Execution::finish` calls on the ordinary decoder route with empty candidate
hints. It derives reconstruction, the Berlekamp–Massey locator, root recovery,
verification, and canonicalization from those premises. Bucket views, zero-ID
interpretation, and bucket-order assembly are defined in Lean. Scratch and
work assumptions are per row.

The supporting mathematics proves that capacity-bounded nonzero supports are
uniquely determined by their odd syndromes, and connects native GF64 arithmetic
to Mathlib's field representation. The
[row theorem](verification/lean/bridge/BulksketchBridge/PortableRowEndToEnd.lean)
and [verification guide](verification/lean/README.md) give the exact statements
and their scope.

### Verification

The proof checkpoint `d0155ee` passed all six audit gates, including frozen
statement and source checks, a transitive axiom audit, Lean kernel replay,
and independent Nanoda replay. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. The native release suite passed 139 tests.
The Rust source is pinned to `0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`.

```sh
cd verification/lean
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```

The connection to Rust uses pinned Charon/Aeneas translations and the recorded
standard-library models. The translation, models, and correspondence with the
production compiler and runtime are trusted. Broader verification work includes
establishing input validity through the public constructors and updates, wire
parsing, the shared request job and its aggregate work allowance, candidate-hint
and V3 routes, and accelerated backend execution and memory contracts.

## Benchmark

```sh
cargo bench -p bulksketch-oracle --bench decode
```

One Criterion benchmark compares bulksketch with minisketch impl 0 (portable)
and impl 1 (CLMUL, x86-64 only) on the same inputs:

| Case | Rows x capacity | Differences |
|---|---|---|
| `vote_16x18_total11`, `vote_16x89_total11` | 16 x 18, 16 x 89 | 10 to 12 per vote in total, routed to rows by `id % 16`, so most rows hold 0 to 2 and some are equal (the shape of the "full vote" rows under Performance) |
| `vote_16x18_d11`, `vote_16x89_d11` | 16 x 18, 16 x 89 | 11 in every row |
| `row_c18_d1`, `_d2`, `_d5` | 1 x 18 | 1, 2, 5 |
| `row_c89_d1`, `_d2`, `_d5` | 1 x 89 | 1, 2, 5 |
| `pressure_16x18` | 16 x 18 | 6 to 60 per row; half of the rows exceed capacity and fail |

Both libraries start from a prebuilt local sketch and the remote row bytes.
bulksketch decodes all rows in one `decode_rows_into` call; minisketch
deserializes each row into a reused sketch, merges the local sketch and decodes
it. Each case cycles through 32 different fixtures. Results are checked before
timing.

This is a plain single-process benchmark. It does not reproduce the method
behind the numbers below (64 fresh processes per cell, a pinned core,
percentiles over all calls), and its numbers will differ from them. Pin it to
one core for steadier results, for example `taskset -c 2 cargo bench ...`.

The vendored minisketch has two small local additions (a candidate-decode entry
point that the benchmark does not use, and a per-thread seeded generator for the
randomized basis instead of a `std::random_device` per sketch) and is compiled
with `-O3 -march=native`.

## Performance

In the tables below, a *vote* is one complete 16-bucket sketch from a peer,
compared against the local sketch: one call handles all 16 rows, and each row
decodes or fails on its own.

Measured on one core of an AMD EPYC 9575F (x86-64) server: 64 fresh processes
per cell, both libraries timed in the same process, minisketch compiled with
PCLMUL support. The inputs went through an application wrapper (not part of
this repository) that skips equal rows and calls `decode_rows_into` with plan
V3 on the remaining rows of minisketch-format bytes. Fixtures came from an
independent generator, not from production traffic. Times below about 410 ns
are at the resolution limit of the method. These are percentiles of selected fixtures, not a worst-case guarantee,
and other CPUs will give other numbers.

Speedup = minisketch time / bulksketch time (above 1 means bulksketch is faster).

| Case | vs impl 0 (portable), p50 / p99 | vs impl 1 (CLMUL), p50 / p99 |
|---|---|---|
| Full vote, 16 x 18, about 11 differences in total | 12.6x / 11.3x | 2.08x / 1.94x |
| Full vote, 16 x 89, about 11 differences in total | 20.4x / 18.1x | 2.46x / 2.24x |
| Vote with one differing row of 1 or 2 IDs | 5.2x to 7.0x (p50) | 1.08x to 1.26x (p50) |
| Vote with 3 or more differences (one row of 3 to 18 IDs, or 3 to 5 IDs spread over the rows) | 9.6x to 16.1x (p50) | 1.7x to 3.2x (p50) |
| Pressure fixture, 16 x 18 | 0.85x / 22.4x | not stated / 5.8x |
| Pressure fixture, 16 x 89 | 0.82x / 16.8x | not stated / 4.2x |

The row ranges cover ordinary fixtures at capacities 18 and 89; a few
special-case fixtures were faster still (up to 35x portable and 7.7x CLMUL at p50).

Where bulksketch is **not** faster, or only slightly:

- **Pressure fixture at p50: about 0.8x, so slower than minisketch's portable
  build** (481 vs 411 ns at 16 x 18). Its p99 is 17x to 22x lower than portable
  and 4x to 6x lower than CLMUL. This fixture replays per-row difference counts
  recorded under heavy load; at 16 x 18 many of its rows exceed capacity and
  fail.
- **A single differing row with 1 or 2 IDs: only 1.1x to 1.3x faster than
  CLMUL** at p50.
- Full 16 x 18 votes are just under 2x CLMUL at p99 (1.94x).

The work budget limits counted operations, not time.

### Reproducing the numbers

The timing tool behind this table is not in this repository yet. Its method:

- Both libraries (and minisketch impl 0 and 1) are linked into one release
  binary and given identical input bytes. Correctness is checked outside the
  timed region.
- The binary runs as 64 fresh processes, one after another, pinned with
  `taskset -c 2` on an otherwise idle host (no builds or other benchmarks).
- Within each process the libraries alternate in a random balanced ABBA/BAAB
  order per call: 1,600 calls per library per process, 5,000 for the
  smallest cases.
- Every individual call is kept. p50 and p99 are taken over all calls from all
  processes, with no overhead subtracted. An A/A pair (the same code timed
  twice) in every cell shows the noise level.
- The fixtures are frozen before timing.

To get comparable ratios with what is here, run the Criterion benchmark above
pinned to one idle core on an x86-64 CPU with PCLMUL, and compare ratios rather
than absolute times. Expect different numbers: the benchmark decodes every row,
including equal ones, and does not use the wrapper described above.

## Repository layout

| Path | What it is |
|---|---|
| `src/` | The library: field arithmetic and backends (`field/`, `backend/`), polynomials (`poly/`), Berlekamp-Massey, root finding and verification (`decode/`), and the sketch, wire format, scratch and request API (`sketch/`) |
| `tests/` | Integration tests and frozen vectors (`tests/vectors/`) |
| `tools/check-ownership.py` | Compile-fail check used by `tests/ownership.rs` |
| `verification/lean/` | Lean 4 proofs of the field arithmetic and work meter (see Proofs) |
| `oracle/` | Test-only crate (`publish = false`): minisketch comparisons (`oracle/tests/`) and the benchmark (`oracle/benches/decode.rs`) |
| `oracle/minisketch-rs/` | Vendored copy of the [minisketch-rs](https://github.com/eupn/minisketch-rs) binding (Apache-2.0, see its `Cargo.toml`) with the minisketch C++ sources (MIT, `oracle/minisketch-rs/minisketch/LICENSE`, copyright 2018 Pieter Wuille, Greg Maxwell, Gleb Naumenko) |

The toolchain is pinned in `rust-toolchain.toml`. `rustfmt.toml` uses options
that need a nightly rustfmt (`cargo +nightly fmt`).
