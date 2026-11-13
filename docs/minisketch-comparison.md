# bulksketch and minisketch

[minisketch](https://github.com/bitcoin-core/minisketch) by Pieter Wuille, Greg
Maxwell and Gleb Naumenko is the reference implementation of PinSketch.
bulksketch implements the same construction for one field, GF(2^64), in Rust,
and changes how a sketch is organised and how it is decoded. This page lists
what is the same, what bulksketch adds, and what minisketch offers that
bulksketch does not.

No minisketch code is part of this repository. Earlier revisions held a
test-and-benchmark crate that compared the two libraries; it is kept in the
git history (see the last section). The library sources in `src/` have not
changed since then.

## What is the same

- **The sketch.** A sketch of capacity `c` stores the `c` odd power sums
  `S1, S3, ..., S(2c-1)` of the set's elements in GF(2^64). bulksketch uses
  minisketch's 64-bit field (modulus `x^64 + x^4 + x^3 + x + 1`), so for a
  one-bucket sketch the stored syndromes are byte-for-byte minisketch's
  serialized sketch. The comparison tests checked this for every capacity from
  1 to 89.
- **The guarantee.** If two sets differ in at most `c` elements, the difference
  is recovered exactly. (minisketch cannot hold the element 0, so there this is
  about nonzero elements. In bulksketch it holds per bucket, when the decode's
  output allowance covers the difference and it is given the work and scratch
  limits from `DecodePlan::complete_bound`.)
  Beyond `c` the sketch no longer identifies the difference; see "Beyond
  capacity" in the README.
- **The outline of decoding.** XOR the two sketches, find the error-locator
  polynomial with Berlekamp-Massey, find its roots.

## What bulksketch adds

| | minisketch | bulksketch |
|---|---|---|
| Work per decode | no explicit operation budget; the caller limits work through the capacity and the number of elements it asks for | every request runs under a caller-set work budget and stops with the error `WorkLimitExceeded` when it would exceed it |
| Memory during decode | allocates as needed | one scratch arena, sized in advance by `DecodePlan::complete_bound`; no allocation during decode |
| Result check | returns the roots it finds | every returned row is checked against all stored syndromes before it is returned |
| Buckets | one sketch | a sketch has a power-of-two number of buckets (`id % buckets`); each bucket decodes or fails on its own |
| Element 0 | cannot be stored | stored through a separate membership bit, so every `u64` is a valid ID |
| 1 or 2 differences | Berlekamp-Massey, then linear and quadratic factors are solved directly | solved from `S1` (and `S3`) before Berlekamp-Massey, then verified |
| 3 or 4 differences | Berlekamp-Massey, then trace-based root finding | closed-form cubic and quartic solvers (plan V3), then verified |
| Root finding | Berlekamp trace algorithm with a random basis per sketch | trace splitting along directions derived from a caller-supplied seed, or (plan V3) roots from the least affine multiple of the locator |
| Known candidates | none | the caller may pass IDs it expects in the difference; confirmed ones are divided out before root finding |
| Decoding many rows | one sketch per call | one call decodes a batch of rows with one arena; a `DecodeJob` can also run stage by stage |
| Arithmetic | portable or CLMUL, chosen when the sketch is created | portable, PCLMUL or VPCLMUL with AVX-512, chosen at runtime; forced backends are tested to give identical results and work counts |
| Untrusted input | caller checks lengths | parsing takes explicit limits (`ParseLimits`) and rejects non-canonical encodings |
| Language | C++ with a C API | Rust; `unsafe` only in the two x86-64 backend files; the library has no dependencies |
| Machine-checked proofs | none | Lean 4 proofs for the portable decoder (see "Proofs" in the README for their scope) |

Notes on the rows above:

- **The work budget counts operations, not time.** It caps what a hostile row
  can cost; it does not make that cost small. The bound that
  `DecodePlan::complete_bound` computes is deliberately conservative.
- **The seed matters.** With a known seed an attacker can choose IDs that make
  bulksketch's seeded root finding slow. Use a secret seed in production. See
  "Why the splitter seed should be secret" in the README.
- **Verification does not detect aliases.** Beyond capacity, a different set of
  at most `c` IDs can have exactly the same syndromes. No decoder can tell it
  from the real difference. Verification guarantees only that a returned set
  reproduces the sketch.

## What minisketch offers that bulksketch does not

- **Other field sizes.** minisketch supports elements of 2 to 64 bits, so
  sketches of short IDs are smaller. bulksketch supports 64-bit elements only.
- **A C API** and, through it, bindings for other languages.
- **Capacity helpers.** `minisketch_compute_capacity` and
  `minisketch_compute_max_elements` size a sketch for a target false-positive
  rate.
- **Age.** minisketch is the older, established implementation; bulksketch is
  new.

bulksketch's own encoding (`FrozenSketch::encoded_v1`) may still change, so do
not store it long-term.

## How the two were compared

The comparison crate is in the git history at
[`0a5bda5`](https://github.com/Bulk-trade/bulksketch/tree/0a5bda53f6b07fcae8acd870e2d0c4a246d207e6/oracle),
the revision the Lean proofs pin for `src/`:

- `oracle/tests/` built the same sets in both libraries and checked that the
  syndrome bytes are equal and that both decode to the same difference, for
  every capacity from 1 to 89, against minisketch's portable implementation
  (impl 0) and, on x86-64, its CLMUL implementation (impl 1).
- `oracle/benches/decode.rs` timed both on the same inputs. The README's
  "Recorded comparison harness" and "Performance" sections describe the cases
  and give the measured numbers.

That crate builds a vendored copy of minisketch with two small local additions
(described in the README) and needs a C++ compiler and libclang.
