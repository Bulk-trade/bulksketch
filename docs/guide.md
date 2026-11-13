# A guide to bulksketch

This guide explains what bulksketch does, how to use it, and how to choose its
settings. It assumes you know Rust. It does not assume you know anything about
sketches, error-correcting codes or finite fields.

The code in this guide is shortened. Complete programs that compile and run
are in [`examples/`](../examples):

| Example | What it shows |
|---|---|
| [`reconcile.rs`](../examples/reconcile.rs) | Two peers find the IDs they do not share |
| [`buckets.rs`](../examples/buckets.rs) | A sketch with 16 buckets, and what to do when one bucket fails |
| [`untrusted_input.rs`](../examples/untrusted_input.rs) | Limits, errors and a secret seed for input from untrusted peers |
| [`staged.rs`](../examples/staged.rs) | Running a decode one stage at a time |
| [`raw_rows.rs`](../examples/raw_rows.rs) | Decoding many small rows from raw bytes in one call |

Run one with `cargo run --release --example reconcile`.

## The problem

Two machines each hold a large set of 64-bit IDs, for example hashes of
transactions or file chunks. The sets are almost the same: each machine has a
few IDs that the other lacks. They want to find those few IDs while sending as
little data as possible.

Sending the full list costs 8 bytes per ID. With 10,000 IDs that is 80 KB,
even if only five IDs differ.

A **sketch** solves this. It is a short summary of a set whose size depends
only on how many differences you want to be able to find, not on how many IDs
the set holds. One peer sends its sketch; the other combines it with its own
sketch and recovers the IDs that are in exactly one of the two sets (the
*symmetric difference*). In [`reconcile.rs`](../examples/reconcile.rs), a
sketch that can recover up to 18 differences takes 171 bytes, whether the set
holds ten IDs or ten million.

The catch is the **capacity**: you choose in advance how many differences a
sketch can recover. If the sets differ in more IDs than that, decoding usually
fails, and in rare cases it returns a wrong answer that the sketch cannot
detect. You need a capacity with headroom and a fallback for failures (see
[When there are too many differences](#when-there-are-too-many-differences)).

## How it works

You do not need this section to use the library, but it explains the names
you will meet in the API.

bulksketch implements *PinSketch*, a construction from coding theory, also
implemented by the C++ library [minisketch](https://github.com/bitcoin-core/minisketch).

- Each ID is treated as an element of a field with 2^64 elements, GF(2^64).
  In that field, addition is XOR, and multiplication is a fixed operation on
  64-bit words.
- A sketch of capacity `c` stores `c` numbers, called *syndromes*: the sums of
  the IDs, of their cubes, of their fifth powers, and so on, up to the power
  `2c - 1`. Each syndrome is a 64-bit word, so the sketch is `8 * c` bytes plus
  a small header.
- Adding an ID updates every syndrome. Adding the same ID again undoes it,
  because in this field `x + x = 0`. This is why the method that adds an ID is
  called `toggle`.
- Combining two sketches with XOR gives the sketch of the symmetric
  difference: the IDs both sets hold cancel out.
- *Decoding* turns those `c` power sums back into the IDs that produced them.
  The Berlekamp-Massey algorithm finds a polynomial whose roots are the
  unknown IDs, and a root-finding step recovers them. When there are at most
  `c` IDs, this recovers them exactly.
- ID 0 is a special case: every power of 0 is 0, so it would leave no trace in
  the sums. A sketch therefore stores one extra flag that records whether the
  set holds ID 0. When ID 0 is part of the difference, it is returned like any
  other ID and counts toward the number of IDs a bucket may return.
- Before returning a result, bulksketch recomputes every syndrome (and the
  ID 0 flag) from the decoded IDs and checks that they match. A result that
  does not match is never returned.

## Words used in the API

| Term | Meaning |
|---|---|
| ID | A `u64` in your set. Every value is allowed, including 0. |
| capacity | The most differences one bucket can recover. |
| bucket | A sketch can be split into several independent parts. An ID goes to bucket `id % buckets`. Each bucket has its own capacity and is decoded on its own. The API also calls a bucket a *row*. |
| shape | The number of buckets and the capacity of each (`SketchShape`). Two sketches can only be compared if their shapes are equal. |
| syndrome | One of the 64-bit words a sketch stores. A bucket of capacity `c` stores `c` of them. |
| `MutableSketch` | A sketch you can add IDs to. |
| `FrozenSketch` | An immutable snapshot of a sketch. Decoding and encoding use frozen sketches. |
| `SketchView` | A received sketch, parsed and checked in place, without copying. |
| decode | Recover the IDs in the symmetric difference of two sketches. |
| `DecodeOutcome` | The result for one bucket: `Equal`, `Decoded { ids }` or `Failed { reason }`. |
| plan | Which decoding algorithm to use (`DecodePlan::v3()` or `v2()`). Both recover the same IDs whenever a bucket holds at most its capacity of differences; they differ in speed and in how work is counted. Use `v3`. |
| work, `WorkUnits` | A count of the operations a decode performs. You set a maximum, so a hostile input cannot make a decode do unlimited work. It counts operations, not time. |
| scratch | Memory that the decoder works in (`DecodeScratch`). You allocate it once and reuse it, so decoding itself does not allocate. |
| seed | A number that steers how the decoder searches for roots. Keep it secret in production (see [The seed](#the-seed)). |
| backend | The arithmetic implementation: portable Rust, or faster x86-64 instructions when the CPU has them. `BackendRequest::Auto` picks the best available one. The results and work counts are the same with every backend. |

## A complete round, step by step

This follows [`reconcile.rs`](../examples/reconcile.rs).

**1. Agree on a shape.** Both peers must use the same number of buckets and
the same capacities. Here: one bucket of capacity 18. `ShapeLimits` caps how
large a shape may be; there is no unbounded default, so a mistake cannot
allocate gigabytes.

```rust
let shape = Arc::new(SketchShape::<Gf64>::new(&[18], &ShapeLimits {
    max_wire_bytes: 4096,
    max_buckets: 1,
    max_capacity_per_bucket: 18,
    max_total_syndrome_words: 18,
})?);
```

**2. Build a sketch of your set.** Toggle each ID once, then freeze.

```rust
let mut sketch = MutableSketch::new(shape, BackendRequest::Auto)?;
for id in my_ids {
    sketch.toggle(id);
}
let mine = sketch.freeze();
```

For many IDs at once you can use `toggle_batch` instead (see
[`buckets.rs`](../examples/buckets.rs)). Freezing is cheap: the snapshot
shares the data instead of copying it, and the data is copied only if you
change the mutable sketch again later.

**3. Send it.** `encoded_v1()` returns the bytes to send. The encoding is
computed once per snapshot and then cached.

```rust
let outgoing: &[u8] = mine.encoded_v1()?;
// ... send `outgoing` to the other peer, and receive theirs as `incoming` ...
```

**4. Parse what you receive.** Treat the other peer's bytes as untrusted.
`ParseLimits` says what you accept; anything larger or malformed is rejected.

```rust
let remote = SketchView::parse(&incoming, &ParseLimits {
    max_wire_bytes: 4096,
    max_buckets: 1,
    max_capacity_per_bucket: 18,
    max_total_syndrome_words: 18,
})?;
```

**5. Size the decode once.** `complete_bound` computes a work budget and a
scratch size that are enough for any input of your shape. Create the
`Decoder` and the `DecodeScratch` once and reuse them.

```rust
let plan = DecodePlan::v3();
let (max_work, layout) = plan.complete_bound(&[18], &[Some(18)], 18, 0)?;
let limits = DecodeLimits {
    max_output_per_bucket: 18,
    max_candidate_inputs: 0,
    max_work,
    max_scratch_bytes: layout.total_bytes(),
};
let decoder = Decoder::new(BackendRequest::Auto, secret_seed)?;
let mut scratch = DecodeScratch::new(&layout)?;
```

The four arguments of `complete_bound`, in order:

1. The capacity of each bucket, as in the shape.
2. One entry per bucket: `Some(n)`, where `n` is the third argument. Passing
   the same value for every bucket is always enough. (Internally, a bucket
   whose difference contains ID 0 has one slot fewer for other IDs; the
   `Option` exists for callers who size that case exactly.)
3. The most IDs a decode may return from any one bucket, ID 0 included. It
   applies to every bucket, so it can be at most the smallest capacity. To
   recover everything the sketch can hold, use the capacity. Put the same
   number in `DecodeLimits::max_output_per_bucket`.
4. How many candidate IDs you will pass in total, counting duplicates and 0
   (see [Optional: candidate IDs](#optional-candidate-ids)).

**6. Decode.**

```rust
let report = decode_into(
    DecodeRequest { local: &mine, remote, candidates: &[], plan: &plan, limits: &limits },
    &decoder,
    &mut scratch,
)?;
match report.outcome(0) {
    Some(DecodeOutcome::Equal) => { /* the two sketches are equal */ }
    Some(DecodeOutcome::Decoded { ids }) => { /* the symmetric difference */ }
    Some(DecodeOutcome::Failed { reason }) => { /* no verified result for this bucket */ }
    None => unreachable!(),
}
```

The decoded IDs are sorted in ascending order. They are the IDs that exactly
one side holds. To tell the sides apart, check each ID against your own set:
if you hold it, the other peer lacks it; otherwise you lack it.

`Equal` means the two sketches are identical. Within the capacity, that means
the sets are equal. `Failed` means this bucket could not produce a verified
result under the limits you set, most often because it holds more
differences than the capacity (or than `max_output_per_bucket`, if you set
that lower).

The report borrows the scratch memory. Drop the report before you reuse the
scratch for the next decode.

## Choosing capacity and buckets

**Capacity.** Pick it from the number of differences you expect between two
peers, with headroom. Each unit of capacity costs 8 bytes in every sketch you
send. The exact encoded size is

```
24 + 2 * buckets + ceil(buckets / 8) + 8 * (sum of all capacities)   bytes
```

so one bucket of capacity 18 is 171 bytes, and 16 buckets of capacity 8 are
1,082 bytes. Decoding work depends on the capacity as well as on the number of
differences; the README's [Performance](../README.md#performance) section has
measured times.

**Buckets.** With one bucket, more differences than the capacity usually
make the whole decode fail. Splitting the same total capacity over several
buckets limits the damage: an overloaded bucket usually fails on its own, the
others still decode, and the fallback only has to cover the failed bucket (the
rare wrong results described below apply to each bucket too). In
[`buckets.rs`](../examples/buckets.rs), one of 16 buckets fails and the peers
then exchange the IDs of that bucket only: about 1/16 of the set.

The cost is that differences do not spread perfectly evenly, so each bucket
needs some headroom of its own.

**Limits on the shape.** The number of buckets must be a power of two, at
most 32,768. A capacity is between 1 and 65,535. Very large shapes can be
valid but too large to plan for: `complete_bound` then returns
`DecodeError::WorkLimitExceeded`, because the work bound no longer fits in a
`u64`. Call `complete_bound` when you choose a shape, not only when you
decode.

**IDs should look random.** Buckets are chosen by `id % buckets`, which uses
the low bits of the ID. IDs that share their low bits (for example, IDs that
are all multiples of 16) crowd into a few buckets. Structured IDs such as
small consecutive integers also make the wrong results described below more
likely. Use a hash of your items as the ID.

## When there are too many differences

If a bucket holds more differences than its capacity, its outcome is usually
`Failed`. The `reason` says which check stopped it; for planning, treat all
reasons the same way: the bucket needs a fallback.

Rarely, an overloaded bucket gives a result that passes every check but is
wrong. This is a property of all sketches of this kind, not a defect of this
library: past the capacity, two different sets can have exactly the same
syndromes, and no decoder can tell them apart. For example, with capacity 1 a
sketch stores only the XOR of the IDs. Since `1 XOR 2 = 3`, the difference
`{1, 2}` has the same sketch as `{3}`, and the difference `{1, 2, 3}` has the
same sketch as no difference at all, so it decodes as `Equal`.

bulksketch only returns sets that match every stored syndrome, so a result is
always *consistent* with the sketches, but beyond the capacity consistency is
all it can promise. In tests, random 64-bit IDs gave such wrong results only
at capacities 1 to 3; small consecutive integers gave them more often, at
capacities up to 89.

What to do:

- Choose the capacity so that overflows are rare, and use hashed IDs.
- When a bucket fails, fall back: exchange that bucket's IDs directly, or
  send a sketch with a larger capacity for it.
- When the reconciled sets must be exactly equal, confirm it independently
  afterwards, for example by comparing a hash of each whole set. Checking the
  IDs a decode returned is not enough: it cannot reveal IDs that a wrong
  result left out.

## Untrusted input

bulksketch is built to decode sketches from peers that may be hostile.
[`untrusted_input.rs`](../examples/untrusted_input.rs) shows each defence:

- **Parsing.** `SketchView::parse` checks, in this order, the total size
  against `ParseLimits::max_wire_bytes`, the format, the number of buckets
  and capacities against the other limits, and finally the payload. Size and
  dimension problems give `ParseError::InputLimitExceeded`; format problems
  give `ParseError::InvalidEncoding`. Parsing does not allocate or copy.
- **Shape.** A sketch of a different shape gives
  `DecodeError::ShapeMismatch`.
- **Work.** Every decode counts its operations against
  `DecodeLimits::max_work`. When the next step would exceed it, the whole
  request stops with `DecodeError::WorkLimitExceeded`.
- **Memory.** Decoding uses only the scratch you allocated. A request that
  would need more fails with `DecodeError::ScratchTooSmall` before it starts.

There are two kinds of failure, and they behave differently:

- A **request error** (`Err(DecodeError)` from `decode_into`) returns no
  results at all, not even for buckets that finished before the error.
- A **bucket failure** (`DecodeOutcome::Failed`) affects only that bucket.
  The other buckets' outcomes are returned as usual.

The budget from `complete_bound` is deliberately generous: it covers the worst
case of every step. In [`reconcile.rs`](../examples/reconcile.rs), a decode of
five differences used 30,694 work units out of a budget of 35,497,822. You may
set a smaller budget if you measure your own workload, but then an unusual
input can fail the whole request with `WorkLimitExceeded`.

The work budget caps the number of operations. It does not promise that a
decode is fast; it promises that a decode cannot do more than that many
operations.

## The seed

The root-finding step splits a polynomial along directions derived from the
seed you pass to `Decoder::new`. An attacker who knows the seed can choose IDs
whose roots resist those directions, so the decode takes many more attempts
than usual (the README's "Why the splitter seed should be secret" gives
numbers). The work budget still caps the cost. A secret seed is a mitigation
against such tailored inputs, not a proven bound.

- In production, draw the seed from a random source when the process starts
  and keep it private. [`untrusted_input.rs`](../examples/untrusted_input.rs)
  shows one way with the standard library.
- In tests and simulations, use a fixed seed, so runs are reproducible. The
  seed can change how much work a decode takes; the tests check that, within
  the budget from `complete_bound`, it does not change the outcome.

## Optional: candidate IDs

If you can guess some of the IDs in the difference (for example IDs you saw
recently from that peer), pass them in `DecodeRequest::candidates`. When a
bucket needs the general algorithm, the decoder tests each guess against the
polynomial that the Berlekamp-Massey step found and removes the confirmed
ones before the root-finding step, which saves work there. Every candidate
also costs a little preprocessing, and buckets with few differences are
decoded by shortcuts that do not use candidates, so for small differences
candidates can increase the total work. A candidate is never returned unless
the sketch confirms it. Set `max_candidate_inputs` in the limits and pass the
same count to `complete_bound`; the count includes duplicates and 0.

## Advanced: staged and batched decoding

- **`DecodeJob`** runs a request one stage at a time instead of in one call.
  A stage is one phase of the algorithm, such as the whole Berlekamp-Massey
  step for a bucket, and runs to completion when you call `run_next`; stages
  are not time slices, and one stage can take much longer than another. The
  stages and their work counts are deterministic. See
  [`staged.rs`](../examples/staged.rs).
- **`decode_rows_into`** decodes many independent one-bucket sketches in one
  call, each given as raw syndrome bytes (8 bytes per unit of capacity,
  little-endian) without the encoding header. Raw rows have no ID 0 flag: the
  decoder assumes the remote set does not hold ID 0. If it does, the result
  for that row is wrong (an ID 0 held by both sides appears as a difference,
  and one held only by the remote side is missed). Keep ID 0 out of sets you
  exchange as raw rows. See [`raw_rows.rs`](../examples/raw_rows.rs).

## Performance tips

- Create one `Decoder` and one `DecodeScratch` and reuse them for every
  decode with the same limits.
- `toggle_batch` first sorts a batch of IDs into their buckets and then adds
  each bucket's IDs together, which can be faster than one `toggle` per ID.
- Build with `--release`. `BackendRequest::Auto` uses carry-less multiply
  instructions (PCLMUL, or VPCLMUL with AVX-512) when the CPU has them.
- When most comparisons are between equal sets, compare the encoded bytes
  first: equal sketches have equal bytes, and a byte comparison is cheaper
  than a decode.

## Compatibility

The encoding returned by `encoded_v1` may change in a later version. Both
peers should run the same version of bulksketch, and the encoding should not
be stored long-term.

## Further reading

- [README](../README.md): features, performance, and the Lean proofs.
- [How bulksketch compares with minisketch](minisketch-comparison.md).
- [SECURITY.md](../SECURITY.md): what the library defends against and how to
  report a problem.
- The API reference: run `cargo doc --open` in this repository.
