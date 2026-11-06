# Independent review of the original const Frobenius square

Reviewed 2026-11-06 by the Aeneas-capture agent, which authored none of these
proof, specification, extraction or source-projection files. Native source pin:
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`.

## Outcome and precise scope

No blocking semantic issue was found. The exact challenge quantifies every U64
input and concludes a normal return of the complete canonical word. It names the
actual source-generated `bulksketch.field.frobenius.square`; it does not assume
source success, a degree bound on the operand, field irreducibility, or the
correctness of a precomputed table.

The full `BulksketchBridge.FrobeniusConst` target was independently rebuilt
successfully. A separate Lean file assigns `square_refines` to the exact fixed
challenge and checks the transitive axioms of that endpoint, byte conversion,
both loop completions and final division meaning. Only the permitted standard
foundations occur. Root's aggregate checker supplies the independent exported-term
replay gate; this report does not substitute its local build for that gate.

## Mathematical and source review

- `spreadPrefix_bits` covers every processed count through 64 and every 128-bit
  coefficient. The source reads input bit 0 through 63 and writes even positions 0
  through 126. Its signed counter additions, multiplication by two, masks and
  shifts are normal and bounded; no field word is sampled or enumerated.
- The source initializes its division counter to 128, tests `bit > 64`, then
  decrements BEFORE inspecting the selected coefficient. The invariant matches
  exactly the resulting leading positions 127 down through 64, including the last
  cancellation at 64. Terminal counter 64 returns without another decrement.
- The shifted degree 64 modulus has a unique leading coefficient at 64+shift and
  no higher coefficient. For shifts 0 through 63 all polynomial coefficients fit
  in 128 bits. `divisionPrefix_upper` clears each selected coefficient while
  preserving the already-cleared suffix above it.
- `quotientPrefix` records the corresponding degree 63 through 0 monomials.
  `divisionPrefix_certificate` maintains the full input as current remainder XOR
  the exact untruncated modulus multiple. The final remainder's high 64 bits are
  zero. Existing division-certificate uniqueness then identifies its low 64 bits
  with the previously verified reduction fold. This holds for arbitrary 128-bit
  division inputs; it does not rely only on the spread square's zero bit 127.
- The composition uses `spreadPrefix_complete` to link to the independent raw
  polynomial square and `division_square_complete` to identify the original word
  square. The target is the complete output word, not merely low selected bits.
- The eight original byte reads are checked against the actual 16-byte little
  endian list. `low_bytes_refines` checks read bounds and proves all 64 output
  coefficients after rebuilding the low eight bytes. The dependent byte-width
  cast is erased explicitly before using `Array.make_val`; no unchecked numeric
  conversion or new byte model is introduced. Little endian conversion is
  explicit in the source, so this is not an inference from host endianness.
- The strict source projector was independently rerun successfully. Its complete
  Funs file is byte-identical to `Arithmetic/FrobeniusConstGenerated.lean`, with
  exactly 5 declarations: both original loop bodies, both loop functions, and the
  single source function. The generated Types file declares no application types.

## Source and trust boundary

The extraction uses the original pinned Charon/Aeneas tools and the original
source with `--target x86_64-apple-darwin`, which exposes the cfg-gated module.
This does not claim x86 execution on the Mac or verify PCLMUL/VPCLMUL instructions.
The source projection and extraction receipt record that target and its original
LLBC and generated hashes. The separate immutable-capture frontend patch is not
used by this const-square extraction.

Only ONE additional native body may be credited for this endpoint. Four loop
helpers are part of that body's proof, not separate Rust-function coverage.
`tables`, `inverse21_table`, the lookup functions, accelerated backends and
compiler/runtime/machine correspondence remain distinct obligations. The proof
uses existing Aeneas scalar/array/byte semantics under the documented TCB; this
review does not formally verify Rust's standard library or the translator.
All 344 native executable obligations remain in scope.

## Independent local checks

- `lake build BulksketchBridge.FrobeniusConst`: exit 0.
- Exact challenge assignment and transitive-axiom checks for
  `square_refines`, `low_bytes_refines`, `spread_loop`, `division_loop`, and
  `divisionPrefix_complete`: exit 0.
- `python3 extraction/frobenius-const/project.py`: exit 0;5 verbatim declarations.

Build and axiom logs are external evidence under
`/Users/junbug/bulk/bulksketch-proof-tools/frobenius-const-review-{build,axioms}.log`.

## Reviewed hashes

| Path relative to verification/lean | SHA-256 |
| --- | --- |
| `bridge/BulksketchBridge/FrobeniusConstSpec.lean` | `68ae588ef8c0c8808c3feaa95550254fb4a511c434d8d0300e18d074000a6df4` |
| `bridge/BulksketchBridge/FrobeniusConstChallenges.lean` | `3b6d008cc28b54591230316749b45b42380d735bd3abad9d03c350eff12ddd4d` |
| `bridge/BulksketchBridge/FrobeniusConstMath.lean` | `62463a835c8ef3b3633e692da36698b20d9f159d8ac72ffad542e00639431a24` |
| `bridge/BulksketchBridge/FrobeniusConstSource.lean` | `7c4507d36f8d6c074ae4c8e30e39bebcb324b40e291550b8e052cc2b1be799b8` |
| `bridge/BulksketchBridge/FrobeniusConst.lean` | `e536bb8852d48ebfee0e94e5414e83806997f447b07067ca247db5578ff8678c` |
| `bridge/Arithmetic/FrobeniusConstGenerated.lean` | `840f09b2caaf3a369502fcaa724ecdd097f031c47e2abd950aba59bc25218d23` |
| `extraction/frobenius-const/project.py` | `0a3c7e4720e4cc8e35af198449aa2c8803d3938390fa61031c8a044ed8b59d2e` |
| `extraction/frobenius-const/square/receipt.json` | `507afdab619af5c9a1f06708f5ab78fc69c648b5fd4368c14ad52b0d0c363977` |
