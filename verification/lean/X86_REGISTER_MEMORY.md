# Native x86 register kernels and masked-memory boundary

The [stateful LLBC proofs](NATIVE_STATEFUL.md) cover the associated masked-memory
execution contracts.

The associated record contains 64 original generated-body refinements under the
recorded extraction and runtime boundary. All 344 executable obligations
from the frozen native source revision remain in the ledger.

## Scalar PCLMUL

The original signed and unsigned native-endian byte conversions preserve all
64 bits on the x86 target. The XMM move puts that word in the low half and
zeroes the high half. The original words method reads the low half directly
and the high half after an eight-byte shift. The low-low carryless selector
and both reads return the entire polynomial product. The proof reaches
the original Pclmul raw multiply, multiply and square entry methods.

For the carryless reduction branch, the first product multiplies the high
word by the low modulus 0x1b. Its low word is the first fold and its high
word is the overflow of that fold. The next product folds that overflow
once more, with zero high word. XOR with the input gives the canonical
remainder in the low word and the exact quotient word in the high half.
The fallback calls the already verified original GF64 reducer and
zero-extends its result. Both original multiplication modes return the
same GF64 value.

The register and immediate definitions are grounded in the pinned
Rust stdarch source and Intel instruction descriptions. They state the
register value semantics used by these source refinements. Feature dispatch,
code generation, and physical instruction execution retain their separate
obligations. [Intel instruction reference](https://cdrdv2-public.intel.com/782151/253667-sdm-vol-2b.pdf)

## AVX-512 register kernels

The eight 64-bit words are represented as four 128-bit pairs. The original
raw function produces the complete products of the even and odd words in
separate registers. The original shift reducer computes the canonical GF64
remainder independently in all eight lanes. The carryless reducer preserves
the exact low remainder and high quotient in each of its four pairs.
Both original multiply branches unpack those results into the same eight
field products in their original lane order.

## Masked memory

The original extracted pure store returns the slice from as_mut_ptr before
the raw-pointer write. Its external store binding returns Result Unit.
The proof quantifies over all bindings with those signatures and shows
that two successful stores of different register values return the same
slice. Even a one-word destination requires a result that depends on the
new lane value.

At fixed length and mask, the original extracted pure load passes only a
single 64-bit pointer payload to its load binding. Exact reading of two
arbitrary words would require an injection from 128 bits into 64 bits.
The Lean proof rules out that injection. Both obstruction proofs use
verbatim bodies and earn zero source-refinement credit.

The separate executable byte-memory model checks all enabled addresses,
zeroes inactive load lanes, writes only enabled bytes, preserves the
remaining memory, and reads back the exact written payload. It proves
the correspondence between flat lanes and the register pairs. Its
prefix theorems use the original verified lane mask. Linking these
theorems to the actual masked source methods requires a heap effect or
verified writeback lowering, then machine address, pointer provenance and
intrinsic correspondence.

## Decoder and memory scope

The original cube-root helper checks all ten iterations and returns a
nonzero cube root exactly when one exists, under the explicit GF64
multiply, square and Frobenius callback equations. The proof gives the
exact chain exponent (2^64 + 2) / 9.

The recorded Berlekamp–Massey extraction reached a mutable reference
expansion in the prefix scaling loop after clearing the normalization
match. The obstructing projector belongs to an unrelated symbolic owner,
but the expansion is mutable, so the existing checked shared-owner rule
leaves its guard in place. That extraction is outside the admitted proof pipeline. The recorded
reconstruction extraction reaches its mandatory loop-backedge match.
[Reconstruction](NATIVE_RECONSTRUCTION.md), [locator](NATIVE_BM_LOCATOR.md) and
[Portable decoder](README.md) proofs document the corresponding source
contracts. Accelerated end-to-end memory paths and compiler-expanded closure
are outside these register proofs.
