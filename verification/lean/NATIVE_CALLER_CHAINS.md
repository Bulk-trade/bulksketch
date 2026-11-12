# Native x86 callers and the degree-3/4 certificate

The frozen scope retains 344 executable native declarations. The associated
verification record contains 82 original Aeneas generated-body refinements and four separate
source-linked stateful LLBC contracts. Production Rust is unchanged.

## Scalar PCLMUL

Seven original bodies cover the scale-XOR and square helpers and their
Arithmetic entry methods, the BulkKernels XOR entry, and the Horner helper
and its BulkKernels entry. The slice proofs cover the zero and unit branches,
the carryless multiply paths, common-prefix effects, and the original
mismatch guards. The Horner proof follows the original nested loops and
low-register carryless recurrence, including empty coefficients and
mismatched output lengths. These proofs use the recorded XMM value and
standard-library iterator models. The Horner extraction reuses the
checked ended shared-scalar matcher under its own original-LLBC receipt.

## Stateful AVX-512 callers

The XOR assignment and difference projectors bind the exact Rust spans,
LLBC artifacts, target and typed control flow. Their normal-path execution
uses mapped bytes, explicit write permissions and separate source and
destination ranges. XOR assignment requires equal source and destination word
counts. Difference requires equal local and destination word counts and eight
remote bytes per word. The original XOR assignment writes each expected word
and preserves every byte outside the destination. The original difference
writes local XOR little-endian remote words and returns true exactly when a
word differs. Its loop advances by eight, uses the source tail mask for the
last block and accumulates the bitwise OR of all block differences before
the final self test. The invariant covers every prefix and the zero-length
case. The self test models the nonzero lane predicate of VPTESTMQ.
[Intel instruction reference](https://www.intel.com/content/dam/develop/external/us/en/documents/319433-024-697869.pdf)

The caller proofs compose the two previously checked masked-memory LLBC
primitives. They are separate from original Aeneas generated-body credit.
The address model uses natural-number byte addresses within admitted views.
Rust allocation/provenance, address representability, concrete intrinsic
correspondence and the higher-level backend entry methods remain separate.

## Native decoder certificate

The original degree-3/4 verifier extracts with the checked ended-projector
leaf matcher. The rule preserves identical unmarked leaves of equal type
and symbolic ID with empty consumed and borrowed descendants. The scoped
variant receipt binds the original LLBC, generated output, rejection without
checks, and the negative leaf controls.

The exact generated wrapper checks wrong length, zeros and duplicates.
Valid candidates produce the rebuilt coefficient prefix while preserving
the scratch suffix. Under the exact GF64 multiplication callback, size
representability and path-conditional scratch capacity, acceptance holds
exactly when the factor length is the root count plus one, the roots are
nonzero and pairwise distinct, and the ascending factor polynomial equals
their monic product in the quotient field. The polynomial characterization
uses the same original certificate body.

## Reproduction and related proofs

Run `python3 scripts/verify_all.py` from this directory after setting up the
pinned toolchain. The aggregate gate checks frozen exact-type challenges,
transitive axiom dependencies, both proof replays and negative controls.
Projector receipts preserve the original extraction commands and hashes.

The related proofs cover Dense multiplication, Portable Horner, the native
rebuilt verifier, its Portable seed composition and its locator construction.
The original reconstruction control recorded a context-join failure on pinned
Aeneas. The checked ended-projector variant extracted the original wrapper and
both loops with workspace admission modeled as an external call. The
[reconstruction proofs](NATIVE_RECONSTRUCTION.md) document the loop, wrapper and
admission contracts; [locator](NATIVE_BM_LOCATOR.md) and
[root traversal](NATIVE_ROOT_RUN.md) proofs cover the associated decoder stages.
The [Portable theorem](README.md) composes ordinary no-hint decoding under
explicit input and resource assumptions. Public admission, shared-job accounting,
hint/V3 routes, accelerated end-to-end execution, physical memory and
compiler-to-ISA correspondence remain broader obligations.
