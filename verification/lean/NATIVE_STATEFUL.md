# Native field maps, root recovery and masked-memory execution

The ledger retains all 344 executable native obligations from the frozen
source revision. The associated record contains 74 original Aeneas generated-body
refinements and separately records two checked source-linked LLBC execution
contracts.

## Stateful masked-memory paths

The checked projector reads the original x86 masked load and store LLBC.
It binds both exact Rust source spans, the x86 target and little-endian
metadata, local and operand types, Move and Copy operations, borrow and
pointer metadata, every call identity, and the return and unwind shape.
It emits typed instruction lists from the original normal paths. Nine
semantic mutations of the input are rejected in both ordinary and optimized
Python independently of the raw artifact hash. The aggregate gate also
rejects swapped load/store attribution and attempts to count the interpreter
program as an Aeneas body.

The scoped interpreter carries the byte heap, borrowed view and permissions.
For an admitted mapped slice, the original load instructions return exactly
the active words in their register positions, zero the inactive lanes and
preserve the heap. For an admitted writable mapped slice, the original store
instructions return Unit and the updated heap. Reading the restored caller
view gives the exact low register payload, with every address outside the
slice preserved.

These are the two separately audited LLBC contracts. They compose the prior
source mask proof and byte-memory instruction models. The
[native caller proofs](NATIVE_CALLER_CHAINS.md) document the associated vector
callers under their memory contracts. Physical address and pointer provenance,
real intrinsic correspondence and accelerated end-to-end execution remain
broader obligations. The recorded pure Aeneas obstruction still applies to its
original external signatures.

## Accelerated scalar field maps

The original PCLMUL Frobenius helper and its Arithmetic entry method cover
every U32 count. The exact table hit and repeated-square fallback both
produce the full Frobenius iterate by the period theorem. The original
quadratic solver and its entry method prove trace rejection, the hardware
square assertion, and the exact normalized quadratic option.

The original PCLMUL inverse and its Arithmetic entry method return None
for zero and the represented field inverse otherwise. The original unit
guard returns one. The fast branch checks the exact fixed map lookups and
the original chain through t2, t3, t6, t7, t14, t21, t42 and t63. Its final
square raises the input to the field inverse exponent 2^64 − 2. The map7
closure and polynomial transport add zero duplicate source-body credits.

## Feature gate and cubic recovery

The original AVX-512 detector reads modeled CPUID leaf 1 and leaf 7 register
observations. Its result requires the original CPU capability bits and the
five required XCR0 state bits. The proof establishes that XGETBV is reached
only when the original XSAVE and OSXSAVE guard holds. The support helper
returns the exact conjunction of the CPU and OS predicates. Actual CPUID
register correspondence, the OnceLock availability cache, and backend
dispatch are separate obligations. [Intel AVX-512 detection reference](https://cdrdv2-public.intel.com/843827/253665-sdm-vol-1-dec-24.pdf)

The original degree-three/four quadratic helper returns the exact normalized
quadratic option under the stated GF64 callback equations. The original
cubic helper terminates normally under its callback contracts, and every
word in a returned array is a root of the input monic cubic. A returned
array requires the caller's acceptance checks, and the theorem permits a
`None` result. The [quartic](NATIVE_QUARTIC.md) and
[closed-leaf](NATIVE_CLOSED_LEAF.md) proofs cover the associated recovery and
certification contracts. The helper theorem alone is not a decoder-completeness
result; the [Portable theorem](README.md) states that result with its admission
and resource assumptions.

The recorded isolated BM extraction accepted a checked mutable expansion with
an unrelated owner and exact leaf children, then reached an enum case containing
a fresh mutable word borrow in the original prefix-scaling loop. The
reconstruction record contains a loop-backedge mismatch. These diagnostic
translator configurations are outside the admitted proof pipeline; the
[BM locator](NATIVE_BM_LOCATOR.md) and [reconstruction](NATIVE_RECONSTRUCTION.md)
documentation describe the function-body proofs.
