# Original AVX-512 register kernels

The pinned Charon run targeted `x86_64-apple-darwin`. The checked,
unmodified Aeneas translator emitted all four raw Lean artifacts from
the original LLBC. Fresh Charon output matches the original LLBC apart
from the recorded destination path. Aeneas replay matches all four
raw Lean artifacts byte for byte. The retained declarations are the
original `raw`, `reduce_shift`, `reduce_cl`, `multiply`, and the
`reduce_shift` closure. The closure contributes to the enclosing
proof.

## Register semantics

The local model represents the 512-bit value as four 128-bit pairs.
Each pair has a low and high 64-bit word, in increasing bit-position
order. VPCLMULQDQ uses immediate bit 0 to select the first operand's
word and bit 4 to select the second operand's word in each pair. It
returns all 128 product bits. Low and high unpack operate separately
within each pair. Shifts are logical and word-local, with a count of
64 or greater producing zero. XOR and broadcast operate on the
complete bit pattern. [Intel instruction set reference](https://cdrdv2-public.intel.com/874240/325462-090-sdm-vol-1-2abcd-3abcd-4.pdf)

The pinned Rust source is the `nightly-2026-09-17` rust-src component.
Its `vpclmulqdq.rs:40` passes the validated byte to the vector CLMUL
builtin. In `avx512f.rs`, the shifts use unsigned word vectors, unpack
uses the exact eight-element shuffles, XOR operates over all 512 bits,
and broadcast splats the input bit pattern. The refinement receipt
records both source hashes.

## Complete outputs

- `raw` returns two vectors of four complete carry-less products.
  The first vector represents the even input lanes and the second
  represents the odd lanes.
- `reduce_shift` gives the GF64 remainder independently in each
  of the eight lanes for arbitrary low and high words.
- `reduce_cl` gives both words in each pair. The low word is the
  same remainder. The high word is the polynomial quotient, equal
  to the original high word XOR the first fold's overflow.
- Both values of `CL` in `multiply` return the same eight GF64
  product words. The proof checks that interleaving reconstructs
  the original lane order.

The Lean kernel checks the original projected bodies against these
models. The trust boundary includes correspondence of the scoped
intrinsic models to the pinned ISA and standard library. LLVM code
generation, runtime feature availability, masked memory and hardware
execution are separate. Release-mode x86-64 test targets were
cross-compiled on Arm.
