# Exact 128-bit native multiplication

The source remains `src/field/gf64.rs` at the pinned native revision. The
original two loops, assertion and output casts are present in the unedited
generated `bridge/Arithmetic/Funs.lean`. No replacement multiplication routine
is used to discharge the generated-body contract.

## Independent mathematical product

Interpret bit `i` of a word as the coefficient of `X^i` over GF(2). For all
64-bit operands `a,b`, the unreduced product is

`C(X) = XOR[j=0..63] (b_j * X^j * A(X))`.

[CLMulSpec.lean](BulksketchProofs/Field/CLMulSpec.lean) defines that XOR of widened
shifts and independently defines coefficient convolution. The coefficient of
`X^k` is the XOR of `a_(k-j) AND b_j` with the explicit guard `j <= k`; natural
subtraction must not alias a negative index to zero.

[CLMul.lean](BulksketchProofs/Field/CLMul.lean) proves equality at every one of
the 128 output positions and proves that every mathematical coefficient at
index 127 or above vanishes. Since both operands have degree at most 63, the
degree is at most 126. Thus retaining 128 bits loses no polynomial coefficient.
Operands are universally quantified; no enumeration of operand pairs occurs.

## First original loop: construct the nibble table

For nibble `i`, let `N(a,i)` be the four-term carryless multiple selected by its
bits. Clearing its lowest set bit gives the source recurrence

`N(a,i) = N(a, i & (i-1)) XOR (widen128(a) << ctz(i))`.

[NibbleTable.lean](BulksketchProofs/Field/NibbleTable.lean) proves this for all
input words. It enumerates only the fifteen possible nonzero nibble indices.
The cleared index is strictly smaller than `i`, and the trailing-zero count is
below four.

[RawMulTable.lean](bridge/BulksketchBridge/RawMulTable.lean) maintains that every
table entry before the range start is exactly `N(a,index)`. Unused tail values
are unrestricted. The real zero initialization establishes the prefix at one.
Each original body reads an earlier initialized entry and extends the prefix
by its checked write. Total correctness uses the decreasing measure
`16 - range.start.val`, including the source's terminal `None` case.

## Second original loop: consume four coefficients at a time

[RawMulAccum.lean](bridge/BulksketchBridge/RawMulAccum.lean) tracks a source
iterator at `4*k` and the complete product using exactly the first `4*k` right
operand bits. The independently proved block identity is

`prefix(4*(k+1)) = prefix(4*k) XOR (N(a, nibble(b >> (4*k))) << (4*k))`.

The source body therefore adds exactly the next four polynomial terms. Its
suffix proof decreases `16-k` and unfolds the original loop one step at a time;
it does not replace the source loop with an unrolled implementation. At `k=16`
the source iterator returns `None` before either shift is attempted.

| Source operation | Checked bound or exactness |
| --- | --- |
| First range index | `1 <= i < 16`; increment reaches at most 16 |
| `i - 1` | No unsigned underflow |
| Cleared-bit table read | `i & (i-1) < i < 16` |
| General trailing-zero primitive | Exact count, including zero; the nonzero nibble caller specializes to `< 4` |
| Widened first-loop shift | Count `< 4 < 128`; U64 widening preserves all bits |
| First-loop table write | Index `< 16`, preserving all previous entries |
| Second range shift | `4*k <= 60`, hence below both 64 and 128 |
| Masked table index | Below 16; cast to either supported pointer width is lossless |
| Final iterator state | Stops at 64 before a shift by 64 |
| Final U128 shift | Shift by 64 is below 128 |
| Output casts | Exact low/high halves; rejoining equals the original 128-bit product |

## Whole-source composition

[RawMul.lean](bridge/BulksketchBridge/RawMul.lean) proves that every pair of U64
operands returns the exact low/high pair, with no assumes-success or
canonicality premise. It uses the real extracted Gf64 dictionary, both source
loop theorems, the actual guard and the final casts. Its coefficient endpoint
connects every output bit directly to convolution.

The actual `mul` theorem composes raw multiplication with the existing Gf64
reduction theorem. Its complete raw polynomial equals the widened U64 remainder
XOR the displayed modulus multiple. This is a polynomial-division certificate;
modulus irreducibility remains a separate obligation.

The additional [Frobenius proof](bridge/BulksketchBridge/Frobenius.lean) covers
the original guard, U32 remainder and bounded repeated-square loop for every
word/power. It specifies exactly `power % 64` independent polynomial squarings.
A period-64 identity and an unmodded exponent interpretation are not assumed.

## Evidence and limits

Frozen statements, transitive axiom audits and Lean/Nanoda replay apply to the
complete proof set, including both original loop proofs and all new primitive
property lemmas. The [replay loader notes](bridge/README.md) describe the
scheduling-only repair for the pinned Lean string-literal replay bug and its
negative regression cases. No mathematical goal or original export is weakened.

Charon/Aeneas translation, concrete standard-library/intrinsic value-model
correspondence, production compilation, memory/ownership representation and ISA
execution remain explicit trust boundaries. All 344 native executable
obligations remain in the ledger. These arithmetic refinements do not establish
whole-native coverage, decoder completeness or x86 backend verification.
