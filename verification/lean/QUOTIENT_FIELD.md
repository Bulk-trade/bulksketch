# Word representation, algebra trace and source inversion

This records the earlier quotient-field checkpoint. The subsequent
[native coverage checkpoint](NATIVE_COVERAGE.md) closes the enclosing inversion
wrappers listed as open below using an explicitly reviewed, checks-enabled
frontend variant. The original failing extractor evidence remains preserved.

The native source remains revision
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`. This checkpoint adds proof and checking
artifacts; it changes no native Rust, build input or runtime operation.

## The exact field and its word representation

[WordSpec.lean](bridge/BulksketchBridge/Algebra/WordSpec.lean) interprets a word
as the polynomial whose coefficient of `X^i` is bit `i`. Its target is Mathlib's
`AdjoinRoot (X^64 + X^4 + X^3 + X + 1 : Polynomial (ZMod 2))`. The field instance
uses the earlier proved irreducibility theorem; native arithmetic laws are not
assumed to construct it.

[Word.lean](bridge/BulksketchBridge/Algebra/Word.lean) proves every coefficient,
including all indices outside the word width, and preserves zero, one and XOR.
Strict degree bounds give injectivity: a nonzero difference of two canonical
representatives has degree below 64 and cannot be divisible by the modulus.
[WordEquiv.lean](bridge/BulksketchBridge/Algebra/WordEquiv.lean) proves surjectivity
from that injectivity and independently proved cardinality `2^64` on each side.
The forward map of the resulting equivalence is the actual polynomial map.

[WordOps.lean](bridge/BulksketchBridge/Algebra/WordOps.lean) interprets the complete
128-bit carryless product as ordinary polynomial multiplication. A bounded
widening shift is multiplication by `X^i`; every prefix of the convolution is
proved. The complete modulus multiple retains all coefficients through degree
127. Mapping the earlier division certificate into the quotient proves exact
reduction and multiplication for every word pair.

[WordSquare.lean](bridge/BulksketchBridge/Algebra/WordSquare.lean) proves the
polynomial square coefficient by coefficient using polynomial expansion in
characteristic two. [WordLaws.lean](bridge/BulksketchBridge/Algebra/WordLaws.lean)
then transports associativity, commutativity, identities, distributivity over
XOR and square-as-self-product through the injective map. Ordinary numeric
BitVec multiplication and addition are never substituted for field operations.

## Transport to the existing Mathlib algebra trace

[TraceSpec.lean](bridge/BulksketchBridge/Algebra/TraceSpec.lean) proves dimension
64 and cardinality `2^64` for the exact quotient. Mathlib's finite-field theorem
expresses `Algebra.trace` as the sum of the 64 binary conjugates.
[Trace.lean](bridge/BulksketchBridge/Algebra/Trace.lean) transports every repeated
square and the independently specified word conjugate sum to that formula.
Thus the original selector `bit61 XOR bit63` is the actual scalar algebra trace.

[WordNative.lean](bridge/BulksketchBridge/Algebra/WordNative.lean) composes the
unchanged generated reduction, multiplication, square and Frobenius bodies with
these results. The Frobenius theorem covers every native U32 power and denotes
the full exponent `2^power.val`; the original modulo-count source loop is
justified by the earlier word-period theorem.
[TraceNative.lean](bridge/BulksketchBridge/Algebra/TraceNative.lean) gives both
actual trace functions normal returns on every U64 input. Their complete output
byte is bounded by one before being identified with the scalar trace. Equality
only after casting an arbitrary byte to `ZMod 2` would be weaker and is not the
contract used here.

## The original inversion body

[Inverse.lean](bridge/BulksketchBridge/Inverse.lean) verifies the actual extracted
`inverse_with_frobenius`, including its zero and unit early returns, original
reverse iterator, each of five iterations, terminal iterator result and every
scalar operation. Reachable chain indices are `1, 3, 7, 15, 31, 63`; the remaining
range length strictly decreases. The target's leading-zero count, subtraction,
shift bounds, doubling and increment are all checked.

[InverseMath.lean](bridge/BulksketchBridge/InverseMath.lean) proves the prefix
meaning `t_k = a^(2^k - 1)`. The final square reaches `a^(2^64 - 2)`.
[InversePower.lean](bridge/BulksketchBridge/Algebra/InversePower.lean) identifies
this exponent with Mathlib's total field inverse using the proved quotient
cardinality and field power period. Its zero case is handled explicitly.

[InverseNative.lean](bridge/BulksketchBridge/InverseNative.lean) proves normal
return of `None` exactly for zero and otherwise `Some` of the unique word
representing the Mathlib inverse. The generic API has explicit universal
callback contracts. The field theorem requires the supplied callbacks to equal
the actual native multiplication and Frobenius on every argument, whose
normality and field meaning are proved. A separate closed `BuiltinFn` instance
supplies those native functions and discharges both callback premises.

The three generated inversion declarations are copied byte for byte from the
successful original extraction. The strict
[projection check](extraction/inverse-chain/project.py) also checks every shared
type and Gf64 dictionary against the existing arithmetic extraction. Eight
mutation fixtures test rejection in ordinary and optimized Python. The original
generated files remain untouched. No new runtime model is introduced.

## Remaining inversion wrappers and full native scope

The enclosing `inverse_using` captures a shared borrow of its square callback.
Pinned Aeneas cannot join the resulting nested shared loans across that loop.
Both loop extraction modes and isolated optimized-MIR attempts were investigated
without changing native code; none yielded a usable enclosing-wrapper proof.
[The investigation](audit/inverse-enclosing-translator-investigation.md) records
the exact guard, evidence and requirements for a separately reviewed frontend
fix. `inverse_using` and its `inverse` caller receive no new proof credit.

This checkpoint strengthens six earlier native endpoints in place and adds one
source-body refinement for `inverse_with_frobenius`: fifteen distinct bodies
under the stated translation/runtime/compiler/machine trust boundary. Loop
helpers, field lemmas, equivalences and extraction artifacts add no Rust-body
credit. All 344 native executable obligations remain in scope. X86 lookup and
table generation, accelerated arithmetic, general decoder completeness, public
state/resource/ownership behavior and compiler-expanded closure remain open.
Full native coverage is false and no percentage is claimed.

## Independent checking and native behavior

Every earlier frozen proposition is retained. New fixed propositions are
cross-reviewed, pinned and compared to theorem types before export. All project
theorem axiom closures are checked, and the original exported terms are replayed
through Lean and independent Nanoda. Only `propext`, `Quot.sound` and
`Classical.choice` are permitted. Existing replay time limits remain unchanged.

The native implementation and build inputs are byte-identical to the baseline,
so this is a proof milestone with no native performance change. The local native
release regression suite passed all 139 tests. Runtime benchmarking lives in
the excluded oracle crate and is not used as evidence of a performance gain.
Proof-checking timings are recorded separately from runtime behavior.
