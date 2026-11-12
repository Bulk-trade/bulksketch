# Exact modulus irreducibility analysis

Analysis date: 2026-11-04. Current file fingerprints are recorded in `audit/frozen-inputs.json`. The recorded targeted build completed 2,095 jobs. The axiom log contains only `propext`, `Classical.choice` and `Quot.sound` for the exact literal root and supporting modulus, Frobenius, Bézout and final square-certificate roots. Aggregate exported-term replay is separate from this source argument.

## Goal and assumptions

The final exactPolynomialIrreducible root has the independently frozen literal proposition Irreducible(X^64+X^4+X^3+X+1 : Polynomial(ZMod2)). modulus is exactly that expression. No extra hypothesis, ambient modulus irreducibility instance, or assumed field structure on its quotient is present. The coefficient field ZMod2 is the ordinary independently known two-element field; that is a legitimate coefficient assumption, not the desired quotient-field result.

## All certificate data are checked

ModulusCertificates.lean contains65explicit candidate remainder polynomials and64unconditional adjacent identities R_i^2+modulus*q_i+R_(i+1)=0. All 64 theorem headers use exactly the adjacent indices 0..63 and have no parameters. Each proof unfolds the required polynomials and modulus and uses ordinary `ring_nf` and characteristic-two reasoning. No admission, custom axiom or native-decision token occurs. The direct final Bezout theorem explicitly proves u*modulus+v*(R32+X)=1. These data are witnesses whose identities must be checked, not externally trusted computed results.

Canonical remainder degree bounds are not needed for the divisibility argument: arbitrary R_i satisfying the proved congruences are sufficient, with R0=X and R64=X. Degree64 of the modulus and positive/small factor degrees are separately proved where needed.

## Opaque package is a checked abstraction

Modulus.lean22–33 introduces an opaque SUBTYPE value containing function n↦X^(2^n) and the proof ∀n,function(n)=X^(2^n), constructed explicitly with rfl. This is neither an axiom nor an unproved abstract power sequence. Projection of its checked property gives the exact power equation. Its purpose is to avoid expanding enormous polynomial powers during specialization. The exporter and both checkers must still include and check its ordinary opaque declaration body; no imported cache may be treated as an accepted proof.

## Rabin argument

The generic next_frobenius step squares a prior divisibility and adds the certified adjacent square congruence. The bounded induction uses every finite step up to64 and yields modulus dividing X^(2^64)-X and X^(2^32)-R32, through the exact opaque-package equation.

The proof separately establishes monicity and natDegree64. Any hypothetical monic divisor of degree1..32 has an independently obtained irreducible factor. That factor divides the modulus and therefore X^(2^64)-X. Pinned Mathlib Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X implies its positive degree divides64. Since its degree is at most32, elementary finite divisor reasoning implies it divides32, hence the factor also divides X^(2^32)-X.

Subtracting the two32-power congruences gives divisibility of R32+X in characteristic2. The proved Bezout identity then forces the factor to be a unit, contradicting its irreducibility. This excludes every proper small monic divisor and proves the final irreducibility statement. The Mathlib finite-field lemma internally constructs a quotient field only for the already-proved irreducible FACTOR; it does not assume irreducibility of the target modulus, so the argument is not circular.

The native BitVec-to-polynomial quotient representation has a separate specification. This exact polynomial theorem does not, by itself, prove all native field operations satisfy the field laws or establish whole-library source coverage.

## Recorded isolated export and replay

The scoped export contains only `Gf64.exactPolynomialIrreducible` and `Gf64.modulus_irreducible` as selected roots from the fixed module, without a source edit or rebuild. The untouched export has156,850,168bytes and SHA256 fd80ffa72f70d262f12ac6289180d352c2f84301f11b7ac51d606af6c95d89cc.

Export completed in6.842seconds. The original stock Leanchecker accepted it in13.606seconds; ordinary independent Nanoda accepted the exact same file in4.459seconds. Every process returned0 within unchanged120second limits. Nanoda used2threads, only propext/Quot.sound/Classical.choice permitted, forbidden-axiom hard errors, and the existing nat/string extension configuration. No scheduling fallback or transformed proof export was needed.

An independent NDJSON structure pass confirmed that the only axiom declaration names are those three and that the private frobeniusPackage appears as an opaque declaration WITH an exported value and type. Thus the abstraction was not silently replaced by an axiom or omitted body during replay. The recorded export fingerprint identifies the input to both replay checks. Whole-project integration remains a distinct check.
