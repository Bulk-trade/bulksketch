module
public import Aeneas
@[expose] public section

/-!
General concrete standard-library value models required by field maps.
Checked conversions reuse Aeneas' full range-checking model for all inputs.
Population count is the complete BitVec population count, not a caller stub.
Rust std/intrinsic/compiler/ISA correspondence remains an explicit trust boundary.

The pinned Aeneas runtime represents TryFromIntError as Unit and erases diagnostic
formatting in Result.expect. The Debug adapter below reuses that existing Unit
model. It does not prove Rust formatting correctness. The independence theorem
covers every Debug dictionary, and native endpoint proofs establish inner Ok
before expect, so actual formatting is unreachable on all admitted calls.
-/

namespace Aeneas.Std

@[rust_fun "core::convert::num::{core::convert::TryFrom<u8, u64, core::num::error::TryFromIntError>}::try_from"]
def U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from (word : U64) :
    Result (core.result.Result U8 core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .U8 word

@[rust_fun "core::convert::num::ptr_try_from_impls::{core::convert::TryFrom<usize, u64, core::num::error::TryFromIntError>}::try_from"]
def Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from (word : U64) :
    Result (core.result.Result Usize core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .Usize word

/-- The general checked conversion yields inner Ok and preserves every value
within the target range; overflow retains the existing runtime's Err model. -/
theorem checked_unsigned_conversion_normal {source target : UScalarTy}
    (word : UScalar source) (bounded : word.val ≤ UScalar.max target) :
    ∃ output : UScalar target,
      core.num.tryFromUScalar target word = Result.ok (.Ok output) ∧
      output.val = word.val := by
  have lossless := UScalar.cast_inBounds_spec target word bounded
  simp only [lift, WP.spec_ok] at lossless
  exact ⟨UScalar.cast target word, by simp only [core.num.tryFromUScalar, bounded, ite_true],
    lossless⟩

@[rust_fun "core::num::{u64}::count_ones"]
def core.num.U64.count_ones (word : U64) : Result U32 :=
  .ok ⟨word.bv.cpop.setWidth 32⟩

/-- Population count returns normally with the full exact count, bounded by64. -/
theorem u64_count_ones_spec (word : U64) :
    ∃ count : U32,
      core.num.U64.count_ones word = Result.ok count ∧
      count.val = word.bv.cpop.toNat ∧ count.val ≤ 64 := by
  have bound := BitVec.toNat_cpop_le word.bv
  have fits : word.bv.cpop.toNat < 2 ^ 32 := by omega
  refine ⟨⟨word.bv.cpop.setWidth 32⟩, rfl, ?_, ?_⟩
  · change (word.bv.cpop.setWidth 32).toNat = word.bv.cpop.toNat
    simp only [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt fits
  · change (word.bv.cpop.setWidth 32).toNat ≤ 64
    simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt fits] using bound

@[rust_fun "core::num::error::{core::fmt::Debug<core::num::error::TryFromIntError>}::fmt"]
def core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt
    (error : core.num.error.TryFromIntError) (formatter : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  core.fmt.DebugUnit.fmt error formatter

/-- The result value/panic distinction is independent of every diagnostics
implementation in the pinned runtime; no formatting assumption enters expect. -/
theorem result_expect_independent_of_debug {T E : Type}
    (first second : core.fmt.Debug E) (result : core.result.Result T E) (message : Str) :
    core.result.Result.expect first result message =
      core.result.Result.expect second result message := by
  rfl

end Aeneas.Std
