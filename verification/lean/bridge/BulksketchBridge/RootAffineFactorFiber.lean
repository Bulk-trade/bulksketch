import BulksketchBridge.RootAffineGuards
import BulksketchBridge.AffineSolveMapComplete
import BulksketchBridge.RootSetupSpec

namespace BulksketchBridge.RootAffinePreparation

open Aeneas Aeneas.Std DenseCoefficient Polynomial Algebra.Gf64
open AffineSubspaces AffineSubspaceAlgebra AffineEnumerate AffineSolveMap
open bulksketch.backend.contract bulksketch.decode.affine

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem field_lift_evaluates (linear : Slice U64) (point : Field) :
    fieldLift (linearWord linear) point = (rowPolynomial linear).eval point := by
  rw [field_lift_linear_word, ← rowPolynomial_eval]
  have represented : toField (wordFieldEquiv.symm point) = point := wordFieldEquiv.apply_symm_apply point
  exact congrArg (fun x => (rowPolynomial linear).eval x) represented

/-- Once the affine multiple witness is known, the original solve map
    returns a complete fiber containing every factor root. Neither
    original rank rejection condition can occur. -/
def ActualNativeFactorFiber : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    TimesXMod.ExactScaleXor kernels →
    ∀ (affine linear : Slice U64) (initial : Columns) (factor : Polynomial Field),
      0 < affine.length → affine.length ≤ 65 → linear.val = affine.val.drop 1 →
      0 < linear.length → linear[(0 : Nat)]! ≠ 0#u64 →
      0 < factor.natDegree → factor.Splits → factor.roots.Nodup →
      factor ∣ AffineMultiple.witnessPolynomial affine[0]! linear →
      ∃ base rank written,
        solve_map RootSetup.gf64Dictionary kernels affine initial = .ok (some (base, rank), written) ∧
        let basis := prefixSlice written.to_slice rank.val
        rank.val ≤ 64 ∧ basis.length = rank.val ∧ IndependentDirections basis ∧
        factor.natDegree ≤ 2 ^ rank.val ∧ rank.val < affine.length - 1 ∧
        (∀ point, factor.IsRoot point → point ∈ coset (toField base.bv) (prefixDirections basis basis.length))

theorem native_factor_fiber : ActualNativeFactorFiber := by
  intro K kernels scale affine linear initial factor positive width linearValue hasX nonzeroX
    degree split simple multiple
  have bits : RootSetup.gf64Dictionary.BITS = .ok 64#u32 := by
    change Result.ok bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = _
    rw [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
  obtain ⟨coefficients, answer, written, exactValue, returned, fiber⟩ :=
    native_solve_map_fibers RootSetup.gf64Dictionary kernels bits scale affine initial positive width
  have exactLinear : coefficients = linear := Slice.ext _ _ (exactValue.trans linearValue.symm)
  subst coefficients
  have nonzeroFactor : factor ≠ 0 := by
    intro zero
    rw [zero, natDegree_zero] at degree
    omega
  cases answer with
  | none =>
    have nonempty : 0 < factor.roots.card := by rwa [← split.natDegree_eq_card_roots]
    obtain ⟨point, present⟩ := Multiset.card_pos_iff_exists_mem.mp nonempty
    have root := (mem_roots nonzeroFactor).mp present
    have solves := multiple_root_solves factor affine[0]! linear multiple point root
    change ¬∃ point, fieldLift (linearWord linear) point = value affine[0]! at fiber
    exact (fiber ⟨point, by rw [field_lift_evaluates]; exact solves⟩).elim
  | some answer =>
    obtain ⟨base, rank⟩ := answer
    let basis := prefixSlice written.to_slice rank.val
    obtain ⟨rankBound, basisLen, independent, _, _, exactFiber⟩ := fiber
    have equation (point : Field) : (rowPolynomial linear).eval point = toField affine[0]!.bv ↔
        point ∈ coset (toField base.bv) (prefixDirections basis basis.length) := by
      rw [← field_lift_evaluates]
      exact exactFiber point
    obtain ⟨enough, strict⟩ :=
      affine_rank_bounds factor affine[0]! linear basis (toField base.bv) hasX nonzeroX
        multiple nonzeroFactor split simple independent equation
    have linearLen : linear.length = affine.length - 1 := by
      rw [Slice.length, linearValue, List.length_drop]
    refine ⟨base, rank, written, returned, rankBound, basisLen, independent, ?_, ?_, ?_⟩
    · rwa [basisLen] at enough
    · rwa [basisLen, linearLen] at strict
    · intro point root
      exact (equation point).mp (multiple_root_solves _ _ _ multiple point root)

end BulksketchBridge.RootAffinePreparation
