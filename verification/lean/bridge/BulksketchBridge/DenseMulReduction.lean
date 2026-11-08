import BulksketchBridge.DenseMulReductionSpec
import BulksketchBridge.Gf64Reduce

namespace BulksketchBridge.DenseMulReduction

open Aeneas Aeneas.Std BulksketchBridge.MutableZip DenseMulReductionSpec
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial
open scoped BulksketchBridge.DenseMulReductionSpec

theorem loop_refines : DenseMulReductionSpec.finalReductionFrame := by
  intro K kernels reduceAgrees dst raw same start bounded back
  have reduceNormal (product : bulksketch.types.RawProduct) :
      kernels.ArithmeticInst.reduce product = Result.ok (reduceWord product) := by
    obtain ⟨output, normal, bits, _⟩ := Gf64Reduce.reduce_refines product
    have exactWord : output = reduceWord product := by
      apply U64.bv_eq_imp_eq
      exact bits
    rw [reduceAgrees, normal, exactWord]
  suffices ∀ remaining start, start ≤ dst.length → dst.length - start = remaining →
      ∀ back : State U64 bulksketch.types.RawProduct → State U64 bulksketch.types.RawProduct,
        ∃ restore : State U64 bulksketch.types.RawProduct → State U64 bulksketch.types.RawProduct,
          mul_into_loop1 dictionary kernels (stateAt dst raw start) back =
            Result.ok (stateAt dst raw dst.length, restore) ∧
          restore (stateAt dst raw dst.length) =
            back (stateAt (mapFrom dst raw (fun _ product => reduceWord product) start) raw dst.length)
    from this (dst.length - start) start bounded rfl back
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bounded count back
    by_cases active : start < dst.length
    · have rightBound : start < raw.length := by omega
      have step : mul_into_loop1.body dictionary kernels (stateAt dst raw start) back =
          Result.ok (ControlFlow.cont (stateAt dst raw (start + 1),
            fun final => back (replaceLeft final start (reduceWord raw[start]!)))) := by
        simp only [mul_into_loop1.body, next_some_at dst raw start active rightBound, bind_ok]
        dsimp! only
        rw [Slice.Inhabited_getElem_eq_getElem! raw start rightBound, reduceNormal]
        simp only [bind_ok]
      obtain ⟨restore, returns, meaning⟩ := ih (dst.length - (start + 1)) (by omega)
        (start + 1) (by omega) rfl
        (fun final => back (replaceLeft final start (reduceWord raw[start]!)))
      refine ⟨restore, ?_, ?_⟩
      · unfold mul_into_loop1 loop
        dsimp only
        rw [step]
        simp only [bind_ok]
        exact returns
      · rw [meaning, apply_step dst raw (fun _ product => reduceWord product) start active]
    · have terminal : start = dst.length := by omega
      subst start
      refine ⟨back, ?_, ?_⟩
      · unfold mul_into_loop1 loop
        dsimp only
        simp only [mul_into_loop1.body,
          next_done_at dst raw dst.length (Or.inl (Nat.le_refl _)), bind_ok]
        dsimp! only
        simp only [bind_ok]
      · rw [mapFrom_full_length]

end BulksketchBridge.DenseMulReduction
