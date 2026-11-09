import BulksketchBridge.AvxHornerHeap

namespace BulksketchBridge.AvxHorner

open Aeneas.Std Aeneas.Std.AvxSquareRuntime
open AvxSquare X86MaskedMemory X86MaskedMemory.Allocation PortableHornerChallenges

set_option maxRecDepth 4096
set_option maxHeartbeats 1700000

inductive KernelHeapTrace (pointBase outBase : Address) (permit : Address → Bool)
    (coefficients points out : Slice U64) (heap : AddressHeap) : AddressHeap → Prop
  | empty {updated} : coefficients.val.reverse = [] →
      FillTrace outBase permit 0 out.length heap updated →
      KernelHeapTrace pointBase outBase permit coefficients points out heap updated
  | nonempty {leading rest updated} :
      coefficients.val.reverse = leading :: rest.val.reverse →
      AllocatedTrace pointBase outBase permit leading rest points 0 out heap
        (expected coefficients points) updated →
      KernelHeapTrace pointBase outBase permit coefficients points out heap updated

/-- Physical trace for point chunks and output, with coefficient values
supplied by the admitted typed slice. The model includes the empty
polynomial's scalar fill and both register reduction modes. -/
def ActualAllocatedAvxHornerKernel : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (live : LiveAllocations) (la57 : Bool) (pointBase outBase : Address)
      (permit : Address → Bool) (cl : Bool) (coefficients points out : Slice U64) (heap : AddressHeap),
      out.length = points.length →
      ReadView live la57 heap pointBase (8 * points.length) 8 →
      FiniteWordWindow heap pointBase points.length (fun i => points[i]!.bv) →
      WriteView live la57 heap permit outBase (8 * out.length) 8 →
      FiniteWordWindow heap outBase out.length (fun i => out[i]!.bv) →
      Disjoint outBase (8 * out.length) pointBase (8 * points.length) →
      ∃ updated,
        bulksketch.backend.x86_vpclmul512.horner_kernel loadModel storeModel cl coefficients points out =
          .ok (expected coefficients points) ∧
        KernelHeapTrace pointBase outBase permit coefficients points out heap updated ∧
        FiniteWordWindow updated outBase out.length (fun i => (expected coefficients points)[i]!.bv) ∧
        WriteView live la57 updated permit outBase (8 * out.length) 8 ∧
        ReadView live la57 updated pointBase (8 * points.length) 8 ∧
        FiniteWordWindow updated pointBase points.length (fun i => points[i]!.bv) ∧
        FramesOutside heap updated outBase (8 * out.length)

theorem allocated_kernel_refines : ActualAllocatedAvxHornerKernel := by
  intro loadModel storeModel loadLaw storeLaw live la57 pointBase outBase permit cl coefficients points out heap
    aligned pointView pointBytes outView outBytes apart
  have native := kernel_refines loadModel storeModel loadLaw storeLaw cl coefficients points out aligned
  cases reversed : coefficients.val.reverse with
  | nil =>
    obtain ⟨updated, ran, words, view, frame⟩ := fill_trace live la57 heap outBase permit (fun i => out[i]!.bv)
      out.length 0 out.length (by omega) outView outBytes
    have evaluated : FiniteWordWindow updated outBase out.length (fun i => (expected coefficients points)[i]!.bv) := by
      intro i active byte
      have value := expected_word coefficients points i (by omega)
      have filled := words i active byte
      simp only [evalWord, reversed] at value
      have within : 0 ≤ i ∧ i < 0 + out.length := ⟨Nat.zero_le _, by omega⟩
      simpa only [value, show (0#u64 : U64).bv = (0 : BitVec 64) from rfl, ite_eq_left within] using filled
    exact ⟨updated, native, .empty reversed ran, evaluated, view,
      frame_read_view frame apart pointView, frame_word_view frame apart pointView.no_wrap pointBytes, frame⟩
  | cons leading tail =>
    let rest := Slice.from coefficients.val.dropLast
      (by rw [List.length_dropLast]; exact (Nat.sub_le _ _).trans coefficients.length_ineq)
    have restWords : rest.val.reverse = tail := by
      have original : coefficients.val = tail.reverse ++ [leading] := by
        simpa using congrArg List.reverse reversed
      simp [rest, original]
    have initial : Prefix leading rest points out out 0 := by
      refine ⟨rfl, ?_⟩
      intro i _
      rw [ite_eq_right (Nat.not_lt_zero _)]
    have exactEval : evalFrom leading rest points out 0 = expected coefficients points := by
      apply Slice.ext_getElem (by simp [aligned])
      intro i leftRoom rightRoom
      have fit : i < points.length := by simpa using rightRoom
      rw [Slice.Inhabited_getElem_eq_getElem! _ _ leftRoom, Slice.Inhabited_getElem_eq_getElem! _ _ rightRoom,
        eval_from_word _ _ _ _ _ _ (by omega), expected_word _ _ _ fit]
      simp only [Nat.zero_le, ite_true, evalWord, reversed, restWords]
    obtain ⟨updated, ran, words, view, frame⟩ :=
      allocated_scan live la57 pointBase outBase permit leading rest points out out 0 heap aligned
        (Nat.zero_le _) initial pointView pointBytes outView outBytes apart
    rw [exactEval, expected_length, ← aligned] at words view
    rw [exactEval] at ran
    exact ⟨updated, native, .nonempty (leading := leading) (rest := rest) (by rwa [restWords]) ran, words, view,
      frame_read_view frame apart pointView, frame_word_view frame apart pointView.no_wrap pointBytes, frame⟩

end BulksketchBridge.AvxHorner
