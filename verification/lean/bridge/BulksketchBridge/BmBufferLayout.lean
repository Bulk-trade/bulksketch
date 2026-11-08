import BulksketchBridge.BmLoopFrames
import BulksketchBridge.BmHonestLocator

namespace BulksketchBridge.BmBufferLayout

open Aeneas.Std BulksketchBridge
open BmEntry DenseCoefficient RebuiltLfsr BmLoop
open bulksketch.types bulksketch.backend.contract

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

private theorem restore_val (original : Slice U64) (width : Nat) (left right : Slice U64)
    (admitted : width ≤ original.length)
    (leftLen : left.length = width) (rightLen : right.length = original.length - width) :
    (splitBack original width (left, right)).val = left.val ++ right.val := by
  simp only [splitBack, leftLen, rightLen, Nat.min_eq_left admitted, eq_self, and_self,
    dite_true, Slice.from_val]

private theorem restore_length_eq (original : Slice U64) (width : Nat) (left right : Slice U64)
    (admitted : width ≤ original.length)
    (leftLen : left.length = width) (rightLen : right.length = original.length - width) :
    (splitBack original width (left, right)).length = original.length := by
  change (splitBack original width (left, right)).val.length = original.length
  rw [restore_val original width left right admitted leftLen rightLen, List.length_append]
  change left.length + right.length = original.length
  omega

/-- For all admitted equal-length returned pieces, the three original
split backward functions restore the full row in source buffer order. -/
theorem three_frames (buffers : Slice U64) (width : Nat)
    (connection previous saved : Slice U64) (room : 3 * width ≤ buffers.length)
    (connLen : connection.length = width) (prevLen : previous.length = width)
    (saveLen : saved.length = width) :
    let rest := tail buffers width
    let rest1 := tail rest width
    let suffix := tail rest1 width
    let joined := BmTerminal.joinBuffers (splitBack buffers width) (splitBack rest width)
      (splitBack rest1 width) suffix connection previous saved
    joined.val = connection.val ++ previous.val ++ saved.val ++ suffix.val := by
  dsimp only
  let rest := tail buffers width
  let rest1 := tail rest width
  let suffix := tail rest1 width
  have restLen : rest.length = buffers.length - width := tail_length _ _
  have rest1Len : rest1.length = rest.length - width := tail_length _ _
  have suffixLen : suffix.length = rest1.length - width := tail_length _ _
  have thirdLen := restore_length_eq rest1 width saved suffix (by omega) saveLen suffixLen
  have secondLen := restore_length_eq rest width previous (splitBack rest1 width (saved, suffix))
    (by omega) prevLen (thirdLen.trans rest1Len)
  change (splitBack buffers width
    (connection, splitBack rest width (previous, splitBack rest1 width (saved, suffix)))).val = _
  rw [restore_val buffers width connection _ (by omega) connLen (secondLen.trans restLen),
    restore_val rest width previous _ (by omega) prevLen (thirdLen.trans rest1Len),
    restore_val rest1 width saved suffix (by omega) saveLen suffixLen]
  simp only [List.append_assoc, rest, rest1, suffix]

private theorem entry_widths (buffers : Slice U64) (capacity budget : Usize) (meter : WorkMeter)
    (room : 3 * (capacity.val + 1) ≤ buffers.length) :
    widths (BmLocator.initial buffers capacity budget meter) =
      (capacity.val + 1, capacity.val + 1, capacity.val + 1) := by
  have initialize_length (words : Slice U64) : (initialBuffer words budget).length = words.length := by
    rw [initialBuffer, Slice.setAtNat_length, restore_length]
  have prefix_width (words : Slice U64) (bounded : capacity.val + 1 ≤ words.length) :
      (prefixSlice words (capacity.val + 1)).length = capacity.val + 1 := by
    rw [prefix_length, Nat.min_eq_left bounded]
  simp only [widths, BmLocator.initial, initialize_length]
  rw [prefix_width buffers (by omega), prefix_width _ (by rw [tail_length]; omega),
    prefix_width _ (by rw [tail_length, tail_length]; omega)]

/-- The public returned buffer actually starts with the proved monic
locator. The other two live rows and the untouched original suffix follow
in the source split order. -/
theorem returned_locator (roots : Finset Algebra.Gf64.Field) (syndromes buffers : Slice U64)
    (capacity budget : Usize) (meter : WorkMeter) (last : State) (reply : BmTerminal.Return)
    (room : 3 * (capacity.val + 1) ≤ buffers.length)
    (returned : run (BmLocator.inputs syndromes buffers capacity budget) (2 * capacity.val)
      (BmLocator.initial buffers capacity budget meter) = some (last, reply))
    (outcome : BmHonestLocator.Outcome roots (BmLocator.inputs syndromes buffers capacity budget) last reply)
    (degree : Usize) (success : reply.1 = .Ok (.Ok degree)) :
    degree.val = roots.card ∧
      BmSyndromePolynomials.connectionPolynomial (prefixSlice reply.2.1 (capacity.val + 1))
        degree.val = Reconciliation.supportLocator roots := by
  have shape := (run_widths _ _ _ _ _ returned).trans (entry_widths buffers capacity budget meter room)
  rcases last with ⟨iter, finalMeter, connection, previous, saved, finalDegree, previousLen, shift, scale⟩
  change (connection.length, previous.length, saved.length) =
    (capacity.val + 1, capacity.val + 1, capacity.val + 1) at shape
  have connectionWidth := congrArg Prod.fst shape
  have previousWidth := congrArg (fun dims : Nat × Nat × Nat => dims.2.1) shape
  have savedWidth := congrArg (fun dims : Nat × Nat × Nat => dims.2.2) shape
  rcases outcome with ⟨error, chargedMeter, _, _, rfl⟩ | ⟨_, degreeVal, support, rfl⟩
  · cases success
  change core.result.Result.Ok (core.result.Result.Ok finalDegree) = _ at success
  injection success with inner
  injection inner with sameDegree
  subst degree
  let normalized := BmTerminal.normalizedConnection connection finalDegree.val
  have normalizedWidth : normalized.length = capacity.val + 1 := by
    unfold normalized BmTerminal.normalizedConnection
    rw [restore_length]
    exact connectionWidth
  have layout := three_frames buffers (capacity.val + 1) normalized previous saved
    room normalizedWidth previousWidth savedWidth
  change (BmTerminal.joinBuffers _ _ _ _ normalized previous saved).val = _ at layout
  have prefixEq : prefixSlice
      (finish (BmLocator.inputs syndromes buffers capacity budget) normalized previous saved finalMeter
        (.Ok (.Ok finalDegree))).2.1 (capacity.val + 1) = normalized := by
    apply Slice.ext
    simp only [finish, BmLocator.inputs, prefixSlice, Slice.from_val, layout]
    rw [← normalizedWidth]
    change List.take normalized.val.length _ = normalized.val
    rw [List.append_assoc, List.append_assoc, List.take_left]
  refine ⟨degreeVal, ?_⟩
  change BmSyndromePolynomials.connectionPolynomial (prefixSlice
    (finish (BmLocator.inputs syndromes buffers capacity budget) normalized previous saved finalMeter
      (.Ok (.Ok finalDegree))).2.1 (capacity.val + 1)) finalDegree.val = _
  rw [prefixEq]
  exact support

/-- Successful original source calls expose the exact support locator in
the caller's first workspace row. -/
def ActualReturnedLocator : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    BmDiscrepancy.RawArithmetic kernels → BmDiscrepancy.ReduceArithmetic kernels →
    BmMutable.NativeMul kernels → BmTerminal.NativeInverse kernels →
    ∀ (roots : Finset Algebra.Gf64.Field) (syndromes buffers difference initialSyndromes : Slice U64)
      (capacity budget : Usize) (meter : WorkMeter) (reply : BmTerminal.Return) (degree : Usize),
      (0 : Algebra.Gf64.Field) ∉ roots → roots.card ≤ budget.val → budget.val ≤ capacity.val →
      3 * (capacity.val + 1) ≤ buffers.length → 2 * capacity.val + 1 ≤ syndromes.length →
      Reconstruction.Prefix difference initialSyndromes syndromes (2 * capacity.val + 1) →
      BmHonestLocator.Moments roots syndromes (2 * capacity.val) →
      bulksketch.decode.bm.locator BmEntry.fieldDictionary kernels syndromes capacity budget buffers meter =
        .ok reply → reply.1 = .Ok (.Ok degree) →
      degree.val = roots.card ∧
        BmSyndromePolynomials.connectionPolynomial (prefixSlice reply.2.1 (capacity.val + 1)) degree.val =
          Reconciliation.supportLocator roots

theorem actual_returned_locator : ActualReturnedLocator := by
  intro K kernels raw reduce mul inverse roots syndromes buffers difference initialSyndromes capacity budget
    meter reply degree noZero supportBudget budgetCapacity room syndromeRoom reconstructed moments executed success
  obtain ⟨result, native, outcome⟩ := BmHonestLocator.honest_locator_refines kernels raw reduce mul inverse
    roots syndromes buffers difference initialSyndromes capacity budget meter noZero supportBudget
    budgetCapacity room syndromeRoom reconstructed moments
  have same := Result.ok_injective (native.symm.trans executed)
  subst result
  rcases outcome with ⟨_, _, _, rfl⟩ | ⟨finalMeter, last, _, returned, honest⟩
  · cases success
  · exact returned_locator roots syndromes buffers capacity budget finalMeter last reply room returned honest degree success

end BulksketchBridge.BmBufferLayout
