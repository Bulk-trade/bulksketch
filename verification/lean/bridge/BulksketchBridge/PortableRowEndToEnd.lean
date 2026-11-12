import BulksketchBridge.PortableSketchBoundary
import BulksketchBridge.PortableDecoderLaws
import BulksketchBridge.NativePlainCandidateFinish
import BulksketchBridge.NativePlainCandidateFinishZero
import BulksketchBridge.PortableBeginFront
import BulksketchBridge.RowConfiguration

namespace BulksketchBridge.PortableDecoder

open Aeneas.Std Algebra.Gf64 Reconciliation RebuiltLfsr RootRun RootWorkBudget
open ExecutionDriver ExecutionDriverRuntime ExecutionFinish PortableSketchBoundary
open PortableBeginFront (frontWork start atCandidates)
open bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch bulksketch.decode.stages
open bulksketch.types
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels (xor_assign)
open bulksketch.decode.stages.BinaryDecoder.Insts.BulksketchDecodeRowRowDecoderFKExecution (begin)
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (finish)
open scoped symmDiff

set_option maxRecDepth 4096
set_option maxHeartbeats 6500000

/-- The original row convention reserves one output slot for a changed
zero membership bit. The public size premise makes the subtraction exact. -/
def rowBudget (beta : Usize) (zeroDiff : Bool) : RowBudget :=
  ⟨ClosedLeafAdvance.usizeWord (beta.val - zeroCost zeroDiff), beta⟩

theorem rowBudget_nonzero (beta : Usize) (zeroDiff : Bool) :
    (rowBudget beta zeroDiff).nonzero.val = beta.val - zeroCost zeroDiff :=
  ClosedLeafAdvance.word_val _ ((Nat.sub_le ..).trans (show beta.val ≤ Usize.max by scalar_tac))

/-- An input-computable work reserve for the source row route with no
candidate hints. The root allowance uses the admitted output bound. -/
def rowWork (capacity : Nat) (budget : RowBudget) : Nat :=
  frontWork capacity budget.nonzero + plainCandidateWork capacity budget.nonzero.val budget.total

private theorem tail_monotone (capacity degree bound : Nat) (beta : Usize) (fits : degree ≤ bound) :
    plainCandidateWork capacity degree beta ≤ plainCandidateWork capacity bound beta := by
  have deflate : 2 * degree * (degree + 1) ≤ 2 * bound * (bound + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have rebuild : rebuiltVerifyUnits capacity degree beta.val ≤ rebuiltVerifyUnits capacity bound beta.val := by
    unfold rebuiltVerifyUnits
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega)) (by omega)
  exact Nat.add_le_add (Nat.add_le_add deflate (rootsEnvelope_mono fits))
    (Nat.add_le_add_right (max_le_max (Nat.le_refl _) rebuild) _)

/-- Start the original Portable binary row decoder on the original
Portable XOR of two valid in-memory rows. Its exact result denotes
their symmetric difference, including the independently tracked zero. -/
def ActualPortableRowEndToEnd : Prop :=
  ∀ (left right : Finset U64) (leftWords rightWords : Slice U64)
    (leftZero rightZero : Bool) (beta : Usize) (workspace : RowWorkspace) (meter : WorkMeter),
    ValidInMemoryRow left leftWords leftZero → ValidInMemoryRow right rightWords rightZero →
    leftWords.length = rightWords.length → 0 < leftWords.length → leftWords.length ≤ 65535 →
    (left ∆ right).card ≤ beta.val → beta.val ≤ leftWords.length →
    let zeroDiff := Bool.xor leftZero rightZero
    let budget := rowBudget beta zeroDiff
    WorkspaceAdmission.Admitted (workspaceLengths workspace) leftWords.length budget.nonzero.val →
    meter.exhausted = false →
    meter.used.val + rowWork leftWords.length budget ≤ meter.limit.val →
    ∃ (difference : Slice U64) (execution : Execution bulksketch.field.Gf64 bulksketch.backend.portable.Portable)
        (result : RowResult) (written : RowWorkspace) (paid : WorkMeter) (output : List U64),
      let input : RowInput := ⟨difference, Slice.from [] (by simp)⟩
      xor_assign portableField leftWords rightWords = .ok difference ∧
      begin portableField portableKernels budget = .ok execution ∧
      finish nativeCalls nativeDivRem nativeCanonicalize portableField portableKernels
        execution input workspace meter = .ok (.Ok result, written, id, paid) ∧
      decodedIds zeroDiff result = some output ∧ output.Nodup ∧ output.toFinset = left ∆ right ∧
      paid.limit = meter.limit ∧ paid.exhausted = false ∧
      paid.used.val ≤ meter.used.val + rowWork leftWords.length budget


theorem portable_row_end_to_end : ActualPortableRowEndToEnd := by
  intro left right leftWords rightWords leftZero rightZero beta workspace meter
    leftValid rightValid sameWidth nonempty widthMax diffFits betaFits zeroDiff budget admitted live reserve
  obtain ⟨difference, xorRun, width, valid⟩ :=
    portable_sketch_xor left right leftWords rightWords leftZero rightZero leftValid rightValid sameWidth
  let input : RowInput := ⟨difference, Slice.from [] (by simp)⟩
  let ids := left ∆ right
  let support := nonzeroSupport ids
  let initial := start budget workspace meter
  have widthEq : input.difference.length = leftWords.length := width
  have odd : ∀ i < input.difference.length, toField input.difference[i]!.bv = oddSyndrome support i :=
    valid.odd
  have oddsForFront : ∀ i < input.difference.length, toField input.difference.val[i]!.bv = oddSyndrome support i := by
    simpa only [Slice.getElem!_Nat_eq] using odd
  have membership : zeroDiff = true ↔ 0#u64 ∈ ids := valid.zero
  have size : support.card + zeroCost zeroDiff = ids.card := support_card_add_zeroCost ids zeroDiff membership
  have exactBudget : budget.nonzero.val = beta.val - zeroCost zeroDiff := rowBudget_nonzero beta zeroDiff
  have betaWord : budget.total = beta := rfl
  have reserved : budget.total.val = budget.nonzero.val + zeroCost zeroDiff := by
    change ids.card ≤ beta.val at diffFits
    rw [betaWord, exactBudget]
    omega
  have supportFits : support.card ≤ budget.nonzero.val := by
    change ids.card ≤ beta.val at diffFits
    rw [betaWord] at reserved
    omega
  have budgetFits : budget.nonzero.val ≤ input.difference.length := by
    rw [widthEq, exactBudget]
    exact (Nat.sub_le ..).trans betaFits
  have betaFitsWord : budget.total.val ≤ 65535 := by rw [betaWord]; exact betaFits.trans widthMax
  have tailBound : plainCandidateWork input.difference.length support.card budget.total ≤
      plainCandidateWork input.difference.length budget.nonzero.val budget.total :=
    tail_monotone _ _ _ _ supportFits
  have totalReserve : meter.used.val + (frontWork input.difference.length budget.nonzero +
      plainCandidateWork input.difference.length budget.nonzero.val budget.total) ≤ meter.limit.val := by
    rw [widthEq]
    exact reserve
  have frontFits : meter.used.val + frontWork input.difference.length budget.nonzero ≤ meter.limit.val := by omega
  have inputAdmitted : WorkspaceAdmission.Admitted (workspaceLengths workspace)
      input.difference.length budget.nonzero.val := by rwa [widthEq]
  obtain ⟨began, front⟩ := PortableBeginFront.portable_begin_front budget input workspace meter support
    (nonzeroSupport_no_zero ids) supportFits budgetFits inputAdmitted oddsForFront live frontFits
  rcases front with ⟨empty, equalBudget, finished⟩ | ⟨degree, written, paid, chunk, exactDegree, locator, _,
      widths, paidLive, paidLimit, paidUsed⟩
  · have noZero := (row_budget_total_eq_nonzero budget zeroDiff reserved).mp equalBudget
    have noIds : ids = ∅ := by
      rw [empty, noZero] at size
      exact Finset.card_eq_zero.mp (by simpa [zeroCost] using size.symm)
    exact ⟨difference, initial.execution, .Equal, workspace, meter, [], xorRun, began, finished, rfl,
      List.nodup_nil, by simp [noIds, ids], rfl, live, Nat.le_add_right ..⟩
  · let before := atCandidates budget degree written paid
    have ready : PlainCandidate before input support :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, exactDegree, locator, by
        change WorkspaceAdmission.Admitted (workspaceLengths written) input.difference.length budget.nonzero.val
        rwa [widths], paidLive⟩
    have tailRoom : paid.used.val + plainCandidateWork input.difference.length support.card budget.total ≤
        paid.limit.val := by
      rw [paidLimit]
      omega
    have positive : 0 < input.difference.length := by rwa [widthEq]
    have capFits : input.difference.length ≤ 65535 := by rwa [widthEq]
    have recovered :
        ∃ (sorted : Slice U64) (out : RowWorkspace) (finalMeter : WorkMeter),
          let reply := if support.card = 0 ∧ budget.total = budget.nonzero then RowResult.Equal
            else RowResult.Decoded sorted
          finish nativeCalls nativeDivRem nativeCanonicalize portableField portableKernels initial.execution
            input workspace meter = .ok (.Ok reply, out, id, finalMeter) ∧
          rootSupport sorted = support ∧ sorted.val.Nodup ∧ finalMeter.limit = paid.limit ∧
          finalMeter.exhausted = false ∧
          finalMeter.used.val ≤ paid.used.val + plainCandidateWork input.difference.length support.card budget.total := by
      by_cases zeroBudget : budget.nonzero.val = 0
      · obtain ⟨sorted, out, finalMeter, ran, supportEq, distinct, _, _, _, limit, active, debit⟩ :=
          native_plain_candidate_finish_zero support input before initial 2 positive capFits zeroBudget
            betaFitsWord supportFits odd rfl ready tailRoom chunk
        exact ⟨sorted, out, finalMeter, ran, supportEq, distinct, limit, active, debit⟩
      · obtain ⟨sorted, out, finalMeter, ran, supportEq, distinct, _, _, _, limit, active, debit⟩ :=
          native_plain_candidate_finish_positive portableKernels exact_scale_xor reducer_square raw_mul square reduce
            mul_word inverse direct_two horner paid_verification support input before initial 2
            positive capFits (Nat.pos_of_ne_zero zeroBudget) budgetFits betaFitsWord supportFits
            (nonzeroSupport_no_zero ids) odd rfl ready tailRoom chunk
        exact ⟨sorted, out, finalMeter, ran, supportEq, distinct, limit, active, debit⟩
    obtain ⟨sorted, out, finalMeter, ran, supportEq, distinct, limit, active, debit⟩ := recovered
    let reply := if support.card = 0 ∧ budget.total = budget.nonzero then RowResult.Equal
      else RowResult.Decoded sorted
    obtain ⟨output, interpreted, unique, exact⟩ :=
      decoded_ids_exact_at_budget ids sorted zeroDiff budget membership reserved supportEq distinct
    refine ⟨difference, initial.execution, reply, out, finalMeter, output, xorRun, began, ran, interpreted,
      unique, exact, limit.trans paidLimit, active, ?_⟩
    unfold rowWork
    rw [← widthEq]
    omega

#print axioms portable_row_end_to_end

end BulksketchBridge.PortableDecoder
