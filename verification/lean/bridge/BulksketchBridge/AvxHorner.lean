import BulksketchBridge.AvxHornerOuter

namespace BulksketchBridge.AvxHorner

open Aeneas Aeneas.Std Aeneas.Std.AvxSquareRuntime
open Aeneas.Std.AvxHornerChunkRuntime Aeneas.Std.PortableHornerRuntime
open AvxSquare PortableHornerChallenges
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1700000

def expected (coefficients points : Slice U64) : Slice U64 :=
  Slice.from (points.val.map (evalWord coefficients.val)) (by simp)

@[simp] theorem expected_length (coefficients points : Slice U64) :
    (expected coefficients points).length = points.length := by simp [expected, Slice.length]

theorem expected_word (coefficients points : Slice U64) (i : Nat) (active : i < points.length) :
    (expected coefficients points)[i]! = evalWord coefficients.val points[i]! := by
  simp only [expected, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ _ (by simpa using active), List.getElem_map,
    List.Inhabited_getElem_eq_getElem! _ _ active]

def ActualAvxHornerKernel : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (cl : Bool) (coefficients points out : Slice U64), out.length = points.length →
      horner_kernel loadModel storeModel cl coefficients points out = .ok (expected coefficients points)

theorem kernel_refines : ActualAvxHornerKernel := by
  intro loadModel storeModel loadLaw storeLaw cl coefficients points out same
  cases reversed : coefficients.val.reverse with
  | nil =>
    have splitNone : splitLast coefficients = Result.ok none := by
      simp [splitLast, List.getLast?_eq_head?_reverse, reversed]
    have expectedZero : expected coefficients points = RebuiltLfsr.zeroWords out := by
      apply Slice.ext
      simp only [expected, RebuiltLfsr.zeroWords, Slice.from_val]
      have zeroEval : evalWord coefficients.val = fun _ => 0#u64 := by
        funext point
        simp [evalWord, reversed]
      rw [zeroEval, List.map_const', same]
    simp only [horner_kernel, splitNone, bind_ok, RebuiltLfsr.fill_zero, expectedZero]
  | cons leading tail =>
    let rest := Slice.from coefficients.val.dropLast
      (by rw [List.length_dropLast]; exact (Nat.sub_le _ _).trans coefficients.length_ineq)
    have splitSome : splitLast coefficients = Result.ok (some (leading, rest)) := by
      simp [splitLast, List.getLast?_eq_head?_reverse, reversed, rest]
    have restWords : rest.val.reverse = tail := by
      have original : coefficients.val = tail.reverse ++ [leading] := by
        simpa using congrArg List.reverse reversed
      simp [rest, original]
    have expectedEval : evalFrom leading rest points out 0 = expected coefficients points := by
      apply Slice.ext_getElem (by simp [same])
      intro i evalBound expectedBound
      have bounded : i < points.length := by simpa using expectedBound
      rw [Slice.Inhabited_getElem_eq_getElem! _ _ evalBound, Slice.Inhabited_getElem_eq_getElem! _ _ expectedBound,
        eval_from_word _ _ _ _ _ _ (by rwa [same]), expected_word _ _ _ bounded]
      simp only [Nat.zero_le, ite_true, evalWord, reversed, restWords]
    have eight : (8#usize).val = 8 := by simp
    have loop := outer_loop loadModel storeModel loadLaw storeLaw cl leading rest points out 0 (fun s => s) same (Nat.zero_le _)
    simp only [horner_kernel, splitSome, bind_ok]
    dsimp! only
    simp only [chunksMut, chunks, eight, show 8 ≠ 0 by decide, ite_false, bind_ok, zipConstruct]
    dsimp! only
    have initial : (⟨⟨points, 0, 8⟩, ⟨out, 0, 8⟩⟩ : State) = stateAt points out 0 := rfl
    rw [initial, loop, bind_ok]
    simp only [stateAt, expectedEval]

def ActualAvxHornerFree : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (coefficients points out : Slice U64), out.length = points.length →
      horner_many loadModel storeModel coefficients points out = .ok (expected coefficients points)

theorem free_refines : ActualAvxHornerFree := by
  intro loadModel storeModel loadLaw storeLaw coefficients points out same
  exact kernel_refines loadModel storeModel loadLaw storeLaw true coefficients points out same

/-- Exact AVX dispatch for GF64, including the public length guard. -/
def ActualAvxHorner : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
  ∀ (coefficients points out : Slice U64),
    let actual :=
      bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.horner_many
        loadModel storeModel bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField coefficients points out
    if out.length = points.length then actual = .ok (expected coefficients points)
    else actual = .fail Error.panic

theorem trait_refines : ActualAvxHorner := by
  intro loadModel storeModel loadLaw storeLaw coefficients points out
  have lengthCheck : Slice.len out = Slice.len points ↔ out.length = points.length := by
    constructor
    · intro same
      simpa using congrArg UScalar.val same
    · intro same
      exact UScalar.eq_of_val_eq (by simpa using same)
  dsimp only
  unfold bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.horner_many
  simp only [lengthCheck]
  split
  · rename_i same
    have bits : bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = 64#u32 := by
      simp only [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
    simp only [bits, bind_ok, bne_self_eq_false, Bool.false_eq_true, ite_false]
    exact free_refines loadModel storeModel loadLaw storeLaw coefficients points out same
  · simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

open Algebra.Gf64 SliceKernels

def ActualAvxHornerEvaluatesPolynomial : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ coefficients points out : Slice U64, out.length = points.length →
      ∃ output,
        bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.horner_many
          loadModel storeModel bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField coefficients points out =
            Result.ok output ∧ output.length = out.length ∧
        ∀ i, i < points.length →
          toField output[i]!.bv = (slicePolynomial coefficients).eval (toField points[i]!.bv)

theorem trait_polynomial_refines : ActualAvxHornerEvaluatesPolynomial := by
  intro loadModel storeModel loadLaw storeLaw coefficients points out same
  have ran := trait_refines loadModel storeModel loadLaw storeLaw coefficients points out
  dsimp only at ran
  rw [ite_eq_left same] at ran
  refine ⟨expected coefficients points, ran, (expected_length _ _).trans same.symm, ?_⟩
  intro i active
  rw [expected_word _ _ _ active]
  exact PortableHorner.horner_word_evaluates coefficients points[i]!

end BulksketchBridge.AvxHorner
