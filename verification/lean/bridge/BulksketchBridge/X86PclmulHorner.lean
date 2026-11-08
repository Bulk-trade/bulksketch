import BulksketchBridge.X86PclmulHornerChallenges
import BulksketchBridge.X86Pclmul

namespace BulksketchBridge.X86PclmulHorner

open Aeneas Aeneas.Std Aeneas.Std.X86PclmulRuntime
open BulksketchProofs.Field BulksketchBridge.Algebra.Gf64 BulksketchBridge.MutableZip
open X86PclmulHornerChallenges PortableHornerChallenges Aeneas.Std.PortableHornerRuntime
open bulksketch.backend.x86_pclmul

private abbrev doubleEnded :=
  bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT U64

private def registerStep (cl : Bool) (value point : Xmm) (coefficient : U64) : Xmm :=
  let high := high64 (clmul128 (low64 value) (low64 point))
  join128 (multiplyWord (low64 value) (low64 point))
    (if cl then high ^^^ overflow64 high else 0) ^^^ coefficient.bv.setWidth 128

private theorem register_step (cl : Bool) (value point : Xmm) (coefficient : U64) :
    (do
      let product ← clmul 0#i32 value point
      let result ← reduced cl dictionary product
      let coeff ← word coefficient
      X86PclmulRuntime.xor result coeff) = Result.ok (registerStep cl value point coefficient) := by
  have product : clmul 0#i32 value point =
      Result.ok (clmul128 (low64 value) (low64 point)) := by
    simp only [clmul, show (0#i32).bv.getLsbD 0 = false from rfl,
      show (0#i32).bv.getLsbD 4 = false from rfl, Bool.false_eq_true, ite_false]
  simp only [product, X86Pclmul.reduced_refines cl _, X86Pclmul.word_refines coefficient,
    bind_ok, X86PclmulRuntime.xor]
  rfl

private theorem register_step_low (cl : Bool) (value point : Xmm) (coefficient : U64) :
    low64 (registerStep cl value point coefficient) =
      (stepWord ⟨low64 point⟩ ⟨low64 value⟩ coefficient).bv := by
  have lowJoin (lo hi : BitVec 64) : (join128 lo hi).setWidth 64 = lo := by
    apply BitVec.eq_of_getLsbD_eq
    intro index bound
    simp [join128, bound]
  simp [registerStep, low64, lowJoin, stepWord, BitVec.setWidth_xor,
    BitVec.setWidth_setWidth_of_le]

private theorem rev_next {iterator next : core.slice.iter.Iter U64} {item : Option U64}
    (step : core.slice.iter.IteratorSliceIter.next_back iterator = Result.ok (item, next)) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next doubleEnded ⟨iterator⟩ =
      Result.ok (item, ⟨next⟩) := by
  change (do
    let (item, next) ← core.slice.iter.IteratorSliceIter.next_back iterator
    Result.ok (item, (⟨next⟩ : core.iter.adapters.rev.Rev (core.slice.iter.Iter U64)))) = _
  rw [step]
  exact bind_ok (item, next) _

/-- The hardware loop carries the entire register. Its low word alone is the
accumulator used by the next CLMUL instruction and by the final word read. -/
private theorem inner_loop (cl : Bool) (point : Xmm) (remaining : List U64) (rest : Slice U64)
    (reversed : rest.val.reverse = remaining) (value : Xmm) :
    ∃ output,
      horner_loop0_loop0 cl dictionary ⟨⟨rest, 0⟩⟩ point value = Result.ok output ∧
      (⟨low64 output⟩ : U64) = remaining.foldl (stepWord ⟨low64 point⟩) ⟨low64 value⟩ := by
  induction remaining generalizing rest value with
  | nil =>
    have empty : rest.val = [] := List.reverse_eq_nil_iff.mp reversed
    have next : core.slice.iter.IteratorSliceIter.next_back ⟨rest, 0⟩ =
        Result.ok (none, ⟨rest, 0⟩) := by
      unfold core.slice.iter.IteratorSliceIter.next_back
      split
      · rename_i active
        change 0 < rest.val.length at active
        simp [empty] at active
      · rfl
    refine ⟨value, ?_, rfl⟩
    have bodyDone : horner_loop0_loop0.body cl dictionary point ⟨⟨rest, 0⟩⟩ value =
        Result.ok (ControlFlow.done value) := by
      rw [horner_loop0_loop0.body, rev_next next, bind_ok]
      rfl
    unfold horner_loop0_loop0 loop
    dsimp only
    rw [bodyDone, bind_ok]
  | cons coefficient remaining ih =>
    have positive : 0 < rest.val.length := by
      have nonempty : rest.val ≠ [] := by intro empty; simp [empty] at reversed
      exact List.length_pos_iff.mpr nonempty
    obtain ⟨⟨item, next⟩, normal, itemEq, nextVals, nextCursor⟩ :=
      RawMulTable.normal_of_spec _ _ (core.slice.iter.IteratorSliceIter.next_back.spec
        (⟨rest, 0⟩ : core.slice.iter.Iter U64) positive)
    have itemExact : item = some coefficient := by
      change item = rest.val.getLast? at itemEq
      rw [itemEq, List.getLast?_eq_head?_reverse]
      simp [reversed]
    have nextExact : next = ⟨next.slice, 0⟩ := by cases next; simp_all
    have nextReversed : next.slice.val.reverse = remaining := by
      change next.slice.val = rest.val.take (rest.val.length - 1) at nextVals
      rw [nextVals, ← List.dropLast_eq_take]
      have original : rest.val = remaining.reverse ++ [coefficient] := by
        simpa using congrArg List.reverse reversed
      simp [original]
    have nextStep : core.slice.iter.IteratorSliceIter.next_back ⟨rest, 0⟩ =
        Result.ok (some coefficient, ⟨next.slice, 0⟩) := by
      rw [normal, itemExact, nextExact]
    obtain ⟨output, recursive, lowWord⟩ :=
      ih next.slice nextReversed (registerStep cl value point coefficient)
    refine ⟨output, ?_, ?_⟩
    · have bodyStep :
          horner_loop0_loop0.body cl dictionary point ⟨⟨rest, 0⟩⟩ value =
            Result.ok (ControlFlow.cont (⟨⟨next.slice, 0⟩⟩, registerStep cl value point coefficient)) := by
        simp only [horner_loop0_loop0.body, rev_next nextStep, bind_ok]
        dsimp! only
        trans (do
          let newValue ← (do
            let product ← clmul 0#i32 value point
            let result ← reduced cl dictionary product
            let coeff ← word coefficient
            X86PclmulRuntime.xor result coeff)
          Result.ok (ControlFlow.cont (⟨⟨next.slice, 0⟩⟩, newValue)))
        · simp only [Aeneas.Std.bind_assoc]
        · simp only [register_step, bind_ok]
      unfold horner_loop0_loop0 loop
      dsimp only
      rw [bodyStep, bind_ok]
      exact recursive
    · have step : (⟨low64 (registerStep cl value point coefficient)⟩ : U64) =
          stepWord ⟨low64 point⟩ ⟨low64 value⟩ coefficient :=
        U64.bv_eq_imp_eq _ _ (register_step_low cl value point coefficient)
      simpa only [step, List.foldl_cons] using lowWord

private theorem inner_word (cl : Bool) (point leading : U64) (rest : Slice U64) :
    (do
      let value ← horner_loop0_loop0 cl dictionary ⟨⟨rest, 0⟩⟩
        (point.bv.setWidth 128) (leading.bv.setWidth 128)
      low value) = Result.ok (rest.val.reverse.foldl (stepWord point) leading) := by
  obtain ⟨output, normal, lowWord⟩ :=
    inner_loop cl (point.bv.setWidth 128) _ rest rfl (leading.bv.setWidth 128)
  have read := X86Pclmul.low_refines output
  simp only [normal, bind_ok, read]
  change Result.ok (⟨low64 output⟩ : U64) = _
  rw [lowWord]
  cases point
  cases leading
  simp [low64, BitVec.setWidth_setWidth_of_le]

theorem horner_refines : HornerRefines := by
  intro cl coefficients points out
  unfold horner expectedOutput
  cases reversed : coefficients.val.reverse with
  | nil =>
    have splitNone : splitLast coefficients = Result.ok none := by
      simp [splitLast, List.getLast?_eq_head?_reverse, reversed]
    obtain ⟨result, normal, _, words⟩ := RawMulTable.normal_of_spec _ _
      (core.slice.Slice.fill.spec core.clone.CloneU64 out 0#u64
        (by exact (WP.spec_ok (0#u64)).mpr rfl))
    simp only [splitNone, bind_ok, normal]
    exact congrArg Result.ok (Slice.ext _ _ (by simpa only [Slice.from_val] using words))
  | cons leading tail =>
    let rest := Slice.from coefficients.val.dropLast
      (by rw [List.length_dropLast]; exact (Nat.sub_le _ _).trans coefficients.length_ineq)
    have splitSome : splitLast coefficients = Result.ok (some (leading, rest)) := by
      simp [splitLast, List.getLast?_eq_head?_reverse, reversed, rest]
    have restWords : rest.val.reverse = tail := by
      have original : coefficients.val = tail.reverse ++ [leading] := by
        simpa using congrArg List.reverse reversed
      simp [rest, original]
    simp only [splitSome, bind_ok]
    dsimp! only
    apply run_prefix_map out points (fun _ point => tail.foldl (stepWord point) leading)
      (fun pair => horner_loop0.body cl dictionary leading rest pair.1 pair.2)
    · intro index active back
      have outBound : index < out.length := by omega
      have pointsBound : index < points.length := by omega
      change horner_loop0.body cl dictionary leading rest (stateAt out points index) back = _
      simp only [horner_loop0.body, next_some_at out points index outBound pointsBound,
        bind_ok, core.slice.Slice.iter, core.iter.traits.iterator.Iterator.rev.trait_default,
        core.iter.traits.iterator.Iterator.rev.default]
      dsimp! only
      rw [Slice.Inhabited_getElem_eq_getElem! points index pointsBound]
      simp only [X86Pclmul.word_refines points[index]!, X86Pclmul.word_refines leading, bind_ok]
      trans (do
        let target ← (do
          let value ← horner_loop0_loop0 cl dictionary ⟨⟨rest, 0⟩⟩
            (points[index]!.bv.setWidth 128) (leading.bv.setWidth 128)
          low value)
        Result.ok (ControlFlow.cont (stateAt out points (index + 1),
          fun final => back (replaceLeft final index target))))
      · simp only [Aeneas.Std.bind_assoc]
      · rw [inner_word, restWords, bind_ok]
    · intro back
      change horner_loop0.body cl dictionary leading rest
        (stateAt out points (min out.length points.length)) back = _
      rw [horner_loop0.body, next_done_at out points _ (by omega), bind_ok]
      rfl

theorem horner_entry_refines : HornerEntryRefines := by
  intro coefficients points out
  have lengthCheck : Slice.len out = Slice.len points ↔ out.length = points.length := by
    constructor
    · intro same
      simpa using congrArg UScalar.val same
    · intro same
      exact UScalar.eq_of_val_eq (by simpa using same)
  unfold bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.horner_many
  simp only [lengthCheck]
  split
  · exact horner_refines true coefficients points out
  · simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

end BulksketchBridge.X86PclmulHorner
