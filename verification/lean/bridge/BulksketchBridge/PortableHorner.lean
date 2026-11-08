import BulksketchBridge.PortableHornerChallenges
import BulksketchBridge.PortableZipMap
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.PortableHorner

open Aeneas Aeneas.Std BulksketchBridge.Algebra.Gf64 BulksketchBridge.MutableZip
open PortableHornerChallenges Aeneas.Std.PortableHornerRuntime
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels

private abbrev dictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
private abbrev callback :=
  bulksketch.backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64
    dictionary

private abbrev doubleEnded :=
  bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT U64

private theorem call_mut_refines (point value coefficient : U64) :
    bulksketch.backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
      dictionary point (value, coefficient) =
      Result.ok (stepWord point value coefficient, point) := by
  change (do
    let product ← bulksketch.field.gf64.mul dictionary value point
    let result ← lift (product ^^^ coefficient)
    Result.ok (result, point)) = _
  simp only [native_mul_word, Bind.bind, bind_ok, lift, stepWord]

private theorem fold_loop (remaining : List U64) (rest : Slice U64)
    (reversed : rest.val.reverse = remaining) (point initial : U64) :
    loop (foldBody doubleEnded callback)
        ((⟨rest, 0⟩ : core.slice.iter.Iter U64), initial, point) =
      Result.ok (remaining.foldl (stepWord point) initial) := by
  induction remaining generalizing rest initial with
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
    unfold loop
    simp only [foldBody, next, bind_ok, List.foldl_nil]
    dsimp! only
    simp only [bind_ok]
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
    have cursorExact : next.i = 0 := nextCursor
    have nextExact : next = ⟨next.slice, 0⟩ := by cases next; simp_all
    have nextReversed : next.slice.val.reverse = remaining := by
      change next.slice.val = rest.val.take (rest.val.length - 1) at nextVals
      rw [nextVals, ← List.dropLast_eq_take]
      have original : rest.val = remaining.reverse ++ [coefficient] := by
        simpa using congrArg List.reverse reversed
      rw [original]
      simp
    have step : core.slice.iter.IteratorSliceIter.next_back ⟨rest, 0⟩ =
        Result.ok (some coefficient, ⟨next.slice, 0⟩) := by
      rw [normal, itemExact, nextExact]
    unfold loop
    simp only [foldBody, step, bind_ok, List.foldl_cons]
    dsimp! only
    rw [call_mut_refines, bind_ok]
    dsimp! only
    rw [bind_ok]
    exact ih next.slice nextReversed (stepWord point initial coefficient)

private theorem reverse_fold_refines (rest : Slice U64) (point initial : U64) :
    reverseFold doubleEnded callback ⟨⟨rest, 0⟩⟩ initial point =
      Result.ok (rest.val.reverse.foldl (stepWord point) initial) :=
  fold_loop _ rest rfl point initial

private theorem eval_words (out points : Slice U64) (same : out.length = points.length)
    (eval : U64 → U64) :
    (mapFrom out points (fun _ point => eval point) 0).val = points.val.map eval := by
  apply List.ext_getElem
  · simpa using same
  · intro index leftBound rightBound
    have outBound : index < out.length := by simpa using leftBound
    have pointsBound : index < points.length := by simpa using rightBound
    rw [List.getElem_map]
    rw [List.Inhabited_getElem_eq_getElem! _ _ leftBound]
    rw [← Slice.getElem!_Nat_eq, mapFrom_word out points _ 0 index outBound]
    simp only [Nat.zero_le, ite_true, Slice.getElem!_Nat_eq,
      ← List.Inhabited_getElem_eq_getElem! _ _ pointsBound]

private theorem horner_loop (out points : Slice U64) (same : out.length = points.length)
    (leading : U64) (rest : Slice U64) :
    horner_many_loop dictionary (stateAt out points 0) (fun state => state) leading rest =
      Result.ok (stateAt (mapFrom out points
        (fun _ point => rest.val.reverse.foldl (stepWord point) leading) 0) points out.length) := by
  apply map_loop out points
    (fun _ point => rest.val.reverse.foldl (stepWord point) leading)
  · intro index outBound back
    have pointsBound : index < points.length := by omega
    change horner_many_loop.body dictionary leading rest (stateAt out points index) back = _
    simp only [horner_many_loop.body, next_some_at out points index outBound pointsBound,
      bind_ok, core.slice.Slice.iter, core.iter.traits.iterator.Iterator.rev.trait_default,
      core.iter.traits.iterator.Iterator.rev.default]
    dsimp! only
    rw [reverse_fold_refines, bind_ok]
    rw [Slice.Inhabited_getElem_eq_getElem! points index pointsBound]
  · intro back
    change horner_many_loop.body dictionary leading rest (stateAt out points out.length) back = _
    simp only [horner_many_loop.body, next_done_at out points out.length (Or.inl (Nat.le_refl _)),
      bind_ok]
    rfl
  · exact Nat.zero_le _

/-- The original Horner kernel evaluates every point and replaces the entire
destination frame. The guard rejects unequal output and point lengths. -/
theorem horner_many_refines : hornerRefines := by
  intro coefficients points out
  dsimp only
  have lengthCheck : Slice.len out = Slice.len points ↔ out.length = points.length := by
    constructor
    · intro same
      simpa using congrArg UScalar.val same
    · intro same
      exact UScalar.eq_of_val_eq (by simpa using same)
  unfold horner_many
  simp only [lengthCheck]
  split
  · rename_i same
    cases reversed : coefficients.val.reverse with
    | nil =>
      have splitNone : splitLast coefficients = Result.ok none := by
        simp [splitLast, List.getLast?_eq_head?_reverse, reversed]
      obtain ⟨result, normal, length, words⟩ := RawMulTable.normal_of_spec _ _
        (core.slice.Slice.fill.spec core.clone.CloneU64 out 0#u64
          (by exact (WP.spec_ok (0#u64)).mpr rfl))
      refine ⟨result, ?_, length, ?_⟩
      · simpa only [splitNone, bind_ok] using normal
      · rw [words, same]
        have zeroEval : evalWord coefficients.val = fun _ => 0#u64 := by
          funext point
          simp [evalWord, reversed]
        rw [zeroEval, List.map_const']
    | cons leading tail =>
      let rest := Slice.from coefficients.val.dropLast
        (by rw [List.length_dropLast]; exact (Nat.sub_le _ _).trans coefficients.length_ineq)
      have splitSome : splitLast coefficients = Result.ok (some (leading, rest)) := by
        simp [splitLast, List.getLast?_eq_head?_reverse, reversed, rest]
      have restWords : rest.val.reverse = tail := by
        have original : coefficients.val = tail.reverse ++ [leading] := by
          simpa using congrArg List.reverse reversed
        simp [rest, original]
      refine ⟨mapFrom out points (fun _ point =>
        rest.val.reverse.foldl (stepWord point) leading) 0, ?_, mapFrom_length _ _ _ _, ?_⟩
      · simp only [splitSome, bind_ok, core.slice.Slice.iter_mut]
        dsimp! only
        rw [construct]
        simp only [bind_ok]
        dsimp! only
        rw [horner_loop out points same leading rest]
        simp only [bind_ok, stateAt]
      · rw [eval_words out points same]
        simp [evalWord, reversed, restWords]
  · simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

end BulksketchBridge.PortableHorner
