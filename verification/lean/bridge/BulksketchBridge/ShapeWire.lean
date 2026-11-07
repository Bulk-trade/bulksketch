import BulksketchBridge.ShapeWireChallenges

namespace BulksketchBridge.ShapeWire

open Aeneas Aeneas.Std ShapeWireChallenges

private def checkedProgram (buckets words : Usize) : Option Usize := do
  let descriptors ← Usize.checked_mul buckets 2#usize
  let paddedBuckets ← Usize.checked_add buckets 7#usize
  let zero ← Usize.checked_div paddedBuckets 8#usize
  let wordsBytes ← Usize.checked_mul words 8#usize
  let payload ← Usize.checked_add wordsBytes zero
  if descriptors.val ≤ U32.max ∧ payload.val ≤ U32.max then do
    let header ← Usize.checked_add 24#usize descriptors
    Usize.checked_add header payload
  else none

local macro "normalize_wire" : tactic => `(tactic|
  simp_all [lift, bind_ok, Option.bind_eq_bind,
    bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,
    core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from,
    core.num.tryFromUScalar, bulksketch.core.result.Result.ok, UScalar.max])

private theorem exact_program (buckets words : Usize) :
    bulksketch.sketch.shape.record_bytes buckets words = Result.ok (checkedProgram buckets words) := by
  unfold bulksketch.sketch.shape.record_bytes checkedProgram
  cases descStep : Usize.checked_mul buckets 2#usize with
  | none => normalize_wire
  | some descriptors =>
    cases padStep : Usize.checked_add buckets 7#usize with
    | none => normalize_wire
    | some padded =>
      cases zeroStep : Usize.checked_div padded 8#usize with
      | none => normalize_wire
      | some zero =>
        cases wordStep : Usize.checked_mul words 8#usize with
        | none => normalize_wire
        | some wordBytes =>
          cases payloadStep : Usize.checked_add wordBytes zero with
          | none => normalize_wire
          | some payload =>
            cases headerStep : Usize.checked_add 24#usize descriptors <;>
              by_cases descFits : descriptors.val ≤ U32.max <;>
              by_cases payloadFits : payload.val ≤ U32.max <;> normalize_wire <;>
              split_ifs <;> normalize_wire

private theorem usize_at_least_u32 : U32.max ≤ Usize.max := by
  rcases Usize.bounds_eq with eq | eq
  · rw [eq]
  · rw [eq]
    simp [U32.max, U64.max, U32.numBits, U64.numBits]

private theorem add_fits (left right : Usize) (bound : left.val + right.val ≤ Usize.max) :
    ∃ out : Usize, Usize.checked_add left right = some out ∧ out.val = left.val + right.val := by
  have meaning := Usize.checked_add_bv_spec left right
  cases normal : Usize.checked_add left right with
  | none => rw [normal] at meaning; omega
  | some out => rw [normal] at meaning; exact ⟨out, rfl, meaning.2.1⟩

private theorem mul_fits (left right : Usize) (bound : left.val * right.val ≤ Usize.max) :
    ∃ out : Usize, Usize.checked_mul left right = some out ∧ out.val = left.val * right.val := by
  have meaning := Usize.checked_mul_bv_spec left right
  cases normal : Usize.checked_mul left right with
  | none => rw [normal] at meaning; omega
  | some out => rw [normal] at meaning; exact ⟨out, rfl, meaning.2.1⟩

private theorem div_by_eight (input : Usize) :
    ∃ out : Usize, Usize.checked_div input 8#usize = some out ∧ out.val = input.val / 8 := by
  have meaning := Usize.checked_div_bv_spec input 8#usize
  cases normal : Usize.checked_div input 8#usize with
  | none => rw [normal] at meaning; simp at meaning
  | some out => rw [normal] at meaning; exact ⟨out, rfl, by simpa using meaning.2.1⟩

private theorem checked_success (buckets words output : Usize)
    (normal : checkedProgram buckets words = some output) :
    fits buckets.val words.val ∧ output.val = wireBytes buckets.val words.val := by
  unfold checkedProgram at normal
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at normal
  obtain ⟨desc, descStep, padded, padStep, zero, zeroStep, payloadWords, wordsStep,
    payload, payloadStep, finalStep⟩ := normal
  split at finalStep
  next bounds =>
    obtain ⟨header, headerStep, totalStep⟩ := Option.bind_eq_some_iff.mp finalStep
    have descMeaning := Usize.checked_mul_bv_spec buckets 2#usize
    have padMeaning := Usize.checked_add_bv_spec buckets 7#usize
    have zeroMeaning := Usize.checked_div_bv_spec padded 8#usize
    have wordsMeaning := Usize.checked_mul_bv_spec words 8#usize
    have payloadMeaning := Usize.checked_add_bv_spec payloadWords zero
    have headerMeaning := Usize.checked_add_bv_spec 24#usize desc
    have totalMeaning := Usize.checked_add_bv_spec header payload
    rw [descStep] at descMeaning
    rw [padStep] at padMeaning
    rw [zeroStep] at zeroMeaning
    rw [wordsStep] at wordsMeaning
    rw [payloadStep] at payloadMeaning
    rw [headerStep] at headerMeaning
    rw [totalStep] at totalMeaning
    simp at descMeaning padMeaning zeroMeaning wordsMeaning headerMeaning
    unfold fits wireBytes payloadBytes
    omega
  next => contradiction

private theorem checked_complete (buckets words : Usize) (admitted : fits buckets.val words.val) :
    ∃ output : Usize, checkedProgram buckets words = some output := by
  have machineBound := usize_at_least_u32
  have fieldBound : 14 ≤ U32.max := by simp [U32.max, U32.numBits]
  unfold fits wireBytes payloadBytes at admitted
  obtain ⟨desc, descStep, descVal⟩ := mul_fits buckets 2#usize (by simp; omega)
  obtain ⟨padded, padStep, padVal⟩ := add_fits buckets 7#usize (by simp; omega)
  obtain ⟨zero, zeroStep, zeroVal⟩ := div_by_eight padded
  obtain ⟨payloadWords, wordsStep, wordsVal⟩ := mul_fits words 8#usize (by simp; omega)
  obtain ⟨payload, payloadStep, payloadVal⟩ := add_fits payloadWords zero (by
    rw [wordsVal, zeroVal, padVal]
    simp
    omega)
  have descBound : desc.val ≤ U32.max := by rw [descVal]; simp; omega
  have payloadBound : payload.val ≤ U32.max := by
    rw [payloadVal, wordsVal, zeroVal, padVal]
    simp
    omega
  obtain ⟨header, headerStep, headerVal⟩ := add_fits 24#usize desc (by
    rw [descVal]
    simp
    omega)
  obtain ⟨output, totalStep, _⟩ := add_fits header payload (by
    rw [headerVal, descVal, payloadVal, wordsVal, zeroVal, padVal]
    simp
    omega)
  refine ⟨output, ?_⟩
  simp [checkedProgram, descStep, padStep, zeroStep, wordsStep, payloadStep,
    descBound, payloadBound, headerStep, totalStep]

theorem record_bytes_refines : actualRecordBytesMatchesWireBounds := by
  intro buckets words
  refine ⟨checkedProgram buckets words, exact_program buckets words, ?_⟩
  cases result : checkedProgram buckets words with
  | none =>
    have rejected : ¬ fits buckets.val words.val := by
      intro admitted
      obtain ⟨output, normal⟩ := checked_complete buckets words admitted
      rw [result] at normal
      contradiction
    simp only [expectedBytes, ite_eq_right rejected, Option.map_none]
  | some output =>
    obtain ⟨admitted, value⟩ := checked_success buckets words output result
    simp only [expectedBytes, ite_eq_left admitted, Option.map_some, value]

end BulksketchBridge.ShapeWire
