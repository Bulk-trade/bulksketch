import BulksketchBridge.SlicePolynomial
import BulksketchBridge.PortableHorner
import Mathlib.Data.List.Fold

namespace BulksketchBridge.PortableHorner

open Aeneas.Std BulksketchBridge.Algebra.Gf64 SliceKernels
open scoped BigOperators

private theorem fold_field (words : List U64) (value point : U64) :
    toField (words.foldl (fun acc coefficient =>
      (⟨multiplyWord acc.bv point.bv⟩ : U64) ^^^ coefficient) value).bv =
      words.foldl (fun acc coefficient => acc * toField point.bv + toField coefficient.bv)
        (toField value.bv) := by
  induction words generalizing value with
  | nil => rfl
  | cons coefficient rest ih =>
    simp only [List.foldl_cons, ih]
    change rest.foldl (fun acc word => acc * toField point.bv + toField word.bv)
      (toField (multiplyWord value.bv point.bv ^^^ coefficient.bv)) = _
    rw [toField_xor, toField_mul]

private theorem reverse_fold_field (coefficients : List U64) (point : U64) :
    toField (PortableHornerChallenges.evalWord coefficients point).bv =
      coefficients.foldr (fun coefficient value => value * toField point.bv + toField coefficient.bv) 0 := by
  unfold PortableHornerChallenges.evalWord
  rw [List.foldr_eq_foldl_reverse]
  cases scan : coefficients.reverse with
  | nil =>
    simp only [List.foldl_nil]
    exact toField_zero
  | cons leading rest =>
    simp only [List.foldl_cons, zero_mul, zero_add]
    exact fold_field rest leading point

private theorem foldr_coefficients (words : List U64) (point : Field) :
    words.foldr (fun coefficient value => value * point + toField coefficient.bv) 0 =
      ∑ i ∈ Finset.range words.length, toField words[i]!.bv * point ^ i := by
  induction words with
  | nil => simp
  | cons constant rest ih =>
    rw [List.foldr_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [pow_zero, mul_one, List.getElem!_cons_zero, List.getElem!_cons_succ,
      pow_succ, ← mul_assoc, Finset.sum_mul]

/-- The ascending slice polynomial evaluates to the field interpretation of
the reverse native Horner fold, including empty and constant slices. -/
theorem horner_word_evaluates (coefficients : Slice U64) (point : U64) :
    toField (PortableHornerChallenges.evalWord coefficients.val point).bv =
      (slicePolynomial coefficients).eval (toField point.bv) := by
  rw [reverse_fold_field, foldr_coefficients]
  simp only [slicePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    Slice.getElem!_Nat_eq, Slice.length]

/-- The actual Portable body produces the exact field evaluation at each point. -/
def ActualPortableHornerEvaluatesPolynomial : Prop :=
  ∀ coefficients points out : Slice U64, out.length = points.length →
    ∃ result,
      bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField coefficients points out =
        Result.ok result ∧ result.length = points.length ∧
      ∀ i, i < points.length →
        toField result[i]!.bv = (slicePolynomial coefficients).eval (toField points[i]!.bv)

theorem horner_many_polynomial_refines : ActualPortableHornerEvaluatesPolynomial := by
  intro coefficients points out lengths
  have frame := horner_many_refines coefficients points out
  dsimp only at frame
  rw [ite_eq_left lengths] at frame
  obtain ⟨result, normal, length, words⟩ := frame
  refine ⟨result, normal, length.trans lengths, ?_⟩
  intro index bounded
  have word : result[index]! = PortableHornerChallenges.evalWord coefficients.val points[index]! := by
    simp only [Slice.getElem!_Nat_eq, words]
    rw [← List.Inhabited_getElem_eq_getElem! _ _ (by simpa using bounded), List.getElem_map,
      List.Inhabited_getElem_eq_getElem! _ _ bounded]
  rw [word]
  exact horner_word_evaluates coefficients points[index]!

end BulksketchBridge.PortableHorner
