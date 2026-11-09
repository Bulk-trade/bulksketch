import Arithmetic.NativeDeflateGenerated
import BulksketchBridge.DeflateSyntheticAlgebra
import BulksketchBridge.DenseDivRemCursor
import BulksketchBridge.ReconstructionLoop

namespace BulksketchBridge.Deflation

open Aeneas Aeneas.Std ControlFlow Result
open bulksketch.decode.stages.Execution bulksketch.backend.contract
open DenseDivision (reverseRange reverse_next reverse_done nextReverse)

set_option maxRecDepth 4096
set_option maxHeartbeats 2100000

def syntheticFold (locator : Slice U64) (root : U64) : Nat → Slice U64 → Slice U64
  | 0, quotient => quotient
  | n + 1, quotient =>
    syntheticFold locator root n
      (quotient.setAtNat n (locator[n + 1]! ^^^ mulWord root quotient[n + 1]!))

private theorem read_normal (words : Slice U64) (i : Usize) (fits : i.val < words.length) :
    Slice.index_usize words i = .ok words[i.val]! := by
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words i fits)
  rw [normal, value, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! words.val i.val fits)

/-- The exact original inner reverse loop fills the lower quotient words
with the synthetic recurrence and no other writes. -/
theorem native_synthetic_loop {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : ∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b))
    (locator quotient : Slice U64) (root : U64) (stop : Usize)
    (positive : 0 < stop.val) (locatorRoom : stop.val ≤ locator.length)
    (quotientRoom : stop.val ≤ quotient.length) :
    deflate_loop0_loop0 field kernels (reverseRange 1#usize stop) locator quotient root =
      .ok (syntheticFold locator root (stop.val - 1) quotient) := by
  suffices ∀ (remaining : Nat) (stop : Usize) (quotient : Slice U64),
      0 < stop.val → stop.val ≤ locator.length → stop.val ≤ quotient.length →
      stop.val - 1 = remaining →
      deflate_loop0_loop0 field kernels (reverseRange 1#usize stop) locator quotient root =
        .ok (syntheticFold locator root remaining quotient) by
    exact this _ stop quotient positive locatorRoom quotientRoom rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro stop quotient positive locRoom qRoom measure
    by_cases active : 1 < stop.val
    · obtain ⟨top, subTop, topVal, _⟩ := RawMulTable.normal_of_spec _ _
        (Usize.sub_spec (x := stop) (y := 1#usize) (by change 1 ≤ stop.val; omega))
      change top.val = stop.val - 1 at topVal
      have reverse := reverse_next 1#usize stop top (by change 1 < stop.val; exact active) (by omega)
      have topPositive : 0 < top.val := by omega
      obtain ⟨lower, subLower, lowerVal, _⟩ := RawMulTable.normal_of_spec _ _
        (Usize.sub_spec (x := top) (y := 1#usize) (by change 1 ≤ top.val; omega))
      change lower.val = top.val - 1 at lowerVal
      let next := quotient.setAtNat lower.val (locator[top.val]! ^^^ mulWord root quotient[top.val]!)
      have step : deflate_loop0_loop0.body field kernels locator root (reverseRange 1#usize stop) quotient =
          .ok (.cont (reverseRange 1#usize top, next)) := by
        simp only [deflate_loop0_loop0.body, reverse, bind_ok]
        dsimp! only
        simp only [read_normal locator top (by omega), read_normal quotient top (by omega),
          mul, subLower, bind_ok, lift, Reconstruction.update_normal quotient lower _ (by omega), next]
      have nextLength : next.length = quotient.length := Slice.setAtNat_length ..
      have rest := ih (top.val - 1) (by omega) top next topPositive (by omega)
        (by rw [nextLength]; omega) rfl
      have fuel : remaining = (top.val - 1) + 1 := by omega
      rw [deflate_loop0_loop0, loop]
      dsimp only
      rw [step]
      simp only [bind_ok]
      rw [fuel, syntheticFold]
      have index : top.val - 1 + 1 = top.val := by omega
      simpa only [deflate_loop0_loop0, next, lowerVal, index] using rest
    · have fuel : remaining = 0 := by omega
      have reverse := reverse_done 1#usize stop (by change stop.val ≤ 1; omega)
      rw [deflate_loop0_loop0, loop, fuel, syntheticFold]
      simp only [deflate_loop0_loop0.body, reverse, bind_ok]
      dsimp! only
      simp only [bind_ok]

theorem synthetic_fold_length (locator quotient : Slice U64) (root : U64) (count : Nat) :
    (syntheticFold locator root count quotient).length = quotient.length := by
  induction count generalizing quotient with
  | zero => rfl
  | succ count ih =>
    rw [syntheticFold, ih, Slice.setAtNat_length]

theorem synthetic_fold_keeps_high (locator quotient : Slice U64) (root : U64) (count j : Nat)
    (high : count ≤ j) :
    (syntheticFold locator root count quotient)[j]! = quotient[j]! := by
  induction count generalizing quotient with
  | zero => rfl
  | succ count ih =>
    rw [syntheticFold, ih _ (by omega)]
    simpa only [Slice.getElem!_Nat_eq] using (Slice.getElem!_Nat_setAtNat_ne quotient count j
      (locator[count + 1]! ^^^ mulWord root quotient[count + 1]!) (by omega))

theorem synthetic_fold_columns (locator quotient : Slice U64) (root : U64) (count : Nat)
    (fits : count < quotient.length) :
    let output := syntheticFold locator root count quotient
    ∀ i < count, output[i]! = locator[i + 1]! ^^^ mulWord root output[i + 1]! := by
  induction count generalizing quotient with
  | zero => intro i absent; omega
  | succ count ih =>
    let next := quotient.setAtNat count (locator[count + 1]! ^^^ mulWord root quotient[count + 1]!)
    change ∀ i < count + 1, (syntheticFold locator root count next)[i]! =
      locator[i + 1]! ^^^ mulWord root (syntheticFold locator root count next)[i + 1]!
    intro i inside
    by_cases earlier : i < count
    · apply ih next (by unfold next; rw [Slice.setAtNat_length]; omega) i earlier
    · have atHead : i = count := by omega
      subst i
      rw [synthetic_fold_keeps_high locator next root count count (by omega),
        synthetic_fold_keeps_high locator next root count (count + 1) (by omega)]
      have atSet : next[count]! = locator[count + 1]! ^^^ mulWord root quotient[count + 1]! := by
        unfold next
        simpa only [Slice.getElem!_Nat_eq] using (Slice.getElem!_Nat_setAtNat_eq quotient count
          (locator[count + 1]! ^^^ mulWord root quotient[count + 1]!) (by omega))
      have after : next[count + 1]! = quotient[count + 1]! := by
        unfold next
        simpa only [Slice.getElem!_Nat_eq] using (Slice.getElem!_Nat_setAtNat_ne quotient count
          (count + 1) (locator[count + 1]! ^^^ mulWord root quotient[count + 1]!) (by omega))
      rw [atSet, after]

#print axioms native_synthetic_loop
#print axioms synthetic_fold_columns

end BulksketchBridge.Deflation
