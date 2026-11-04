import BulksketchProofs.Field.MapsCertificates
import BulksketchProofs.Field.Period

namespace BulksketchProofs.Field.Maps

private theorem select_xor (word : BitVec 64) (first second : Bool) :
    (if first ^^ second then word else 0) =
      (if first then word else 0) ^^^ (if second then word else 0) := by
  cases first <;> cases second <;> simp

theorem traceBit_zero : traceBit 0 = false := by simp [traceBit]

theorem traceBit_xor (first second : BitVec 64) :
    traceBit (first ^^^ second) = (traceBit first ^^ traceBit second) := by
  simp only [traceBit, BitVec.getLsbD_xor]
  simp only [Bool.xor_assoc]
  rw [Bool.xor_left_comm (second.getLsbD 61) (first.getLsbD 63) (second.getLsbD 63)]

theorem traceWord_zero : traceWord 0 = 0 := by
  rw [traceWord, traceBit_zero]
  rfl

theorem traceWord_xor (first second : BitVec 64) :
    traceWord (first ^^^ second) = traceWord first ^^^ traceWord second := by
  simp only [traceWord, traceBit_xor, select_xor]

theorem tracePrefix_zero (count : Nat) : tracePrefix count 0 = 0 := by
  induction count with
  | zero => rfl
  | succ count ih => rw [tracePrefix, ih, Period.squareWord_zero]; rfl

theorem tracePrefix_xor (count : Nat) (first second : BitVec 64) :
    tracePrefix count (first ^^^ second) = tracePrefix count first ^^^ tracePrefix count second := by
  induction count with
  | zero => simp [tracePrefix]
  | succ count ih =>
    simp only [tracePrefix, ih, Period.squareWord_xor]
    ac_rfl

theorem tracePrefix_step (count : Nat) (input : BitVec 64) :
    tracePrefix (count + 1) input = tracePrefix count input ^^^ Period.iterateSquare count input := by
  induction count with
  | zero =>
    simp only [tracePrefix, Period.iterateSquare]
    rw [Period.squareWord_zero]
  | succ count ih =>
    calc
      tracePrefix (count + 1 + 1) input =
          Period.squareWord (tracePrefix (count + 1) input) ^^^ input := rfl
      _ = Period.squareWord (tracePrefix count input ^^^ Period.iterateSquare count input) ^^^ input := by rw [ih]
      _ = (Period.squareWord (tracePrefix count input) ^^^
          Period.squareWord (Period.iterateSquare count input)) ^^^ input := by rw [Period.squareWord_xor]
      _ = tracePrefix (count + 1) input ^^^ Period.iterateSquare (count + 1) input := by
        simp only [tracePrefix, Period.iterateSquare]
        ac_rfl

theorem tracePrefix_sum (count : Nat) (input : BitVec 64) :
    tracePrefix count input = traceSumPrefix count input := by
  induction count with
  | zero => rfl
  | succ count ih => rw [tracePrefix_step, traceSumPrefix, ih]

theorem absoluteTrace_is_sum : MapsChallenges.traceIsTheConjugateSum :=
  tracePrefix_sum 64

theorem absoluteTrace_eq_selector : MapsChallenges.absoluteTraceMatchesSelector := by
  exact Period.xor_linear_basis_ext (tracePrefix 64) traceWord
    (tracePrefix_zero 64) traceWord_zero (tracePrefix_xor 64) traceWord_xor
    trace_basis_certificate

theorem quadraticPrefix_zero (count : Nat) : quadraticPrefix 0 count = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [quadraticPrefix, ih]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.false_eq_true,
      ↓reduceIte, BitVec.xor_zero]

theorem quadraticPrefix_xor (count : Nat) (first second : BitVec 64) :
    quadraticPrefix (first ^^^ second) count =
      quadraticPrefix first count ^^^ quadraticPrefix second count := by
  induction count with
  | zero => simp [quadraticPrefix]
  | succ count ih =>
    simp only [quadraticPrefix, ih, BitVec.getLsbD_xor, select_xor]
    ac_rfl

theorem quadraticValue_zero : quadraticValue 0 = 0 := quadraticPrefix_zero 64
theorem quadraticValue_xor (first second : BitVec 64) :
    quadraticValue (first ^^^ second) = quadraticValue first ^^^ quadraticValue second :=
  quadraticPrefix_xor 64 first second

theorem chunkValue_image (row : Nat) (small : row < 16) (nibble : BitVec 4) :
    chunkValue row nibble = quadraticValue (nibble.setWidth 64 <<< (4 * row)) :=
  chunk_entries_match ⟨row, small⟩ nibble

theorem chunkPrefix_zero (count : Nat) (small : count ≤ 16) : chunkPrefix 0 count = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [chunkPrefix, ih (by omega)]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_ushiftRight, BitVec.setWidth_zero, BitVec.zero_xor]
    rw [chunkValue_image count (by omega)]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.setWidth_zero, BitVec.zero_shiftLeft] using quadraticValue_zero

theorem chunkPrefix_xor (count : Nat) (small : count ≤ 16) (first second : BitVec 64) :
    chunkPrefix (first ^^^ second) count =
      chunkPrefix first count ^^^ chunkPrefix second count := by
  induction count with
  | zero => simp [chunkPrefix]
  | succ count ih =>
    rw [chunkPrefix, chunkPrefix, chunkPrefix, ih (by omega)]
    rw [chunkValue_image count (by omega), chunkValue_image count (by omega),
      chunkValue_image count (by omega)]
    simp only [BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor,
      BitVec.shiftLeft_xor_distrib, quadraticValue_xor]
    ac_rfl

theorem chunk_lookup_eq_matrix : MapsChallenges.chunkLookupMatchesMatrixForEveryWord := by
  exact Period.xor_linear_basis_ext quadraticChunkValue quadraticValue
    (chunkPrefix_zero 16 (by decide)) quadraticValue_zero
    (chunkPrefix_xor 16 (by decide)) quadraticValue_xor chunks_basis_certificate

theorem quadratic_zero : quadratic 0 = 0 := by rw [quadratic, Period.squareWord_zero]; rfl
theorem quadratic_xor (first second : BitVec 64) :
    quadratic (first ^^^ second) = quadratic first ^^^ quadratic second := by
  simp only [quadratic, Period.squareWord_xor]
  ac_rfl

theorem traceProjection_zero : traceProjection 0 = 0 := by rw [traceProjection, traceBit_zero]; rfl
theorem traceProjection_xor (first second : BitVec 64) :
    traceProjection (first ^^^ second) = traceProjection first ^^^ traceProjection second := by
  simp only [traceProjection, traceBit_xor, select_xor]
  ac_rfl

theorem normalizedProjection_zero : normalizedProjection 0 = 0 := by simp [normalizedProjection]
theorem normalizedProjection_xor (first second : BitVec 64) :
    normalizedProjection (first ^^^ second) =
      normalizedProjection first ^^^ normalizedProjection second := by
  simp only [normalizedProjection, BitVec.getLsbD_xor, select_xor]
  ac_rfl

theorem quadratic_right_inverse : MapsChallenges.quadraticRightInverseProjection := by
  exact Period.xor_linear_basis_ext (fun input => quadratic (quadraticValue input)) traceProjection
    (by rw [quadraticValue_zero, quadratic_zero]) traceProjection_zero
    (by intros; rw [quadraticValue_xor, quadratic_xor]) traceProjection_xor
    right_inverse_basis_certificate

theorem quadratic_left_inverse : MapsChallenges.quadraticLeftInverseProjection := by
  exact Period.xor_linear_basis_ext (fun input => quadraticValue (quadratic input)) normalizedProjection
    (by rw [quadratic_zero, quadraticValue_zero]) normalizedProjection_zero
    (by intros; rw [quadratic_xor, quadraticValue_xor]) normalizedProjection_xor
    left_inverse_basis_certificate

theorem traceWord_eq_zero_iff (input : BitVec 64) : traceWord input = 0 ↔ traceBit input = false := by
  simp only [traceWord]
  cases traceBit input <;> decide

theorem quadratic_trace_zero : MapsChallenges.quadraticMapHasZeroTrace := by
  intro input
  apply (traceWord_eq_zero_iff _).mp
  exact Period.xor_linear_basis_ext (fun input => traceWord (quadratic input)) (fun _ => 0)
    (by rw [quadratic_zero, traceWord_zero]) rfl
    (by intros; rw [quadratic_xor, traceWord_xor]) (by intros; simp)
    trace_quadratic_basis_certificate input

theorem quadraticValue_bit_zero : MapsChallenges.chosenSolutionHasZeroFreeBit := by
  intro input
  have masked := Period.xor_linear_basis_ext
    (fun input => quadraticValue input &&& 1) (fun _ => (0 : BitVec 64))
    (by rw [quadraticValue_zero]; simp) rfl
    (by
      intro first second
      rw [quadraticValue_xor]
      apply BitVec.eq_of_getLsbD_eq
      intro index hi
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
      cases (quadraticValue first).getLsbD index <;>
        cases (quadraticValue second).getLsbD index <;> simp) (by intros; simp)
    normalized_basis_certificate input
  have bit := congrArg (fun word : BitVec 64 => word.getLsbD 0) masked
  simpa [-BitVec.getLsbD_eq_getElem] using bit

theorem quadratic_solvable_iff_trace_zero : MapsChallenges.quadraticSolutionsExactlyTraceZero := by
  intro input
  constructor
  · rintro ⟨solution, equation⟩
    rw [← equation]
    exact quadratic_trace_zero solution
  · intro zeroTrace
    refine ⟨quadraticValue input, ?_⟩
    rw [quadratic_right_inverse]
    simp [traceProjection, zeroTrace]

theorem normalized_solution_unique : MapsChallenges.normalizedSolutionIsUnique := by
  intro input solution equation normalized
  have projection := quadratic_left_inverse solution
  rw [equation] at projection
  rw [normalizedProjection, normalized] at projection
  simp only [Bool.false_eq_true, ↓reduceIte] at projection
  simp only [BitVec.ofNat_eq_ofNat, BitVec.xor_zero] at projection
  exact projection.symm

end BulksketchProofs.Field.Maps
