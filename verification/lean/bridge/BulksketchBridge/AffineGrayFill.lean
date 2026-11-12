import Arithmetic.AffineEnumerateGenerated
import BulksketchBridge.RawMulTable
import BulksketchBridge.RebuiltLfsr
import Mathlib.Algebra.CharP.Algebra

namespace BulksketchBridge.AffineEnumerate

open Aeneas Aeneas.Std ControlFlow
open bulksketch.decode.affine

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

abbrev PointIterator := Aeneas.Std.MutableEnumerate.State U64
abbrev PointRestore := PointIterator → PointIterator

def pointIterator (points : Slice U64) (offset : Usize) : PointIterator :=
  ⟨⟨points, offset.val⟩, offset⟩

def replacePoint (state : PointIterator) (offset : Nat) (value : U64) : PointIterator :=
  { state with iter := { state.iter with slice := state.iter.slice.setAtNat offset value } }

/-- Direction of the Gray transition into a positive global point index. -/
def grayDirection (index : Nat) : Nat :=
  (BitVec.ofNat System.Platform.numBits index).ctz.toNat

def grayStep (basis : Slice U64) (index : Nat) (point : U64) : U64 :=
  if index = 0 then point else point ^^^ basis[grayDirection index]!

/-- Keep the immutable iterator snapshot through the scan and apply writes in
the exact order in which the generated continuation returns them. -/
def grayFill (basis : Slice U64) (start : Nat) (points : Slice U64)
    (offset : Nat) (point : U64) : Nat → U64 × Slice U64
  | 0 => (point, points)
  | count + 1 =>
    let nextPoint := grayStep basis (start + offset) point
    let result := grayFill basis start points (offset + 1) nextPoint count
    (result.1, result.2.setAtNat offset nextPoint)

private theorem iterator_next (points : Slice U64) (offset : Usize) (active : offset.val < points.length) :
    ∃ advanced : Usize, advanced.val = offset.val + 1 ∧
      Aeneas.Std.MutableEnumerate.next (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
        (pointIterator points offset) =
        .ok (some (offset, points[offset.val]!), pointIterator points advanced,
          fun (later : PointIterator) (replacement : Option (Usize × U64)) => match replacement with
            | none => later
            | some item => replacePoint later offset.val item.2) := by
  have safe : offset.val + (1#usize).val ≤ Usize.max := by
    have upper : points.length ≤ Usize.max := points.length_ineq
    change offset.val + 1 ≤ Usize.max
    omega
  obtain ⟨advanced, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Usize.add_spec (x := offset) (y := 1#usize) safe)
  have nextValue : advanced.val = offset.val + 1 := value
  have nextMut :
      core.slice.iter.IteratorIterMut.next (⟨points, offset.val⟩ : core.slice.iter.IterMut U64) =
        .ok (some points[offset.val]!, ⟨points, offset.val + 1⟩,
          fun (later : core.slice.iter.IterMut U64) (replacement : Option U64) => match replacement with
            | none => later
            | some item => { later with slice := later.slice.setAtNat offset.val item }) := by
    unfold core.slice.iter.IteratorIterMut.next
    have fits : offset.val < points.len.val := by rwa [Slice.len_val]
    rw [dite_eq_left fits]
    dsimp! only
    conv_rhs => rw [← Slice.Inhabited_getElem_eq_getElem! points offset.val active]
    congr 3
    funext later replacement
    cases replacement <;> rfl
  refine ⟨advanced, nextValue, ?_⟩
  simp only [Aeneas.Std.MutableEnumerate.next, pointIterator,
    bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT, nextMut, bind_ok, nextValue]
  dsimp! only
  simp only [normal, bind_ok]
  congr 3
  funext later replacement
  cases replacement <;> cases later <;> rfl

private theorem iterator_done (points : Slice U64) (offset : Usize) (exhausted : points.length ≤ offset.val) :
    Aeneas.Std.MutableEnumerate.next (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
      (pointIterator points offset) =
      .ok (none, pointIterator points offset, fun later _ => later) := by
  have stopped : ¬ offset.val < points.len.val := by rw [Slice.len_val]; omega
  have done : core.slice.iter.IteratorIterMut.next (⟨points, offset.val⟩ : core.slice.iter.IterMut U64) =
      .ok (none, ⟨points, offset.val⟩, fun later _ => later) := by
    unfold core.slice.iter.IteratorIterMut.next
    rw [dite_eq_right stopped]
  simp only [Aeneas.Std.MutableEnumerate.next, pointIterator,
    bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT, done, bind_ok]
  rfl

private theorem read_basis (basis : Slice U64) (index : Usize) (bound : index.val < basis.length) :
    Slice.index_usize basis index = .ok basis[index.val]! := by
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec basis index bound)
  rw [normal, value, Slice.getElem!_Nat_eq, List.Inhabited_getElem_eq_getElem! _ _ bound]

/-- The least-set-bit index of a positive value below 2^rank fits the basis. -/
theorem gray_direction_bound (word : Usize) (rank : Nat)
    (positive : 0 < word.val) (range : word.val < 2 ^ rank) :
    word.bv.ctz.toNat < rank := by
  have nonzero : word.bv ≠ 0 := by
    intro zero
    have valueZero : word.val = 0 := by change word.bv.toNat = 0; rw [zero]; rfl
    omega
  by_contra notBelow
  have large : 2 ^ rank ≤ 2 ^ word.bv.ctz.toNat := Nat.pow_le_pow_right (by decide) (by omega)
  have absent := Nat.testBit_lt_two_pow (range.trans_le large)
  have present := BitVec.getLsbD_true_ctz_of_ne_zero (x := word.bv) nonzero
  change word.val.testBit word.bv.ctz.toNat = true at present
  rw [absent] at present
  contradiction

private theorem gray_step_normal (basis : Slice U64) (start offset : Usize) (x : U64)
    (fits : start.val + offset.val ≤ Usize.max)
    (range : start.val + offset.val < 2 ^ basis.length) :
    ∃ index : Usize, (start + offset : Result Usize) = Result.ok index ∧
      (if index != 0#usize then do
        let zeros ← core.num.Usize.trailing_zeros index
        let direction ← lift (UScalar.cast .Usize zeros)
        let word ← Slice.index_usize basis direction
        lift (x ^^^ word)
      else Result.ok x) = .ok (grayStep basis (start.val + offset.val) x) := by
  obtain ⟨index, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Usize.add_spec (x := start) (y := offset) fits)
  refine ⟨index, normal, ?_⟩
  by_cases zero : index = 0#usize
  · have exactZero : start.val + offset.val = 0 := by rw [← value, zero]; rfl
    simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false, exactZero, grayStep, ite_true]
  · have positive : 0 < index.val := by
      by_contra notPositive
      exact zero (UScalar.eq_of_val_eq (by change index.val = 0; omega))
    have test : (index != 0#usize) = true := by simp [zero]
    obtain ⟨count, counted, exactCount, countBound⟩ := usize_trailing_zeros_spec index
    have bounded := gray_direction_bound index basis.length positive (by rwa [value])
    have castExact : (UScalar.cast .Usize count).val = count.val := by
      rw [UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      change count.val < 2 ^ System.Platform.numBits
      have platform := System.Platform.numBits_eq
      rcases platform with width | width <;> simp only [width] at countBound ⊢ <;> omega
    have read := read_basis basis (UScalar.cast .Usize count) (by rw [castExact, exactCount]; exact bounded)
    have exactDirection : grayDirection (start.val + offset.val) = count.val := by
      rw [grayDirection, ← value, exactCount]
      have repr : BitVec.ofNat System.Platform.numBits index.val = index.bv := by
        change BitVec.ofNat System.Platform.numBits index.bv.toNat = index.bv
        simp
      rw [repr]
    have indexNonzero : start.val + offset.val ≠ 0 := by omega
    simp only [test, ite_true, counted, bind_ok, lift, read, castExact,
      grayStep, indexNonzero, ite_false, exactDirection]

private theorem body_normal (basis points : Slice U64) (start offset : Usize) (x : U64) (back : PointRestore)
    (active : offset.val < points.length)
    (fits : start.val + points.length ≤ Usize.max)
    (range : start.val + points.length ≤ 2 ^ basis.length) :
    ∃ advanced : Usize, advanced.val = offset.val + 1 ∧
      let point := grayStep basis (start.val + offset.val) x
      enumerate_loop0_loop0.body basis start (pointIterator points offset) back x =
        .ok (.cont (pointIterator points advanced, (fun later => back (replacePoint later offset.val point)), point)) := by
  obtain ⟨advanced, value, next⟩ := iterator_next points offset active
  obtain ⟨index, added, pointNormal⟩ := gray_step_normal basis start offset x (by omega) (by omega)
  refine ⟨advanced, value, ?_⟩
  simp only [enumerate_loop0_loop0.body, next, bind_ok]
  dsimp! only
  simp only [added, bind_ok]
  by_cases zero : index = 0#usize
  · simp only [zero, bne_self_eq_false, Bool.false_eq_true, ite_false] at pointNormal ⊢
    have same : x = grayStep basis (start.val + offset.val) x := by
      simpa only [Result.ok.injEq] using pointNormal
    rw [← same]
  · have test : (index != 0#usize) = true := by simp [zero]
    simp only [test, ite_true] at pointNormal ⊢
    have transferred := congrArg (fun result : Result U64 => Aeneas.Std.bind result (fun point =>
      .ok (.cont (pointIterator points advanced, (fun later => back (replacePoint later offset.val point)), point) :
        ControlFlow (PointIterator × PointRestore × U64) (U64 × PointIterator × PointRestore)))) pointNormal
    simpa only [Bind.bind, Aeneas.Std.bind_assoc, bind_ok, lift] using transferred

theorem gray_fill_refines (basis points : Slice U64) (start offset : Usize) (point : U64) (back : PointRestore)
    (count : Nat) (remaining : offset.val + count = points.length)
    (fits : start.val + points.length ≤ Usize.max)
    (range : start.val + points.length ≤ 2 ^ basis.length) :
    let result := grayFill basis start.val points offset.val point count
    ∃ terminal : Usize, ∃ restore : PointRestore, terminal.val = points.length ∧
      enumerate_loop0_loop0 (pointIterator points offset) back basis point start =
        .ok (result.1, pointIterator points terminal, restore) ∧
      restore (pointIterator points terminal) = back (pointIterator result.2 terminal) := by
  induction count generalizing offset point back with
  | zero =>
    have stopped := iterator_done points offset (by omega)
    refine ⟨offset, back, by omega, ?_, rfl⟩
    unfold enumerate_loop0_loop0 loop
    dsimp only
    simp only [enumerate_loop0_loop0.body, stopped, bind_ok, grayFill]
    dsimp! only
    simp only [bind_ok]
  | succ count ih =>
    obtain ⟨advanced, advancedValue, body⟩ := body_normal basis points start offset point back (by omega) fits range
    let nextPoint := grayStep basis (start.val + offset.val) point
    obtain ⟨terminal, restore, terminalValue, ran, writes⟩ :=
      ih advanced nextPoint (fun later => back (replacePoint later offset.val nextPoint)) (by omega)
    refine ⟨terminal, restore, terminalValue, ?_, ?_⟩
    · conv_lhs => unfold enumerate_loop0_loop0 loop
      dsimp only
      rw [body, bind_ok]
      simpa only [enumerate_loop0_loop0, grayFill, advancedValue, nextPoint] using ran
    · rw [writes]
      simp only [grayFill, replacePoint, pointIterator, advancedValue, nextPoint]

/-- Binary-reflected Gray mask, independent of the implementation's XOR walk. -/
def grayMask (index : Nat) : Nat := index ^^^ (index >>> 1)

private theorem binary_delta (word : Usize) (positive : 0 < word.val) :
    ∀ bit,
      ((word.val - 1).testBit bit ^^ word.val.testBit bit) =
        decide (bit ≤ word.bv.ctz.toNat) := by
  let index := word.val
  let direction := word.bv.ctz.toNat
  have nonzero : word.bv ≠ 0 := by
    intro zero
    have valueZero : word.val = 0 := by change word.bv.toNat = 0; rw [zero]; rfl
    omega
  have directionSet : index.testBit direction = true := BitVec.getLsbD_true_ctz_of_ne_zero nonzero
  have earlierClear (bit : Nat) (before : bit < direction) : index.testBit bit = false :=
    BitVec.getLsbD_false_of_lt_ctz before
  have low : index % (2 ^ (direction + 1)) = 2 ^ direction := by
    apply Nat.eq_of_testBit_eq
    intro bit
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    by_cases earlier : bit < direction
    · simp [earlierClear bit earlier, show direction ≠ bit by omega]
    · by_cases exactBit : bit = direction
      · subst bit
        simp [directionSet]
      · simp [show ¬ bit < direction + 1 by omega, Ne.symm exactBit]
  let high := index / (2 ^ (direction + 1))
  have indexForm : index = (2 ^ (direction + 1)) * high + 2 ^ direction := by
    have split := Nat.mod_add_div index (2 ^ (direction + 1))
    rw [low, Nat.add_comm] at split
    exact split.symm
  have predecessorForm : index - 1 = (2 ^ (direction + 1)) * high + (2 ^ direction - 1) := by
    rw [indexForm]
    have directionPositive := Nat.two_pow_pos direction
    omega
  have baseRoom : 2 ^ direction < 2 ^ (direction + 1) :=
    Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  intro bit
  change ((index - 1).testBit bit ^^ index.testBit bit) = decide (bit ≤ direction)
  have previousBit : (index - 1).testBit bit = ((2 ^ (direction + 1)) * high + (2 ^ direction - 1)).testBit bit :=
    congrArg (fun n => n.testBit bit) predecessorForm
  have currentBit : index.testBit bit = ((2 ^ (direction + 1)) * high + 2 ^ direction).testBit bit :=
    congrArg (fun n => n.testBit bit) indexForm
  rw [previousBit, currentBit]
  rw [Nat.testBit_two_pow_mul_add high (show 2 ^ direction - 1 < 2 ^ (direction + 1) by omega),
    Nat.testBit_two_pow_mul_add high baseRoom]
  by_cases within : bit < direction + 1
  · rw [ite_eq_left within, ite_eq_left within, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
    by_cases earlier : bit < direction
    · simp [earlier, show direction ≠ bit by omega, show bit ≤ direction by omega]
    · have exactBit : bit = direction := by omega
      subst bit
      simp
  · simp [within, show ¬ bit ≤ direction by omega]

private theorem xor_pairs (a b c d : Bool) :
    ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The reflected Gray masks of successive positions differ in exactly the
least set bit of the new index. -/
theorem gray_mask_step (word : Usize) (positive : 0 < word.val) :
    grayMask (word.val - 1) ^^^ grayMask word.val = 2 ^ grayDirection word.val := by
  have direction : grayDirection word.val = word.bv.ctz.toNat := by
    unfold grayDirection
    have repr : BitVec.ofNat System.Platform.numBits word.val = word.bv := by
      change BitVec.ofNat System.Platform.numBits word.bv.toNat = word.bv
      simp
    rw [repr]
  apply Nat.eq_of_testBit_eq
  intro bit
  simp only [grayMask, Nat.testBit_xor, Nat.testBit_shiftRight, direction, Nat.testBit_two_pow]
  rw [xor_pairs, binary_delta word positive, binary_delta word positive]
  by_cases equal : bit = word.bv.ctz.toNat
  · subst bit
    simp
  · by_cases before : bit < word.bv.ctz.toNat
    · simp [show bit ≤ word.bv.ctz.toNat by omega, show 1 + bit ≤ word.bv.ctz.toNat by omega, Ne.symm equal]
    · simp [show ¬ bit ≤ word.bv.ctz.toNat by omega, show word.bv.ctz.toNat < 1 + bit by omega, Ne.symm equal]

/-- The forward Gray recurrence, indexed by the number of transitions applied. -/
def grayWalk (basis : Slice U64) (start : Nat) (point : U64) : Nat → U64
  | 0 => point
  | count + 1 => grayStep basis (start + count) (grayWalk basis start point count)

private theorem gray_walk_shift (basis : Slice U64) (start : Nat) (point : U64) (count : Nat) :
    grayWalk basis (start + 1) (grayStep basis start point) count =
      grayWalk basis start point (count + 1) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change grayStep basis (start + 1 + count) (grayWalk basis (start + 1) (grayStep basis start point) count) =
      grayStep basis (start + (count + 1)) (grayWalk basis start point (count + 1))
    rw [ih, show start + 1 + count = start + (count + 1) by omega]

/-- Every written point follows the forward recurrence. The output length
and words outside the requested index range are preserved. -/
theorem gray_fill_words (basis points : Slice U64) (start offset : Nat) (point : U64) (count : Nat)
    (room : offset + count ≤ points.length) :
    let result := grayFill basis start points offset point count
    result.1 = grayWalk basis (start + offset) point count ∧
      result.2.length = points.length ∧
      ∀ index, result.2[index]! =
        if offset ≤ index ∧ index < offset + count then
          grayWalk basis (start + offset) point (index - offset + 1)
        else points[index]! := by
  induction count generalizing offset point with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    intro index
    simp only [grayFill, Nat.add_zero, show ¬ (offset ≤ index ∧ index < offset) by omega, ite_false]
  | succ count ih =>
    let next := grayStep basis (start + offset) point
    let later := grayFill basis start points (offset + 1) next count
    obtain ⟨last, length, words⟩ := ih (offset + 1) next (by omega)
    have startNext : start + (offset + 1) = start + offset + 1 := by omega
    have lastExact : later.1 = grayWalk basis (start + offset) point (count + 1) := by
      simpa only [startNext, next, gray_walk_shift] using last
    refine ⟨lastExact, (Slice.setAtNat_length _ _ _).trans length, ?_⟩
    intro index
    change (later.2.setAtNat offset next)[index]! = _
    by_cases atOffset : index = offset
    · subst index
      have write : (later.2.setAtNat offset next)[offset]! = next := by
        simpa only [Slice.getElem!_Nat_eq] using
          (Slice.getElem!_Nat_setAtNat_eq later.2 offset next (by rw [length]; omega))
      rw [write, ite_eq_left ⟨Nat.le_refl _, by omega⟩, Nat.sub_self]
      rfl
    · have preserved : (later.2.setAtNat offset next)[index]! = later.2[index]! := by
        simpa only [Slice.getElem!_Nat_eq] using
          (Slice.getElem!_Nat_setAtNat_ne later.2 offset index next (Ne.symm atOffset))
      rw [preserved]
      have lookup : later.2[index]! =
          if offset + 1 ≤ index ∧ index < offset + 1 + count then
            grayWalk basis (start + (offset + 1)) next (index - (offset + 1) + 1)
          else points[index]! := words index
      rw [lookup]
      have sameRange : (offset + 1 ≤ index ∧ index < offset + 1 + count) ↔
          (offset ≤ index ∧ index < offset + (count + 1)) := by omega
      by_cases inside : offset ≤ index ∧ index < offset + (count + 1)
      · rw [ite_eq_left (sameRange.mpr inside), ite_eq_left inside,
          startNext, show next = grayStep basis (start + offset) point from rfl, gray_walk_shift]
        congr 1
        omega
      · rw [ite_eq_right (mt sameRange.mp inside), ite_eq_right inside]

open DenseCoefficient RebuiltLfsr

/-- The generated outer batch's exact prefix setup and three backward calls,
followed by an arbitrary continuation on its restored points. -/
def fillPointsPrefix {α : Type} (basis points : Slice U64) (start len : Usize) (x : U64)
    (finish : U64 → Slice U64 → Result α) : Result α := do
  let (window, restorePrefixBack) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeToUsizeSlice U64) points ⟨len⟩
  let (iterator, restoreIterator) ← core.slice.Slice.iter_mut window
  let (enumerated, restoreEnumerate) ← Aeneas.Std.MutableEnumerate.construct
    (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64) iterator
  let (point, terminal, restore) ← enumerate_loop0_loop0 enumerated (fun e => e) basis x start
  finish point (restorePrefixBack (restoreIterator (restoreEnumerate (restore terminal))))

theorem gray_fill_prefix_refines {α : Type} (basis points : Slice U64) (start len : Usize) (x : U64)
    (finish : U64 → Slice U64 → Result α) (room : len.val ≤ points.length)
    (fits : start.val + len.val ≤ Usize.max)
    (range : start.val + len.val ≤ 2 ^ basis.length) :
    let filled := grayFill basis start.val (prefixSlice points len.val) 0 x len.val
    fillPointsPrefix basis points start len x finish = finish filled.1 (restorePrefix points filled.2) := by
  let window := prefixSlice points len.val
  have width : window.length = len.val := by rw [show window = prefixSlice points len.val from rfl,
    prefix_length, Nat.min_eq_left room]
  have zero : (0#usize).val = 0 := by simp
  obtain ⟨terminal, restore, _, ran, written⟩ :=
    gray_fill_refines basis window start 0#usize x (fun e => e) len.val
      (by rw [width, zero, Nat.zero_add]) (by rwa [width]) (by rwa [width])
  have enumerated : Aeneas.Std.MutableEnumerate.construct
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
      ⟨window, 0⟩ = .ok (pointIterator window 0#usize, fun e => e.iter) := rfl
  simp only [fillPointsPrefix, Slice.index_mut_SliceIndexRangeToUsizeSliceInst,
    prefix_normal points len room, bind_ok]
  dsimp! only
  simp only [core.slice.Slice.iter_mut, bind_ok]
  dsimp! only
  change (do
    let (state, restoreEnum) ← Aeneas.Std.MutableEnumerate.construct
      (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64) ⟨window, 0⟩
    let (point, terminal, restore) ← enumerate_loop0_loop0 state (fun e => e) basis x start
    finish point (restorePrefix points (restoreEnum (restore terminal)).slice)) = _
  simp only [Bind.bind, enumerated, bind_ok]
  simp only [ran, bind_ok]
  rw [written]
  simp only [pointIterator, zero, window]

open Algebra.Gf64
open scoped BigOperators

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

/-- Coordinate mask in the binary span, transported to the verified GF64
word interpretation. -/
noncomputable def basisMaskValue (basis : Slice U64) (mask : Nat) : Field :=
  ∑ bit ∈ Finset.range basis.length, if mask.testBit bit then toField basis[bit]!.bv else 0

noncomputable def grayPointValue (basis : Slice U64) (base : Field) (index : Nat) : Field :=
  base + basisMaskValue basis (grayMask index)

private theorem mask_sum_toggle (basis : Slice U64) (left right direction : Nat)
    (inside : direction < basis.length) (toggle : left ^^^ right = 2 ^ direction) :
    basisMaskValue basis left + basisMaskValue basis right = toField basis[direction]!.bv := by
  have atBit (bit : Nat) :
      (if left.testBit bit then toField basis[bit]!.bv else 0) +
        (if right.testBit bit then toField basis[bit]!.bv else 0) =
        if bit = direction then toField basis[bit]!.bv else 0 := by
    have bitToggle := congrArg (fun value : Nat => value.testBit bit) toggle
    change (left ^^^ right).testBit bit = (2 ^ direction).testBit bit at bitToggle
    simp only [Nat.testBit_xor, Nat.testBit_two_pow] at bitToggle
    by_cases here : bit = direction
    · subst bit
      simp only [decide_true] at bitToggle
      cases l : left.testBit direction <;> cases r : right.testBit direction <;>
        simp_all
    · have reverse : direction ≠ bit := Ne.symm here
      simp only [reverse, decide_false] at bitToggle
      cases l : left.testBit bit <;> cases r : right.testBit bit <;>
        simp_all [CharTwo.add_self_eq_zero]
  unfold basisMaskValue
  rw [← Finset.sum_add_distrib]
  simp only [atBit]
  rw [Finset.sum_eq_single direction]
  · simp
  · intro bit _ distinct
    simp [distinct]
  · intro missing
    exact (missing (Finset.mem_range.mpr inside)).elim

theorem gray_point_zero (basis : Slice U64) (base : Field) :
    grayPointValue basis base 0 = base := by
  simp [grayPointValue, grayMask, basisMaskValue]

/-- The machine-word update advances the coset point at the reflected Gray
mask, when its input is the preceding coset point. -/
theorem gray_step_field (basis : Slice U64) (base : Field) (index : Usize) (point : U64)
    (positive : 0 < index.val) (range : index.val < 2 ^ basis.length)
    (preceding : toField point.bv = grayPointValue basis base (index.val - 1)) :
    toField (grayStep basis index.val point).bv = grayPointValue basis base index.val := by
  have directionValue : grayDirection index.val = index.bv.ctz.toNat := by
    unfold grayDirection
    have repr : BitVec.ofNat System.Platform.numBits index.val = index.bv := by
      change BitVec.ofNat System.Platform.numBits index.bv.toNat = index.bv
      simp
    rw [repr]
  have inside : grayDirection index.val < basis.length := by
    rw [directionValue]
    exact gray_direction_bound index basis.length positive range
  have toggled := mask_sum_toggle basis _ _ _ inside (gray_mask_step index positive)
  rw [grayStep, ite_eq_right (Nat.ne_of_gt positive)]
  change toField (point.bv ^^^ basis[grayDirection index.val]!.bv) = _
  rw [toField_xor, preceding]
  unfold grayPointValue
  rw [← toggled, add_assoc, ← add_assoc (basisMaskValue basis (grayMask (index.val - 1))),
    CharTwo.add_self_eq_zero, zero_add]

/-- A whole forward walk starts at the previous global Gray coordinate and
ends at the last processed coordinate. Index zero keeps the base point. -/
theorem gray_walk_field (basis : Slice U64) (base : Field) (start count : Nat) (point : U64)
    (fits : start + count ≤ Usize.max) (range : start + count ≤ 2 ^ basis.length)
    (preceding : toField point.bv = grayPointValue basis base (start - 1)) :
    toField (grayWalk basis start point count).bv = grayPointValue basis base (start + count - 1) := by
  induction count with
  | zero => simpa only [grayWalk, Nat.add_zero] using preceding
  | succ count ih =>
    have before := ih (by omega) (by omega)
    by_cases zero : start + count = 0
    · simp only [grayWalk, grayStep, zero, ite_true]
      rw [before, show start + (count + 1) - 1 = start + count - 1 by omega]
    · let index : Usize := ⟨BitVec.ofNat System.Platform.numBits (start + count)⟩
      have bound : start + count < 2 ^ System.Platform.numBits := by
        have maxValue : Usize.max = 2 ^ System.Platform.numBits - 1 := by
          simp only [Usize.max, Usize.numBits, UScalarTy.numBits]
        rw [maxValue] at fits
        omega
      have indexValue : index.val = start + count := by
        change (BitVec.ofNat System.Platform.numBits (start + count)).toNat = _
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
      have earlier : toField (grayWalk basis start point count).bv =
          grayPointValue basis base (index.val - 1) := by rw [indexValue]; exact before
      have step := gray_step_field basis base index (grayWalk basis start point count)
        (by rw [indexValue]; omega) (by rw [indexValue]; omega) earlier
      simpa only [indexValue, grayWalk, show start + (count + 1) - 1 = start + count by omega] using step

/-- The completed mutable buffer denotes the exact consecutive Gray coset
points at every written local index. -/
theorem gray_fill_field_points (basis points : Slice U64) (base : Field)
    (start offset count : Nat) (point : U64)
    (room : offset + count ≤ points.length)
    (fits : start + offset + count ≤ Usize.max)
    (range : start + offset + count ≤ 2 ^ basis.length)
    (preceding : toField point.bv = grayPointValue basis base (start + offset - 1)) :
    let filled := grayFill basis start points offset point count
    toField filled.1.bv = grayPointValue basis base (start + offset + count - 1) ∧
      ∀ i, offset ≤ i → i < offset + count →
        toField filled.2[i]!.bv = grayPointValue basis base (start + i) := by
  obtain ⟨last, _, words⟩ := gray_fill_words basis points start offset point count room
  refine ⟨?_, ?_⟩
  · rw [last]
    exact gray_walk_field basis base (start + offset) count point fits range preceding
  · intro i lower upper
    rw [words i, ite_eq_left ⟨lower, upper⟩]
    rw [gray_walk_field basis base (start + offset) (i - offset + 1) point (by omega) (by omega) preceding,
      show start + offset + (i - offset + 1) - 1 = start + i by omega]

theorem gray_mask_bound (index rank : Nat) (bounded : index < 2 ^ rank) :
    grayMask index < 2 ^ rank := by
  exact Nat.xor_lt_two_pow bounded ((Nat.shiftRight_le index 1).trans_lt bounded)

/-- Reflected Gray coordinates determine every original binary index. -/
theorem gray_mask_injective : Function.Injective grayMask := by
  have grayShift (index : Nat) : grayMask (index >>> 1) = grayMask index >>> 1 := by
    unfold grayMask
    rw [Nat.shiftRight_xor_distrib]
  suffices ∀ total left right : Nat, left + right = total → grayMask left = grayMask right → left = right by
    intro left right equal
    exact this (left + right) left right rfl equal
  intro total
  induction total using Nat.strong_induction_on with
  | h total ih =>
    intro left right summed equal
    by_cases zero : total = 0
    · omega
    · have shrink : (left >>> 1) + (right >>> 1) < total := by
        simp only [Nat.shiftRight_eq_div_pow, pow_one]
        omega
      have high : left >>> 1 = right >>> 1 := ih _ shrink _ _ rfl (by rw [grayShift, grayShift, equal])
      apply Nat.eq_of_testBit_eq
      intro bit
      cases bit with
      | zero =>
        have bitOne := congrArg (fun n : Nat => n.testBit 0) high
        have bitZero := congrArg (fun n : Nat => n.testBit 0) equal
        simp only [Nat.testBit_shiftRight] at bitOne
        simp only [grayMask, Nat.testBit_xor, Nat.testBit_shiftRight, bitOne] at bitZero
        cases l : left.testBit 0 <;> cases r : right.testBit 0 <;> cases h : right.testBit 1 <;> simp_all
      | succ bit =>
        have matching := congrArg (fun n : Nat => n.testBit bit) high
        simpa only [Nat.testBit_shiftRight, Nat.succ_eq_add_one, Nat.add_comm 1 bit] using matching

/-- Every rank-bit coordinate occurs exactly once in a full reflected Gray walk. -/
theorem gray_mask_permutation (rank : Nat) :
    Function.Bijective (fun index : Fin (2 ^ rank) =>
      (⟨grayMask index.val, gray_mask_bound index.val rank index.isLt⟩ : Fin (2 ^ rank))) := by
  have injective : Function.Injective (fun index : Fin (2 ^ rank) =>
      (⟨grayMask index.val, gray_mask_bound index.val rank index.isLt⟩ : Fin (2 ^ rank))) := by
    intro left right equal
    apply Fin.ext
    exact gray_mask_injective (congrArg Fin.val equal)
  exact ⟨injective, Finite.surjective_of_injective injective⟩

end BulksketchBridge.AffineEnumerate
