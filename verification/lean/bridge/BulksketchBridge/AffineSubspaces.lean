import Arithmetic.AffineSubspacesGenerated
import BulksketchBridge.AffineLinearEval
import BulksketchBridge.BmEntry
import BulksketchBridge.AffineSubspaceStart
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.AffineSubspaces

open Aeneas Aeneas.Std ControlFlow
open bulksketch.decode.affine bulksketch.backend.contract
open AffineLinearEval Algebra.Gf64 DenseCoefficient RebuiltLfsr

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

abbrev Iterator := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U64)

def iteratorAt (words : Slice U64) (index : Usize) : Iterator :=
  ⟨⟨words, index.val⟩, index⟩

def productWord (left right : U64) : U64 := ⟨multiplyWord left.bv right.bv⟩

/-- The two writes in the original inner loop, including their order. -/
def innerStep (output : Slice U64) (atDirection coefficient : U64) (index : Nat) : Slice U64 :=
  let next := output.setAtNat index (output[index]! ^^^ productWord atDirection coefficient)
  next.setAtNat (index + 1) (next[index + 1]! ^^^ Square.expectedWord coefficient)

def innerFold (previous : Slice U64) (atDirection : U64)
    (output : Slice U64) (index : Nat) : Nat → Slice U64
  | 0 => output
  | count + 1 => innerFold previous atDirection
      (innerStep output atDirection previous[index]! index) (index + 1) count

@[simp] theorem innerStep_length (output : Slice U64) (atDirection coefficient : U64) (index : Nat) :
    (innerStep output atDirection coefficient index).length = output.length := by
  simp [innerStep, Slice.setAtNat_length]

private theorem read_normal (words : Slice U64) (index : Usize)
    (bounded : index.val < words.length) : Slice.index_usize words index = .ok words[index.val]! := by
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bounded)
  rw [normal, value, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! words.val index.val bounded)

private theorem innerStep_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (previous output : Slice U64)
    (atDirection : U64) (index next : Usize) (active : index.val < previous.length)
    (advanced : next.val = index.val + 1) (room : previous.length < output.length)
    (read : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter U64) (iteratorAt previous index) =
        .ok (some (index, previous[index.val]!), iteratorAt previous next)) :
    subspaces_loop0_loop0.body fieldDictionary kernels atDirection (iteratorAt previous index) output =
      .ok (.cont (iteratorAt previous next, innerStep output atDirection previous[index.val]! index.val)) := by
  have plus : index + 1#usize = Result.ok next := by
    obtain ⟨added, normal, value⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := index) (y := 1#usize)
        (by have bound : previous.length ≤ Usize.max := Slice.length_ineq previous; change index.val + 1 ≤ Usize.max; omega))
    change added.val = index.val + 1 at value
    rwa [show added = next from UScalar.eq_of_val_eq (value.trans advanced.symm)] at normal
  let coefficient := previous[index.val]!
  let product := productWord atDirection coefficient
  let updated := output.setAtNat index.val (output[index.val]! ^^^ product)
  have mul : kernels.ArithmeticInst.mul atDirection coefficient = .ok product :=
    (arithmetic.1 _ _).trans (native_mul_word _ _)
  have sq : kernels.ArithmeticInst.square coefficient = .ok (Square.expectedWord coefficient) :=
    (arithmetic.2 _).trans (Square.square_refines _)
  have read0 := read_normal output index (by omega)
  have write0 := Reconstruction.update_normal output index (output[index.val]! ^^^ product) (by omega)
  have length : updated.length = output.length := Slice.setAtNat_length _ _ _
  have read1 := read_normal updated next (by omega)
  have write1 := Reconstruction.update_normal updated next
    (updated[next.val]! ^^^ Square.expectedWord coefficient) (by omega)
  simp only [subspaces_loop0_loop0.body, read, bind_ok]
  change (do
    let scaled ← kernels.ArithmeticInst.mul atDirection coefficient
    let before ← Slice.index_usize output index
    let xor ← lift (before ^^^ scaled)
    let updated ← Slice.update output index xor
    let sq ← kernels.ArithmeticInst.square coefficient
    let after ← index + 1#usize
    let before ← Slice.index_usize updated after
    let xor ← lift (before ^^^ sq)
    let final ← Slice.update updated after xor
    Result.ok (ControlFlow.cont (iteratorAt previous next, final))) = _
  simp only [Bind.bind, mul, read0, bind_ok, lift, write0, sq, plus]
  simp only [show output.setAtNat index.val (output[index.val]! ^^^ product) = updated by rfl,
    read1, bind_ok, write1]
  rw [advanced]
  rfl

theorem inner_loop_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (previous output : Slice U64)
    (atDirection : U64) (index : Usize) (count : Nat) (remaining : index.val + count = previous.length)
    (room : previous.length < output.length) :
    subspaces_loop0_loop0 fieldDictionary kernels (iteratorAt previous index) output atDirection =
      .ok (innerFold previous atDirection output index.val count) := by
  induction count generalizing index output with
  | zero =>
    obtain ⟨terminal, stop⟩ := root_done previous index (by omega)
    unfold subspaces_loop0_loop0 loop
    dsimp only
    simp only [subspaces_loop0_loop0.body, iteratorAt, stop, bind_ok, innerFold]
    dsimp! only
    simp only [bind_ok]
  | succ count ih =>
    have active : index.val < previous.length := by omega
    obtain ⟨next, read, advanced⟩ := root_next previous index active
    have body := innerStep_normal kernels arithmetic previous output atDirection index next active advanced room read
    have loopNormal := ih (innerStep output atDirection previous[index.val]! index.val)
      next (by omega) (by simpa using room)
    unfold subspaces_loop0_loop0 loop
    dsimp only
    rw [body]
    simpa only [subspaces_loop0_loop0, bind_ok, innerFold, advanced] using loopNormal

/-- Starting index of the row of the prefix-annihilator table for a rank. -/
def offset (rank : Nat) : Nat := rank * (rank + 1) / 2

theorem offset_succ (rank : Nat) : offset (rank + 1) = offset rank + rank + 1 := by
  unfold offset
  rw [show (rank + 1) * (rank + 1 + 1) = rank * (rank + 1) + 2 * (rank + 1) by ring]
  omega

theorem offset_mono : Monotone offset := by
  apply monotone_nat_of_le_succ
  intro rank
  rw [offset_succ]
  omega

def row (table : Slice U64) (rank : Nat) : Slice U64 :=
  ClosedLeaf.region table (offset rank) (offset (rank + 1))

def nextRow (previous shape : Slice U64) (atDirection : U64) : Slice U64 :=
  innerFold previous atDirection (zeroWords shape) 0 previous.length

@[simp] theorem innerFold_length (previous : Slice U64) (atDirection : U64)
    (output : Slice U64) (index count : Nat) :
    (innerFold previous atDirection output index count).length = output.length := by
  induction count generalizing output index with
  | zero => rfl
  | succ count ih => simp only [innerFold, ih, innerStep_length]

@[simp] theorem nextRow_length (previous shape : Slice U64) (atDirection : U64) :
    (nextRow previous shape atDirection).length = shape.length := by
  simp only [nextRow, innerFold_length, zero_length]

def tableStep {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (table : Slice U64) (rank : Nat) (direction : U64) : Result (Slice U64) := do
  let previous := row table rank
  let atDirection ← linear_eval fieldDictionary kernels previous direction
  let next := nextRow previous (row table (rank + 1)) atDirection
  .ok (table.setSlice! (offset (rank + 1)) next.val)

def tableFold {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (basis table : Slice U64) (rank : Nat) : Nat → Result (Slice U64)
  | 0 => .ok table
  | count + 1 => do
    let next ← tableStep kernels table rank basis[rank]!
    tableFold kernels basis next (rank + 1) count

private theorem tableStep_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (basis table : Slice U64)
    (rank nextRank : Usize) (advanced : nextRank.val = rank.val + 1)
    (read : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter U64) (iteratorAt basis rank) =
        .ok (some (rank, basis[rank.val]!), iteratorAt basis nextRank))
    (rankBound : nextRank.val ≤ 64) (room : offset (rank.val + 2) ≤ table.length) :
    ∃ updated,
      subspaces_loop0.body fieldDictionary kernels (iteratorAt basis rank) table =
        .ok (.cont (iteratorAt basis nextRank, updated)) ∧
      tableStep kernels table rank.val basis[rank.val]! = .ok updated ∧
      updated.length = table.length := by
  obtain ⟨start, startOk, startVal⟩ := RootRun.subspace_start_refines rank (by omega)
  obtain ⟨next, nextOk, nextVal⟩ := RootRun.subspace_start_refines nextRank rankBound
  change start.val = offset rank.val at startVal
  change next.val = offset nextRank.val at nextVal
  rw [advanced] at nextVal
  have nextRoom : next.val ≤ table.length := by
    rw [nextVal]; exact (offset_mono (by omega)).trans room
  have startRoom : start.val ≤ next.val := by
    rw [startVal, nextVal]; exact offset_mono (by omega)
  have platform : 66 ≤ Usize.max := by
    simp only [Usize.max, Usize.numBits, UScalarTy.numBits]
    rcases System.Platform.numBits_eq with width | width <;> rw [width] <;> decide
  obtain ⟨oneMore, oneOk, oneVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := rank) (y := 1#usize)
      (by change rank.val + 1 ≤ Usize.max; omega))
  have plusOne : rank + 1#usize = Result.ok nextRank := by
    have exactRank : oneMore = nextRank := UScalar.eq_of_val_eq (oneVal.trans advanced.symm)
    simpa only [exactRank] using oneOk
  obtain ⟨width, widthOk, widthVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := rank) (y := 2#usize)
      (by change rank.val + 2 ≤ Usize.max; omega))
  change width.val = rank.val + 2 at widthVal
  obtain ⟨rest, back, split, restWords, restLen, restore⟩ := ClosedLeaf.split_normal table next nextRoom
  have prefixLen : (prefixSlice table next.val).length = next.val := by
    rw [prefix_length, Nat.min_eq_left nextRoom]
  have roomForRow : width.val ≤ rest.length := by
    have step : offset (rank.val + 2) = offset (rank.val + 1) + rank.val + 2 := by
      simpa only [Nat.add_assoc] using offset_succ (rank.val + 1)
    rw [widthVal, restLen, nextVal]
    omega
  have previousNormal := ClosedLeaf.shared_region_normal (prefixSlice table next.val) start next
    startRoom (by rw [prefixLen])
  have exactPrevious : ClosedLeaf.region (prefixSlice table next.val) start.val next.val = row table rank.val := by
    rw [ClosedLeaf.region_prefix _ _ _ _ (by rfl), startVal, nextVal]
    rfl
  rw [exactPrevious] at previousNormal
  have outputNormal := prefix_normal rest width roomForRow
  let shape := prefixSlice rest width.val
  have shapeSize : shape.length = rank.val + 2 := by
    change (prefixSlice rest width.val).length = _
    rw [prefix_length, Nat.min_eq_left roomForRow, widthVal]
  have previousSize : (row table rank.val).length = rank.val + 1 := by
    unfold row
    rw [ClosedLeaf.region_length _ _ _ (nextVal ▸ nextRoom), offset_succ]
    omega
  have exactShape : shape = row table (rank.val + 1) := by
    apply Slice.ext
    simp only [shape, prefixSlice, row, ClosedLeaf.region, Slice.from_val, restWords, nextVal, List.slice]
    have size : width.val = offset (rank.val + 1 + 1) - offset (rank.val + 1) := by
      rw [widthVal, offset_succ]
      omega
    rw [size]
  obtain ⟨directionValue, evaluated, _⟩ := linear_eval_refines kernels (row table rank.val) basis[rank.val]! arithmetic
  have inner := inner_loop_refines kernels arithmetic (row table rank.val) (zeroWords shape)
    directionValue 0#usize (row table rank.val).length (by simp) (by rw [zero_length, shapeSize, previousSize]; omega)
  let output := nextRow (row table rank.val) shape directionValue
  have outputFits : output.length ≤ rest.length := by
    change (nextRow _ _ _).length ≤ _
    rw [nextRow_length]
    exact prefix_length rest width.val ▸ Nat.min_le_right _ _
  have restored := restore output outputFits
  let updated := table.setSlice! (offset (rank.val + 1)) output.val
  refine ⟨updated, ?_, ?_, Slice.setSlice!_length ..⟩
  · simp only [subspaces_loop0.body, read, bind_ok]
    dsimp! only
    simp only [startOk, plusOne, nextOk, split, bind_ok]
    dsimp! only
    simp only [Slice.index_SliceIndexRangeUsizeSliceInst, previousNormal, widthOk,
      Slice.index_mut_SliceIndexRangeToUsizeSliceInst, outputNormal, bind_ok]
    dsimp! only
    simp only [evaluated, bind_ok, fill_zero, core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default]
    have atZero : (0#usize).val = 0 := by simp
    have innerNormal : subspaces_loop0_loop0 fieldDictionary kernels
        (iteratorAt (row table rank.val) 0#usize) (zeroWords shape) directionValue = .ok output := by
      simpa only [output, nextRow, atZero] using inner
    have zeroIterator : (⟨⟨row table rank.val, 0⟩, 0#usize⟩ : Iterator) =
        iteratorAt (row table rank.val) 0#usize := by rfl
    simp only [zeroIterator, show prefixSlice rest width.val = shape by rfl, innerNormal, bind_ok, restored]
    rw [nextVal]
  · simp only [tableStep, evaluated, bind_ok, updated, output, exactShape]

theorem outer_loop_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (basis table : Slice U64) (index : Usize) (count : Nat)
    (remaining : index.val + count = basis.length) (rankBound : basis.length ≤ 64)
    (room : offset (basis.length + 1) ≤ table.length) :
    ∃ updated,
      subspaces_loop0 fieldDictionary kernels (iteratorAt basis index) table = .ok updated ∧
      tableFold kernels basis table index.val count = .ok updated ∧ updated.length = table.length := by
  induction count generalizing index table with
  | zero =>
    obtain ⟨terminal, stop⟩ := root_done basis index (by omega)
    refine ⟨table, ?_, rfl, rfl⟩
    unfold subspaces_loop0 loop
    dsimp only
    simp only [subspaces_loop0.body, iteratorAt, stop, bind_ok]
    dsimp! only
    simp only [bind_ok]
  | succ count ih =>
    obtain ⟨next, read, advanced⟩ := root_next basis index (by omega)
    have roomForStep : offset (index.val + 2) ≤ table.length :=
      (offset_mono (by omega)).trans room
    obtain ⟨stepped, body, stepModel, sameLength⟩ :=
      tableStep_normal kernels arithmetic basis table index next advanced read (by omega) roomForStep
    obtain ⟨updated, loopNormal, modelNormal, resultLength⟩ :=
      ih stepped next (by omega) (by rwa [sameLength])
    refine ⟨updated, ?_, ?_, resultLength.trans sameLength⟩
    · unfold subspaces_loop0 loop
      dsimp only
      rw [body]
      simpa only [subspaces_loop0, bind_ok] using loopNormal
    · simpa only [tableFold, stepModel, bind_ok, advanced] using modelNormal

def ActualSubspaces : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    CorrectArithmetic kernels → ∀ (basis table : Slice U64),
    basis.length ≤ 64 → offset (basis.length + 1) ≤ table.length →
    ∃ updated,
      subspaces fieldDictionary kernels basis table = .ok updated ∧
      tableFold kernels basis (table.setAtNat 0 1#u64) 0 basis.length = .ok updated ∧
      updated.length = table.length

theorem subspaces_refines : ActualSubspaces := by
  intro K kernels arithmetic basis table rankBound room
  have nonempty : 0 < table.length := by
    have start : offset 1 ≤ offset (basis.length + 1) := offset_mono (by omega)
    change 1 ≤ offset (basis.length + 1) at start
    omega
  have initialized := Reconstruction.update_normal table 0#usize 1#u64 (by exact nonempty)
  have sameLength := Slice.setAtNat_length table 0 1#u64
  obtain ⟨updated, ran, model, length⟩ := outer_loop_refines kernels arithmetic basis
    (table.setAtNat 0 1#u64) 0#usize basis.length (by simp) rankBound (by rwa [sameLength])
  refine ⟨updated, ?_, model, length.trans sameLength⟩
  have atZero : (0#usize).val = 0 := by simp
  simpa only [subspaces, initialized, bind_ok, core.slice.Slice.iter, atZero,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, iteratorAt] using ran

end BulksketchBridge.AffineSubspaces
