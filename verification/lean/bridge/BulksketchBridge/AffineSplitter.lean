import Arithmetic.AffineSplitterGenerated
import BulksketchBridge.AffineLinearEval
import BulksketchBridge.BmEntry
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.ReconstructionLoop
import BulksketchBridge.DenseNormalization
import BulksketchBridge.NativeRootTrace
import BulksketchBridge.TimesXModSpec

namespace BulksketchBridge.AffineSplitter

open Aeneas Aeneas.Std ControlFlow
open bulksketch.decode.affine bulksketch.backend.contract
open DenseCoefficient RebuiltLfsr BmEntry

set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

abbrev State := Slice U64 × Slice bulksketch.types.RawProduct × Slice U64 × Slice U64
abbrev Square := Aeneas.Std.RootTraceRuntime.ModularSquare

def step {F K : Type} (square : Square) (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (modulus table : Slice U64) (degree : Nat)
    (coefficient : U64) (more : Bool) (state : State) : Result State := do
  let (output, raw, residue, squared) := state
  let updated ← kernels.ArithmeticInst.scale_xor (prefixSlice output degree) residue coefficient
  if more then
    let (_, nextSquare, nextRaw) ← square field kernels residue modulus table squared raw
    let nextResidue ← core.slice.Slice.copy_from_slice core.marker.CopyU64 residue nextSquare
    .ok (restorePrefix output updated, nextRaw, nextResidue, nextSquare)
  else
    .ok (restorePrefix output updated, raw, residue, squared)

def fold {F K : Type} (square : Square) (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (modulus table : Slice U64) (degree : Nat) :
    List U64 → State → Result State
  | [], state => .ok state
  | coefficient :: rest, state => do
    let next ← step square field kernels modulus table degree coefficient (!rest.isEmpty) state
    fold square field kernels modulus table degree rest next

private abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U64)

private def iterAt (linear : Slice U64) (count : Usize) : Iter :=
  { iter := ⟨linear, count.val⟩, count := count }

private theorem iter_step (linear : Slice U64) (count : Usize)
    (active : count.val < linear.length) :
    ∃ advanced : Usize,
      count + 1#usize = Result.ok advanced ∧ advanced.val = count.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter U64) (iterAt linear count) =
        Result.ok (some (count, linear[count.val]!), iterAt linear advanced) := by
  have one : (1#usize).val = 1 := by simp
  have safe : count.val + (1#usize).val ≤ Usize.max := by
    have bound := Slice.length_ineq linear
    rw [one]
    exact (Nat.succ_le_of_lt active).trans bound
  obtain ⟨advanced, addNormal, addPost⟩ := RawMulTable.normal_of_spec _ _ (Usize.add_spec (x := count) (y := 1#usize) safe)
  have advancedValue : advanced.val = count.val + 1 := by simpa only [one] using addPost
  refine ⟨advanced, addNormal, advancedValue, ?_⟩
  have inner : core.slice.iter.IteratorSliceIter.next ⟨linear, count.val⟩ =
      Result.ok (some linear[count.val]!, ⟨linear, count.val + 1⟩) := by
    have step : count.val < (Slice.len linear).val := by rwa [Slice.len_val]
    simp only [core.slice.iter.IteratorSliceIter.next, step, _root_.dite_true]
    exact congrArg (fun item => Result.ok (some item, (⟨linear, count.val + 1⟩ : core.slice.iter.Iter U64)))
      (Slice.Inhabited_getElem_eq_getElem! linear count.val active)
  have post := core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
    (core.iter.traits.iterator.IteratorSliceIter U64) (iterAt linear count)
    linear[count.val]! ⟨linear, count.val + 1⟩ (by
      change Aeneas.Std.WP.spec (core.slice.iter.IteratorSliceIter.next _) _
      simp only [iterAt, inner, Aeneas.Std.WP.spec_ok, and_self]) (by simpa only [iterAt, one] using safe)
  obtain ⟨⟨opt, state⟩, normal, rfl, stateIter, stateVal⟩ := RawMulTable.normal_of_spec _ _ post
  have countEq : state.count = advanced := UScalar.eq_of_val_eq (stateVal.trans advancedValue.symm)
  have stateEq : state = iterAt linear advanced := by
    cases state
    simp_all [iterAt]
  rw [normal, stateEq]
  rfl

private theorem iter_done (linear : Slice U64) (count : Usize)
    (stopped : linear.length ≤ count.val) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter U64) (iterAt linear count) =
      Result.ok (none, iterAt linear count) := by
  have inactive : ¬ count.val < (Slice.len linear).val := by rw [Slice.len_val]; omega
  have inner : core.slice.iter.IteratorSliceIter.next (⟨linear, count.val⟩ : core.slice.iter.Iter U64) =
      Result.ok (none, ⟨linear, count.val⟩) := by
    simp only [core.slice.iter.IteratorSliceIter.next, inactive, _root_.dite_false]
  have post := core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
    (core.iter.traits.iterator.IteratorSliceIter U64) (iterAt linear count)
    ⟨linear, count.val⟩ (by
      change Aeneas.Std.WP.spec (core.slice.iter.IteratorSliceIter.next _) _
      simp only [iterAt, inner, Aeneas.Std.WP.spec_ok, and_self])
  obtain ⟨⟨opt, state⟩, normal, rfl, stateIter, stateCount⟩ := RawMulTable.normal_of_spec _ _ post
  have stateEq : state = iterAt linear count := by
    cases state
    simp_all [iterAt]
  rw [normal, stateEq]

def Admitted (degree rawLength : Nat) (state : State) : Prop :=
  degree ≤ state.1.length ∧ state.2.1.length = rawLength ∧
    state.2.2.1.length = degree ∧ state.2.2.2.length = degree

def ScaleLaw {F K : Type} (kernels : BulkKernels K F) : Prop :=
  ∀ destination source : Slice U64, ∀ coefficient : U64, destination.length = source.length →
    ∃ updated, kernels.ArithmeticInst.scale_xor destination source coefficient = .ok updated

def SquareLaw {F K : Type} (square : Square) (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (modulus table : Slice U64) (degree rawLength : Nat) : Prop :=
  ∀ (residue squared : Slice U64) (raw : Slice bulksketch.types.RawProduct),
    residue.length = degree → squared.length = degree → raw.length = rawLength →
    ∃ size nextSquare nextRaw,
      square field kernels residue modulus table squared raw = .ok (size, nextSquare, nextRaw) ∧
      nextSquare.length = degree ∧ nextRaw.length = rawLength

private theorem step_normal {F K : Type} (square : Square) (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (modulus table linear : Slice U64) (degree count advanced : Usize)
    (rawLength : Nat) (state : State)
    (added : (count + 1#usize : Result Usize) = Result.ok advanced)
    (nextNormal : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter U64) (iterAt linear count) =
        .ok (some (count, linear[count.val]!), iterAt linear advanced))
    (more : (advanced != Slice.len linear) = !(linear.val.drop advanced.val).isEmpty)
    (admitted : Admitted degree.val rawLength state)
    (scaleLaw : ScaleLaw kernels) (squareLaw : SquareLaw square field kernels modulus table degree.val rawLength) :
    ∃ next,
      step square field kernels modulus table degree.val linear[count.val]!
        (!(linear.val.drop advanced.val).isEmpty) state = .ok next ∧
      splitter_loop.body square field kernels modulus table linear degree (iterAt linear count)
        state.1 state.2.1 state.2.2.1 state.2.2.2 = .ok (.cont (iterAt linear advanced, next)) ∧
      Admitted degree.val rawLength next := by
  rcases state with ⟨output, raw, residue, squared⟩
  rcases admitted with ⟨room, rawSize, residueSize, squaredSize⟩
  change degree.val ≤ output.length at room
  have same : (prefixSlice output degree.val).length = residue.length := by
    rw [prefix_length, Nat.min_eq_left room, residueSize]
  obtain ⟨updated, scaled⟩ := scaleLaw _ _ linear[count.val]! same
  have outputSize : degree.val ≤ (restorePrefix output updated).length := by simpa using room
  by_cases last : advanced = Slice.len linear
  · have stopped : Bool.not (linear.val.drop advanced.val).isEmpty = false := by
      rw [← more, last]
      simp
    refine ⟨(restorePrefix output updated, raw, residue, squared), ?_, ?_,
      outputSize, rawSize, residueSize, squaredSize⟩
    · unfold step
      dsimp! only
      simp only [stopped, scaled, bind_ok, Bool.false_eq_true, ite_false]
    · simp only [splitter_loop.body, nextNormal, bind_ok, Slice.index_mut_SliceIndexRangeToUsizeSliceInst,
        prefix_normal _ _ room]
      dsimp! only
      simp only [scaled, bind_ok, added, more, stopped, Bool.false_eq_true, ite_false]
  · have moreWork : Bool.not (linear.val.drop advanced.val).isEmpty = true := by rw [← more]; simp [last]
    obtain ⟨size, nextSquare, nextRaw, squaredNormal, nextSize, nextRawSize⟩ :=
      squareLaw residue squared raw residueSize squaredSize rawSize
    have copied := ClosedLeaf.copy_normal residue nextSquare (residueSize.trans nextSize.symm)
    refine ⟨(restorePrefix output updated, nextRaw, nextSquare, nextSquare), ?_, ?_,
      outputSize, nextRawSize, nextSize, nextSize⟩
    · unfold step
      dsimp! only
      simp only [moreWork, scaled, bind_ok, ite_true, squaredNormal]
      dsimp! only
      rw [copied, bind_ok]
    · simp only [splitter_loop.body, nextNormal, bind_ok, Slice.index_mut_SliceIndexRangeToUsizeSliceInst,
        prefix_normal _ _ room]
      dsimp! only
      simp only [scaled, bind_ok, added, more, moreWork, ite_true, squaredNormal]
      dsimp! only
      rw [copied, bind_ok]

def ActualSplitterLoop : Prop :=
  ∀ {F K : Type} (square : Square) (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (modulus table linear : Slice U64) (degree count : Usize)
    (rawLength : Nat) (state : State),
    Admitted degree.val rawLength state → ScaleLaw kernels →
    SquareLaw square field kernels modulus table degree.val rawLength →
    ∃ final, splitter_loop square field kernels (iterAt linear count) modulus table linear state.1
      state.2.1 degree state.2.2.1 state.2.2.2 = .ok final ∧
      fold square field kernels modulus table degree.val (linear.val.drop count.val) state = .ok final ∧
      Admitted degree.val rawLength final

theorem loop_refines : ActualSplitterLoop := by
  intro F K square field kernels modulus table linear degree count rawLength state admitted scaleLaw squareLaw
  suffices ∀ n (count : Usize) (state : State), linear.length - count.val = n →
      Admitted degree.val rawLength state →
      ∃ final, splitter_loop square field kernels (iterAt linear count) modulus table linear state.1
        state.2.1 degree state.2.2.1 state.2.2.2 = .ok final ∧
        fold square field kernels modulus table degree.val (linear.val.drop count.val) state = .ok final ∧
        Admitted degree.val rawLength final from this _ _ _ rfl admitted
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro count state rem bounds
    by_cases active : count.val < linear.length
    · obtain ⟨advanced, added, advancedValue, nextNormal⟩ := iter_step linear count active
      have dropped : linear.val.drop count.val = linear[count.val]! :: linear.val.drop advanced.val := by
        rw [advancedValue, List.drop_eq_getElem_cons (show count.val < linear.val.length from active)]
        exact congrArg (fun word => word :: linear.val.drop (count.val + 1))
          (Slice.Inhabited_getElem_eq_getElem! linear count.val active)
      have more : (advanced != Slice.len linear) = !(linear.val.drop advanced.val).isEmpty := by
        have len : (Slice.len linear).val = linear.length := Slice.len_val _
        have le : advanced.val ≤ linear.length := by omega
        by_cases eq : advanced = Slice.len linear
        · simp [eq]
        · have lt : advanced.val < linear.length := by
            by_contra h
            exact eq (UScalar.eq_of_val_eq (by omega))
          have nonempty : linear.val.drop advanced.val ≠ [] := by
            intro h
            have length := congrArg List.length h
            rw [List.length_drop] at length
            change advanced.val < linear.val.length at lt
            simp only [List.length_nil] at length
            omega
          have inhabited : (linear.val.drop advanced.val).isEmpty = false := by
            cases h : linear.val.drop advanced.val with
            | nil => exact False.elim (nonempty h)
            | cons => rfl
          simp [eq, inhabited]
      obtain ⟨next, stepped, body, nextBounds⟩ :=
        step_normal square field kernels modulus table linear degree count advanced rawLength state
          added nextNormal more bounds scaleLaw squareLaw
      obtain ⟨final, run, folded, finalBounds⟩ := ih (linear.length - advanced.val)
        (by omega) advanced next rfl nextBounds
      refine ⟨final, ?_, ?_, finalBounds⟩
      · unfold splitter_loop loop
        dsimp only
        rw [body]
        simpa only [bind_ok, splitter_loop] using run
      · rw [dropped, fold, stepped, bind_ok, folded]
    · have dropped : linear.val.drop count.val = [] := by
        apply List.drop_eq_nil_of_le
        change linear.length ≤ count.val
        omega
      refine ⟨state, ?_, by rw [dropped, fold], bounds⟩
      unfold splitter_loop loop
      dsimp only
      simp only [splitter_loop.body, iter_done linear count (by omega), bind_ok]
      dsimp! only
      simp only [bind_ok]

def initialState (degree : Nat) (base : U64) (output work : Slice U64)
    (raw : Slice bulksketch.types.RawProduct) : State :=
  ((restorePrefix output (zeroWords (prefixSlice output degree))).setAtNat 0 base, raw,
    (zeroWords (prefixSlice work degree)).setAtNat 1 1#u64, prefixSlice (tail work degree) degree)

def SplitterResult {K : Type} (square : Square)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (modulus table linear : Slice U64) (base : U64) (output work : Slice U64)
    (raw : Slice bulksketch.types.RawProduct) (degree : Nat) : Prop :=
    ∃ evaluated final normalized,
      Algebra.Gf64.toField evaluated.bv = AffineLinearEval.linearValueFrom linear base 0 ∧
      fold square fieldDictionary kernels modulus table degree linear.val
        (initialState degree evaluated output work raw) = .ok final ∧
      Admitted degree raw.length final ∧
      normalized.val = DenseNormalization.normalizedLength (prefixSlice final.1 degree).val ∧
      splitter square fieldDictionary kernels modulus table linear base output work raw =
        .ok (normalized, final.1,
          splitBack work degree (final.2.2.1, restorePrefix (tail work degree) final.2.2.2), final.2.1)

/-- The original splitter performs the affine coefficient fold and exact
backward writes to the output, both work windows, and raw scratch. The original
linear evaluator and inline trailing-zero scan return the specified values. -/
def ActualSplitter : Prop :=
  ∀ {K : Type} (square : Square) (kernels : BulkKernels K bulksketch.field.Gf64)
    (modulus table linear : Slice U64) (base : U64) (output work : Slice U64)
    (raw : Slice bulksketch.types.RawProduct) (degree : Nat),
    modulus.length = degree + 1 → 2 ≤ degree → degree ≤ output.length → 2 * degree ≤ work.length →
    AffineLinearEval.CorrectArithmetic kernels → ScaleLaw kernels →
    SquareLaw square fieldDictionary kernels modulus table degree raw.length →
    SplitterResult square kernels modulus table linear base output work raw degree

theorem splitter_refines : ActualSplitter := by
  intro K square kernels modulus table linear base output work raw degree modulusSize positive outputRoom
    workRoom arithmetic scaleLaw squareLaw
  obtain ⟨d, subtracted, dValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := Slice.len modulus) (y := 1#usize) (by
      rw [Slice.len_val, modulusSize]
      change 1 ≤ degree + 1
      omega))
  have dEq : d.val = degree := by
    simpa only [Slice.len_val, modulusSize, show (1#usize).val = 1 by decide, Nat.add_sub_cancel] using dValue.1
  obtain ⟨evaluated, evaluatedNormal, evaluatedValue⟩ :=
    AffineLinearEval.linear_eval_refines kernels linear base arithmetic
  have outputCut := prefix_normal output d (by rwa [dEq])
  have split := split_refines work d (by rw [dEq]; omega)
  have squaredRoom : degree ≤ (tail work degree).length := by rw [tail_length]; omega
  have squaredCut := prefix_normal (tail work d.val) d (by simpa only [dEq] using squaredRoom)
  have outputUpdate := Reconstruction.update_normal (restorePrefix output (zeroWords (prefixSlice output d.val)))
    0#usize evaluated (by rw [restore_length]; change 0 < output.length; omega)
  have residueUpdate := Reconstruction.update_normal (zeroWords (prefixSlice work d.val)) 1#usize 1#u64 (by
    rw [zero_length, prefix_length, dEq, Nat.min_eq_left (by omega)]
    change 1 < degree
    omega)
  have initialBounds : Admitted degree raw.length (initialState degree evaluated output work raw) := by
    unfold Admitted initialState
    dsimp only
    simp only [Slice.setAtNat_length, restore_length, zero_length, prefix_length, outputRoom,
      Nat.min_eq_left (show degree ≤ work.length by omega), Nat.min_eq_left squaredRoom, and_self]
  obtain ⟨final, ran, folded, bounds⟩ :=
    loop_refines square fieldDictionary kernels modulus table linear d 0#usize raw.length
      (initialState degree evaluated output work raw) (by rwa [dEq]) scaleLaw (by rwa [dEq])
  have finalRoom : d.val ≤ final.1.length := bounds.1
  have finalCut := shared_prefix_normal final.1 d finalRoom
  obtain ⟨normalized, normalizedNormal, normalizedValue⟩ :=
    DenseNormalization.normalized_len_refines (prefixSlice final.1 degree)
  refine ⟨evaluated, final, normalized, evaluatedValue, ?_, by simpa only [dEq] using bounds, normalizedValue, ?_⟩
  · simpa only [dEq, show (0#usize).val = 0 by decide, List.drop_zero] using folded
  · have initEq : iterAt linear 0#usize = { iter := ⟨linear, 0⟩, count := 0#usize } := rfl
    unfold splitter
    simp only [subtracted, bind_ok, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, outputCut]
    dsimp! only
    simp only [fill_zero, bind_ok, evaluatedNormal, outputUpdate, split]
    dsimp! only
    simp only [squaredCut, bind_ok, residueUpdate]
    dsimp! only
    simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
    rw [← initEq]
    simp only [initialState] at ran
    simp only [dEq, show (0#usize).val = 0 by decide, show (1#usize).val = 1 by decide]
    rw [ran, bind_ok]
    dsimp! only
    simp only [Slice.index_SliceIndexRangeToUsizeSliceInst]
    simp only [dEq] at finalCut
    simp only [finalCut, bind_ok]
    let predicate :=
      splitter.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool fieldDictionary kernels
    let mapper := splitter.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize fieldDictionary kernels
    obtain ⟨position, found, _⟩ := ReversePosition.shared_rposition_refines predicate
      (bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT U64)
      (bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT U64)
      ⟨prefixSlice final.1 degree, 0⟩ () (fun word => word != 0#u64) (by intros; exact ⟨(), rfl⟩)
    have scan : bulksketch.poly.dense.normalized_len (prefixSlice final.1 degree) =
        core.option.Option.map_or mapper position 0#usize () := by
      have equivalent : (do
          let (index, _) ←
            core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rposition predicate
              (bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT U64)
              (bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT U64)
              ⟨prefixSlice final.1 degree, 0⟩ ()
          core.option.Option.map_or mapper index 0#usize ()) =
          bulksketch.poly.dense.normalized_len (prefixSlice final.1 degree) := by
        simp only [bulksketch.poly.dense.normalized_len, core.slice.Slice.iter, bind_ok]
        rfl
      rw [← equivalent, found]
      simp only [bind_ok]
      rfl
    rw [scan] at normalizedNormal
    change (do
      let (index, _) ←
        core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rposition predicate
          (bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT U64)
          (bulksketch.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT U64)
          ⟨prefixSlice final.1 degree, 0⟩ ()
      let size ← core.option.Option.map_or mapper index 0#usize ()
      Result.ok (size, final.1,
        splitBack work degree (final.2.2.1, restorePrefix (tail work degree) final.2.2.2), final.2.1)) = _
    rw [found]
    simp only [Bind.bind, bind_ok, normalizedNormal]


open DenseMulConvolutionSpec DenseReducerSquare DenseReducerAlgebra

/-- The original Dense reducer implements the square callback at every
iteration with the fixed modulus table and the admitted scratch widths. -/
def ActualNativeSplitter : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (modulus table linear : Slice U64) (base : U64) (output work : Slice U64)
    (raw : Slice bulksketch.types.RawProduct) (degree : Nat),
    modulus.length = degree + 1 → 4 ≤ modulus.length → degree ≤ output.length →
    2 * degree ≤ work.length → 2 * degree < raw.length →
    modulus[degree]! = 1#u64 → table.length = degree * (degree / 2) →
    CorrectTable modulus table degree → BackendSquareLaw kernels modulus table degree →
    AffineLinearEval.CorrectArithmetic kernels → TimesXMod.ExactScaleXor kernels →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    ∃ evaluated final normalized,
      Algebra.Gf64.toField evaluated.bv = AffineLinearEval.linearValueFrom linear base 0 ∧
      fold RootTrace.nativeSquare fieldDictionary kernels modulus table degree linear.val
        (initialState degree evaluated output work raw) = .ok final ∧
      Admitted degree raw.length final ∧
      normalized.val = DenseNormalization.normalizedLength (prefixSlice final.1 degree).val ∧
      splitter RootTrace.nativeSquare fieldDictionary kernels modulus table linear base output work raw =
        .ok (normalized, final.1,
          splitBack work degree (final.2.2.1, restorePrefix (tail work degree) final.2.2.2), final.2.1)

theorem native_splitter_refines : ActualNativeSplitter := by
  intro K kernels modulus table linear base output work raw degree shape minimum outputRoom workRoom
    rawRoom monic tableLen tableCorrect backend arithmetic scale rawMul square reduce
  apply splitter_refines RootTrace.nativeSquare kernels modulus table linear base output work raw degree
    shape (by omega) outputRoom workRoom arithmetic
  · intro destination source coefficient same
    obtain ⟨updated, normal, _, _⟩ := scale destination source coefficient same
    exact ⟨updated, normal⟩
  · intro residue squared scratch residueWidth squaredWidth scratchWidth
    obtain ⟨length, nextSquare, nextRaw, normal, _, nextSquareWidth, nextRawWidth, _⟩ :=
      native_modular_square kernels rawMul square reduce modulus table degree minimum shape monic
        tableLen tableCorrect backend residue squared scratch (by omega) (by omega) (by omega)
    exact ⟨length, nextSquare, nextRaw, normal, nextSquareWidth.trans squaredWidth, nextRawWidth.trans scratchWidth⟩

end BulksketchBridge.AffineSplitter
