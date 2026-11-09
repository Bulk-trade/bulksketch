import Arithmetic.CanonicalizeGenerated
import BulksketchBridge.CanonicalizePrice

namespace BulksketchBridge.CanonicalizeWrapper

open Aeneas Aeneas.Std CanonicalizeRuntime CanonicalizeOrdering
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.scratch bulksketch.types
open BulksketchBridge.DenseCoefficient RebuiltLfsr
open core.result.Result.Insts

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

def SortLaw (sort : SortWords) : Prop :=
  ∀ words : Slice U64, ∃ ordered : Slice U64,
    sort core.cmp.OrdU64 words = .ok ordered ∧
      ordered.val.Perm words.val ∧ ordered.val.Pairwise DegreeProbeRuntime.ordered

def orderBranch (sort : SortWords) (roots : Slice U64) (meter : WorkMeter) :
    Result (WorkMeter × Slice U64) :=
  if Slice.len roots = 2#usize then do
    let ((left, right), restore) ← core.slice.Slice.split_at_mut roots 1#usize
    let (a, backLeft) ← Slice.index_mut_usize left 0#usize
    let (b, backRight) ← Slice.index_mut_usize right 0#usize
    let (a', b') ← if a > b then .ok (core.mem.swap a b) else .ok (a, b)
    .ok (meter, restore (backLeft a', backRight b'))
  else if Slice.len roots = 0#usize then .ok (meter, roots)
  else do
    let sorted ← if Slice.len roots = 1#usize then .ok roots else sort core.cmp.OrdU64 roots
    .ok (meter, sorted)

private theorem scalarLen (roots : Slice U64) (size : Usize) :
    (Slice.len roots = size) = (roots.length = size.val) := by
  apply propext
  constructor
  · intro equal
    rw [← Slice.len_val, equal]
  · intro equal
    apply UScalar.eq_of_val_eq
    rwa [Slice.len_val]

theorem two_cell_lowering_refines (sort : SortWords) (left right : U64) (meter : WorkMeter) :
    orderBranch sort (pairSlice left right) meter = .ok (meter, orderWords (pairSlice left right)) := by
  have sorted : orderWords (pairSlice left right) =
      Slice.from (orderedPair left right) (by
        rw [(orderedPair_perm left right).length_eq]
        scalar_tac) := by rfl
  rw [sorted]
  unfold orderBranch
  simp only [scalarLen, pairSlice, Slice.length, Slice.from_val, List.length_cons, List.length_nil]
  by_cases h : right.val < left.val
  · simp [h, orderedPair, core.slice.Slice.split_at_mut, Slice.index_mut_usize, Slice.index_usize,
      Slice.length, Slice.from_val, Slice.set, Slice.setAtNat, core.mem.swap]
  · simp [h, orderedPair, core.slice.Slice.split_at_mut, Slice.index_mut_usize, Slice.index_usize,
      Slice.length, Slice.from_val, Slice.set, Slice.setAtNat, core.mem.swap]

theorem order_refines (sort : SortWords) (law : SortLaw sort) (roots : Slice U64) (meter : WorkMeter) :
    orderBranch sort roots meter = .ok (meter, orderWords roots) := by
  obtain ⟨sorted, normal, perm, asc⟩ := law roots
  have sortExact : sort core.cmp.OrdU64 roots = .ok (Aeneas.Std.DegreeProbeRuntime.sortedWords roots) := by
    rw [normal, DegreeProbeRuntime.canonical_unique roots sorted asc perm]
  cases values : roots.val with
  | nil =>
    simp [orderBranch, values, scalarLen, Slice.length]
    unfold orderWords
    split <;> simp_all
  | cons left tail =>
    cases tail with
    | nil =>
      have one : roots = Slice.from [left] (by scalar_tac) := by
        apply Slice.ext
        rw [values]
        rfl
      simp [orderBranch, values, scalarLen, Slice.length]
      rw [one]
      rfl
    | cons right tail =>
      cases tail with
      | nil =>
        have pair : roots = pairSlice left right := by apply Slice.ext; rw [values]; rfl
        rw [pair, two_cell_lowering_refines]
      | cons next tail =>
        simp [orderBranch, orderWords, values, sortExact]

theorem scan_refines {T C D : Type} (callback : core.ops.function.FnMut C T Bool)
    (image : D → T) (predicate : D → Bool)
    (law : ∀ state item, callback.call_mut state (image item) = .ok (predicate item, state))
    (items : List D) (state : C) :
    ∃ consumed, scan callback (items.map image) state = .ok (items.any predicate, consumed) := by
  induction items generalizing state with
  | nil => exact ⟨0, rfl⟩
  | cons first tail ih =>
    obtain ⟨used, step⟩ := ih state
    by_cases h : predicate first = true
    · refine ⟨1, ?_⟩
      simp [scan, law, h, bind_ok]
    · refine ⟨used + 1, ?_⟩
      simp [scan, law, h, step, bind_ok]

private theorem mask_closure {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (mask word : U64) (masked : field.MASK = .ok mask) (state : Unit) :
    bulksketch.decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
      field kernels state word = .ok (wordInvalid mask word, state) := by
  cases state
  unfold bulksketch.decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
  by_cases zero : word = 0#u64
  · simp [zero, wordInvalid]
  · have nonzero : word.bv ≠ 0 := fun same => zero (by apply U64.bv_eq_imp_eq; exact same)
    simp only [zero, ite_false, masked, bind_ok, lift, wordInvalid, nonzero, false_or]
    congr 1

private theorem equal_closure {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (left right : U64) (state : Unit) :
    bulksketch.decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool.call_mut
      field kernels state (pairSlice left right) = .ok (decide (left = right), state) := by
  cases state
  simp [bulksketch.decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool.call_mut,
    pairSlice, Slice.index_usize, Slice.from_val]


private theorem mask_scan {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (mask : U64) (masked : field.MASK = .ok mask) (words : Slice U64) :
    ∃ endIt, anyShared
      (bulksketch.decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
        field kernels) ⟨words, 0⟩ () = .ok (words.val.any (wordInvalid mask), endIt) := by
  obtain ⟨count, normal⟩ := scan_refines
    (bulksketch.decode.stages.Execution.canonicalize.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool field kernels)
    id (wordInvalid mask) (fun state word => mask_closure field kernels mask word masked state) words.val ()
  simp only [List.map_id] at normal
  exact ⟨⟨words, count⟩, by simp [anyShared, normal, bind_ok]⟩

private theorem duplicate_scan {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (words : Slice U64) :
    ∃ endIt, (do
      let it ← windows words 2#usize
      anyWindows ()
        (bulksketch.decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool
          field kernels) it ()) = .ok (adjacentDuplicate words.val, endIt) := by
  obtain ⟨count, normal⟩ := scan_refines
    (bulksketch.decode.stages.Execution.canonicalize.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool
      field kernels) (fun pair : U64 × U64 => pairSlice pair.1 pair.2)
    (fun pair => decide (pair.1 = pair.2))
    (fun state pair => equal_closure field kernels pair.1 pair.2 state) (pairWindows words.val) ()
  rw [windows_any_duplicate] at normal
  exact ⟨((pairWindows words.val).map (fun pair => pairSlice pair.1 pair.2)).drop count, by
    simp [windows, anyWindows, normal, bind_ok]⟩

abbrev Frame (F K : Type) := ExecutionDriverRuntime.Frame F K

def expected {F K : Type} (mask : U64) (self : Execution F K) (workspace : RowWorkspace)
    (meter : WorkMeter) : Result (Frame F K) :=
  match StageCharge.chargeResult meter (WorkSchedule.checkedCost (CanonicalizePrice.units self.budget.total)) with
  | (.Err error, finalMeter) => .ok (.Err error, self, workspace, id, finalMeter)
  | (.Ok (), finalMeter) =>
    if self.roots.count > self.budget.nonzero then
      .ok (.Ok (.Err .DegreeExceedsBudget), self, workspace, id, finalMeter)
    else
      let selected := prefixSlice workspace.roots self.roots.count.val
      let ordered := orderWords selected
      let output := { workspace with roots := restorePrefix workspace.roots ordered }
      .ok (.Ok (if invalid mask ordered.val then .Err .InvalidLocator else .Ok none),
        self, output, id, finalMeter)

def CheckedCanonicalizeWrapper : Prop :=
  ∀ (sort : SortWords), SortLaw sort →
    ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
      (mask : U64) (self : Execution F K) (workspace : RowWorkspace) (meter : WorkMeter),
    field.MASK = .ok mask →
    (self.roots.count ≤ self.budget.nonzero → self.roots.count.val ≤ workspace.roots.length) →
    bulksketch.decode.stages.Execution.canonicalize sort field kernels self workspace meter =
      expected mask self workspace meter

theorem canonicalize_refines : CheckedCanonicalizeWrapper := by
  intro sort law F K field kernels mask self workspace meter maskLaw room
  have charged := CanonicalizePrice.exact_charge field kernels meter self.budget.total
  unfold expected bulksketch.decode.stages.Execution.canonicalize
  rw [charged, bind_ok]
  cases charge : StageCharge.chargeResult meter (WorkSchedule.checkedCost (CanonicalizePrice.units self.budget.total)) with
  | mk outcome finalMeter =>
    cases outcome with
    | Err error =>
      simp [CoreOpsTry.branch, CoreOpsTry_traitFromResidualResult.from_residual]
      rfl
    | Ok success =>
      cases success
      dsimp! only
      rw [bind_ok]
      by_cases excess : self.roots.count > self.budget.nonzero
      · simp only [excess, ite_true]
        rfl
      · have within : self.roots.count ≤ self.budget.nonzero := by
          change ¬ self.budget.nonzero.val < self.roots.count.val at excess
          change self.roots.count.val ≤ self.budget.nonzero.val
          omega
        have read := prefix_normal workspace.roots self.roots.count (room within)
        simp only [excess, ite_false]
        rw [Slice.index_mut_SliceIndexRangeToUsizeSliceInst, read, bind_ok]
        dsimp! only
        let selected := prefixSlice workspace.roots self.roots.count.val
        change Aeneas.Std.bind (orderBranch sort selected finalMeter) _ = _
        rw [order_refines sort law selected finalMeter, bind_ok]
        dsimp! only
        let ordered := orderWords selected
        obtain ⟨maskEnd, masked⟩ := mask_scan field kernels mask maskLaw ordered
        obtain ⟨dupEnd, dup⟩ := duplicate_scan field kernels ordered
        have dupStart : windows ordered 2#usize =
          .ok ((pairWindows ordered.val).map fun pair => pairSlice pair.1 pair.2) := by simp [windows]
        rw [dupStart, bind_tc_ok] at dup
        dsimp only [ordered, selected] at masked dup dupStart
        simp only [core.slice.Slice.iter, bind_ok]
        rw [masked, bind_ok]
        dsimp! only
        by_cases bad : (orderWords selected).val.any (wordInvalid mask) = true
        · simp [bad, invalid, selected]; rfl
        · have good : (orderWords selected).val.any (wordInvalid mask) = false := Bool.eq_false_iff.mpr bad
          simp only [good, Bool.false_eq_true, ite_false, dupStart, bind_ok, dup,
            invalid, Bool.false_or, selected]
          by_cases duplicate : adjacentDuplicate (orderWords selected).val = true
          · simp [duplicate, selected]; rfl
          · have distinct : adjacentDuplicate (orderWords selected).val = false := Bool.eq_false_iff.mpr duplicate
            simp [distinct, selected]; rfl

/-- The scoped unsigned standard-library model meets the wrapper's sort premise. -/
theorem unsigned_sort_law :
    SortLaw (fun (_ : core.cmp.Ord U64) => Aeneas.Std.DegreeProbeRuntime.sortUnsigned) := by
  intro words
  exact ⟨Aeneas.Std.DegreeProbeRuntime.sortedWords words, rfl,
    DegreeProbeRuntime.sortedWords_perm words, DegreeProbeRuntime.sortedWords_ordered words⟩

/-- On an admitted, successfully charged row, canonicalization succeeds
exactly for distinct, in-field nonzero roots. The sorted prefix and the
identity workspace continuation are observable in the returned frame. -/
theorem canonicalize_success {F K : Type} (sort : SortWords) (law : SortLaw sort)
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (mask : U64) (self : Execution F K) (workspace : RowWorkspace) (meter finalMeter : WorkMeter)
    (masked : field.MASK = .ok mask)
    (charged : StageCharge.chargeResult meter (WorkSchedule.checkedCost (CanonicalizePrice.units self.budget.total)) =
      (.Ok (), finalMeter))
    (admitted : self.roots.count ≤ self.budget.nonzero)
    (room : self.roots.count.val ≤ workspace.roots.length) :
    let selected := prefixSlice workspace.roots self.roots.count.val
    let output := { workspace with roots := restorePrefix workspace.roots (orderWords selected) }
    bulksketch.decode.stages.Execution.canonicalize sort field kernels self workspace meter =
      .ok (.Ok (.Ok none), self, output, id, finalMeter) ↔
        (∀ word ∈ selected.val, validWord mask word) ∧ selected.val.Nodup := by
  dsimp only
  rw [canonicalize_refines sort law field kernels mask self workspace meter masked (fun _ => room),
    expected, charged]
  have bound : ¬ self.roots.count > self.budget.nonzero := by
    change ¬ self.budget.nonzero.val < self.roots.count.val
    change self.roots.count.val ≤ self.budget.nonzero.val at admitted
    omega
  dsimp only
  rw [ite_eq_right bound]
  rw [← complete_word_validation]
  cases invalid mask (orderWords (prefixSlice workspace.roots self.roots.count.val)).val <;> simp


end BulksketchBridge.CanonicalizeWrapper
