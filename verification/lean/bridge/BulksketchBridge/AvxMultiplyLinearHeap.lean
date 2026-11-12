import BulksketchBridge.AvxMultiplyLinear

namespace BulksketchBridge.AvxMultiplyLinear

open Aeneas.Std Aeneas.Std.AvxSquareRuntime
open AvxSquare X86MaskedMemory X86MaskedMemory.Allocation X86MaskedMemory.Llbc

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- One physical block follows the source instruction order. The two
possibly overlapping reads observe the same heap, before the only store.
The address arithmetic and active lanes come from the exact masked-memory LLBC. -/
structure AllocatedBlock (base : Address) (permit : Address → Bool) (root : U64)
    (words : Slice U64) (stop : Nat) (heap updated : AddressHeap) : Prop where
  currentLoad :
    let start := blockStart stop
    let current := ClosedLeaf.region words start stop
    let chunk := base + BitVec.ofNat 64 (8 * start)
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨chunk.toNat, current.len⟩) =
      some (.register (loadWords current), liftHeap heap)
  predecessorLoad :
    let start := blockStart stop - 1
    let previous := ClosedLeaf.region words start (stop - 1)
    let chunk := base + BitVec.ofNat 64 (8 * start)
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨chunk.toNat, previous.len⟩) =
      some (.register (loadWords previous), liftHeap heap)
  write :
    let start := blockStart stop
    let current := ClosedLeaf.region words start stop
    let chunk := base + BitVec.ofNat 64 (8 * start)
    exec (liftPermission permit) storeProgram
        (storeInput (liftHeap heap) ⟨chunk.toNat, current.len⟩ (blockRegister words root start stop)) =
      some (.unit, liftHeap updated)
  frame :
    ∀ address : Address,
      address.toNat < base.toNat + 8 * blockStart stop ∨ base.toNat + 8 * stop ≤ address.toNat →
      updated address = heap address

theorem allocated_step (live : LiveAllocations) (la57 : Bool) (base : Address) (permit : Address → Bool)
    (root : U64) (words : Slice U64) (stop : Nat) (heap : AddressHeap)
    (active : 1 < stop) (room : stop ≤ words.length)
    (view : WriteView live la57 heap permit base (8 * words.length) 8)
    (bytes : FiniteWordWindow heap base words.length (fun i => words[i]!.bv)) :
    let out := blockWrite words root (blockStart stop) stop
    ∃ updated, AllocatedBlock base permit root words stop heap updated ∧
      FiniteWordWindow updated base out.length (fun i => out[i]!.bv) ∧
      WriteView live la57 updated permit base (8 * out.length) 8 ∧
      FramesOutside heap updated base (8 * words.length) := by
  obtain ⟨positive, order, width⟩ := block_bounds stop active
  let start := blockStart stop
  have current := load_allocated_window live la57 heap base words permit start stop order room width
    view.toReadView bytes
  have previous := load_allocated_window live la57 heap base words permit (start - 1) (stop - 1)
    (by change 1 ≤ start at positive; change start < stop at order; omega) (by omega)
    (by change stop - start ≤ 8 at width; omega) view.toReadView bytes
  obtain ⟨updated, normal, updatedBytes, frame⟩ :=
    store_allocated_window live la57 heap base words permit (blockRegister words root start stop) start stop
      order room width view bytes
  let region := ClosedLeaf.region words start stop
  have regionLength : region.length = stop - start := ClosedLeaf.region_length _ _ _ room
  have fits : region.length ≤ 8 := regionLength ▸ width
  have out : blockWrite words root start stop =
      words.setSlice! start (storeWords region (blockRegister words root start stop) fits).val := by
    simp only [blockWrite, show ClosedLeaf.region words start stop = region from rfl, dite_eq_left fits]
  have newBytes : FiniteWordWindow updated base (blockWrite words root start stop).length
      (fun i => (blockWrite words root start stop)[i]!.bv) := by
    rw [block_write_length, out]
    exact updatedBytes
  have stableLength : (blockWrite words root start stop).length = words.length := block_write_length ..
  have newView : WriteView live la57 updated permit base (8 * (blockWrite words root start stop).length) 8 := by
    have shaped : WriteView live la57 heap permit base (8 * (blockWrite words root start stop).length) 8 := by
      rwa [stableLength]
    exact write_view_from_words shaped _ newBytes
  refine ⟨updated, ⟨current, previous, normal, frame⟩, newBytes, newView, ?_⟩
  intro address outside
  apply frame
  change start < stop at order
  omega

inductive AllocatedTrace (base : Address) (permit : Address → Bool) (root : U64) :
    Nat → Slice U64 → AddressHeap → Slice U64 → AddressHeap → Prop
  | done {stop words heap} :
      stop ≤ 1 → AllocatedTrace base permit root stop words heap words heap
  | step {stop words heap next final finalHeap} :
      1 < stop → AllocatedBlock base permit root words stop heap next →
      AllocatedTrace base permit root (blockStart stop) (blockWrite words root (blockStart stop) stop) next final finalHeap →
      AllocatedTrace base permit root stop words heap final finalHeap

theorem allocated_scan (live : LiveAllocations) (la57 : Bool) (base : Address) (permit : Address → Bool)
    (root : U64) (original words : Slice U64) (stop : Nat) (heap : AddressHeap)
    (room : stop ≤ original.length) (inv : Descending original words root stop)
    (view : WriteView live la57 heap permit base (8 * words.length) 8)
    (bytes : FiniteWordWindow heap base words.length (fun i => words[i]!.bv)) :
    let final := RebuiltLfsr.linearStep original root
    ∃ updated, AllocatedTrace base permit root stop words heap final updated ∧
      FiniteWordWindow updated base final.length (fun i => final[i]!.bv) ∧
      WriteView live la57 updated permit base (8 * final.length) 8 ∧
      FramesOutside heap updated base (8 * original.length) := by
  induction stop using Nat.strong_induction_on generalizing words heap with
  | h stop ih =>
    by_cases active : 1 < stop
    · obtain ⟨next, block, nextBytes, nextView, frame⟩ :=
        allocated_step live la57 base permit root words stop heap active (by rwa [inv.1]) view bytes
      have order := (block_bounds stop active).2.1
      have nextInv := block_progress original words root stop active room inv
      obtain ⟨updated, trace, resultBytes, resultView, resultFrame⟩ :=
        ih (blockStart stop) order (blockWrite words root (blockStart stop) stop) next (by omega)
          nextInv nextView nextBytes
      have first : FramesOutside heap next base (8 * original.length) := by rwa [← inv.1]
      exact ⟨updated, .step active block trace, resultBytes, resultView, first.trans resultFrame⟩
    · have final := finished_descending original words root stop (by omega) inv
      rw [← final]
      exact ⟨heap, .done (by omega), bytes, view, fun _ _ => rfl⟩

/-- Compose the exact generated original wrapper with the allocated source
trace. Allocation/provenance admission and compiler/ISA agreement are
explicitly separate from the Lean model checked here. -/
def ActualAllocatedMultiplyLinear : Prop :=
  ∀ (loadModel : Load) (storeModel : Store), LoadLaw loadModel → StoreLaw storeModel →
    ∀ (live : LiveAllocations) (la57 : Bool) (base : Address) (permit : Address → Bool)
      (root : U64) (words : Slice U64) (heap : AddressHeap),
      WriteView live la57 heap permit base (8 * words.length) 8 →
      FiniteWordWindow heap base words.length (fun i => words[i]!.bv) →
      let final := RebuiltLfsr.linearStep words root
      ∃ updated,
        bulksketch.backend.x86_vpclmul512.multiply_linear loadModel storeModel words root = .ok final ∧
        AllocatedTrace base permit root words.length words heap final updated ∧
        FiniteWordWindow updated base final.length (fun i => final[i]!.bv) ∧
        WriteView live la57 updated permit base (8 * final.length) 8 ∧
        FramesOutside heap updated base (8 * words.length)

theorem allocated_multiply_linear_refines : ActualAllocatedMultiplyLinear := by
  intro loadModel storeModel loadLaw storeLaw live la57 base permit root words heap view bytes
  obtain ⟨updated, trace, result, finalView, frame⟩ :=
    allocated_scan live la57 base permit root words words words.length heap (Nat.le_refl _)
      (initial_descending words root) view bytes
  exact ⟨updated, multiply_linear_refines loadModel storeModel loadLaw storeLaw words root,
    trace, result, finalView, frame⟩

end BulksketchBridge.AvxMultiplyLinear
