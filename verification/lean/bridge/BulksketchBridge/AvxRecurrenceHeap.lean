import BulksketchBridge.AvxSquareWindows

namespace BulksketchBridge.AvxRecurrence

open Aeneas.Std AvxSquare X86MaskedMemory X86MaskedMemory.Allocation X86MaskedMemory.Llbc

/-- The exact masked load at every reachable recurrence lag and comparison
window preserves the heap. Lag zero is the source's current output block. -/
def ActualAllocatedRecurrenceReads : Prop :=
  ∀ (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (base : Address) (odd : Slice U64) (permit : Address → Bool),
    ReadView live la57 heap base (8 * odd.length) 8 →
    FiniteWordWindow heap base odd.length (fun i => odd[i]!.bv) →
    ∀ (index length lag : Nat), lag ≤ index → 0 < length → length ≤ 8 → index + length ≤ odd.length →
    let start := index - lag
    let window := ClosedLeaf.region odd start (start + length)
    let address := base + BitVec.ofNat 64 (8 * start)
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨address.toNat, window.len⟩) =
      some (.register (loadWords window), liftHeap heap)

theorem allocated_recurrence_reads : ActualAllocatedRecurrenceReads := by
  intro live la57 heap base odd permit view bytes index length lag lagBound positive short room
  exact load_allocated_window live la57 heap base odd permit (index - lag) (index - lag + length)
    (by omega) (by omega) (by omega) view bytes

#print axioms allocated_recurrence_reads

end BulksketchBridge.AvxRecurrence
