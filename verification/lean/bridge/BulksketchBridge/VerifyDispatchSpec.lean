import Arithmetic.VerifyDispatchGenerated

namespace BulksketchBridge.VerifyDispatch

open Aeneas Aeneas.Std
open bulksketch.decode.verify

def toWord (value : Nat) : U64 := ⟨BitVec.ofNat 64 value⟩

def tailVectors (tail : Nat) : Nat :=
  if tail = 0 then 0 else if tail ≤ 8 then 1 else if tail ≤ 16 then 2 else 4

def counts (degree capacity : Nat) : ProductCounts × ProductCounts :=
  let tail := degree % 32
  let vectors := 4 * (degree / 32) + tailVectors tail
  let small := if tail ≤ 16 then tailVectors tail else 0
  let reduction := 2 * vectors + 4 * small
  let blocks := degree / 8
  let locator := 4 * blocks * (blocks + 1) + (blocks + 1) * (degree % 8)
  let continuation := (capacity - degree + 7) / 8
  ({ raw := toWord (2 * vectors * capacity), including_reduction := toWord (reduction * capacity) },
    { raw := toWord (2 * (locator + vectors * degree + degree * continuation) + degree),
      including_reduction := toWord
        (6 * locator + reduction * degree + 3 * degree + (2 * degree + 4) * continuation) })

def expectedCounts (degree capacity : Nat) : Option (ProductCounts × ProductCounts) :=
  if degree ≤ capacity ∧ capacity ≤ 65535 then some (counts degree capacity) else none

def selectsRebuilt (degree capacity : Nat) : Bool :=
  if degree ≤ 2 then false else
    match expectedCounts degree capacity with
    | none => false
    | some (current, rebuilt) => decide
      (rebuilt.raw.val ≤ current.raw.val ∧
        rebuilt.including_reduction.val ≤ current.including_reduction.val ∧
        (rebuilt.raw.val < current.raw.val ∨
          rebuilt.including_reduction.val < current.including_reduction.val))

def ProductCountsRefines : Prop :=
  ∀ degree capacity : Usize,
    product_counts degree capacity = Result.ok (expectedCounts degree.val capacity.val)

def UseRebuiltLfsrRefines : Prop :=
  ∀ degree capacity : Usize,
    use_rebuilt_lfsr degree capacity = Result.ok (selectsRebuilt degree.val capacity.val)

end BulksketchBridge.VerifyDispatch
