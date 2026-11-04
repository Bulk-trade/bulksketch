import BulksketchBridge.RawMulTableSpec

/-!
# Frozen second-loop invariant and safety contracts

These claims name the unchanged generated accumulation loop. They assume only
the fully correct table produced by the first loop and a valid nibble position.
The Aeneas StepBy value model advances its range before returning an element;
its correspondence with the Rust standard library remains in the runtime TCB.
-/

namespace BulksketchBridge.RawMulAccum

open Aeneas Aeneas.Std

abbrev Iterator := core.iter.adapters.step_by.StepBy (core.ops.range.Range U32)

/-- The actual runtime-model state after consuming `count` four-bit blocks. -/
def iteratorAt (count : Nat) : Iterator :=
  { iter := { start := ⟨BitVec.ofNat 32 (4 * count)⟩, «end» := 64#u32 },
    step_by := 4#usize }

/-- Exact complete-width accumulator after the first `count` source iterations. -/
def prefixWord (left right : U64) (count : Nat) : U128 :=
  ⟨BulksketchProofs.Field.clmulPrefix left.bv right.bv (4 * count)⟩

/-- Complete unreduced polynomial product; no output bits are discarded. -/
def outputWord (left right : U64) : U128 :=
  ⟨BulksketchProofs.Field.clmul128 left.bv right.bv⟩

/-- The source's masked nibble before its pointer-width cast. -/
def nibbleWord (right : U64) (count : Nat) : U64 :=
  ⟨(right.bv >>> (4 * count)) &&& (15 : BitVec 64)⟩

/-- Every shift/index is permitted and the source cast loses no nibble bits. -/
def NibbleBounds : Prop :=
  ∀ (right : U64) (count : Nat), count < 16 →
    4 * count < 64 ∧ 4 * count < 128 ∧
      (UScalar.cast .Usize (nibbleWord right count)).val < 16 ∧
      (UScalar.cast .Usize (nibbleWord right count)).val = (nibbleWord right count).val ∧
      BitVec.ofNat 4 (UScalar.cast .Usize (nibbleWord right count)).val =
        (right.bv >>> (4 * count)).setWidth 4

/-- Each real body call preserves the complete polynomial-prefix invariant. -/
def BodyStep : Prop :=
  ∀ (left right : U64) (table : RawMulTable.Table),
    RawMulTable.TableCorrect left table →
    ∀ count : Nat, count < 16 →
      bulksketch.field.gf64.raw_mul_loop1.body right table (iteratorAt count)
          (prefixWord left right count) =
        Result.ok (ControlFlow.cont
          (iteratorAt (count + 1), prefixWord left right (count + 1)))

/-- Exhaustion is tested before an invalid shift-by64 could be attempted. -/
def TerminalBody : Prop :=
  ∀ (left right : U64) (table : RawMulTable.Table),
    bulksketch.field.gf64.raw_mul_loop1.body right table (iteratorAt 16)
        (prefixWord left right 16) =
      Result.ok (ControlFlow.done (outputWord left right))

/-- Every reachable nibble prefix completes normally with the exact128-bit result. -/
def EveryPrefixCompletes : Prop :=
  ∀ (left right : U64) (table : RawMulTable.Table),
    RawMulTable.TableCorrect left table →
    ∀ count : Nat, count ≤ 16 →
      bulksketch.field.gf64.raw_mul_loop1 (iteratorAt count) right table
          (prefixWord left right count) =
        Result.ok (outputWord left right)

end BulksketchBridge.RawMulAccum
