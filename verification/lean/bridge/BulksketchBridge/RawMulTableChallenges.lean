import BulksketchBridge.RawMulTableSpec

/-! Frozen normal-return contracts for the actual first raw-multiplication loop. -/

namespace BulksketchBridge.RawMulTableChallenges

open Aeneas Aeneas.Std

/-- The actual source loop constructs every table entry from its real zero initialization. -/
def initializedTableLoopCompletes : Prop :=
  ∀ left : U64, ∃ table : RawMulTable.Table,
    bulksketch.field.gf64.raw_mul_loop0
      { start := 1#usize, «end» := 16#usize } left (Array.repeat 16#usize 0#u128) =
        Result.ok table ∧ RawMulTable.TableCorrect left table

/-- Any valid initialized prefix, with arbitrary unused tail values, completes normally. -/
def everyInitializedPrefixCompletes : Prop :=
  ∀ (left : U64) (range : core.ops.range.Range Usize) (table : RawMulTable.Table),
    RawMulTable.LoopInvariant left (range, table) →
      ∃ final : RawMulTable.Table,
        bulksketch.field.gf64.raw_mul_loop0 range left table = Result.ok final ∧
          RawMulTable.TableCorrect left final

end BulksketchBridge.RawMulTableChallenges
