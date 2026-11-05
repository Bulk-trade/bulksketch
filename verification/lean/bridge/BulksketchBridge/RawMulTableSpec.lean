import Arithmetic.Funs
import BulksketchProofs.Field.CLMulSpec

/-!
# Independent nibble-table invariant for the first native raw-multiplication loop

The prefix predicate specifies complete 128-bit entries through total optional
getters. It neither assumes a source operation succeeded nor constrains unused
tail values. The source array's fixed length is retained in its actual type.
-/

namespace BulksketchBridge.RawMulTable

open Aeneas Aeneas.Std

abbrev Table := Aeneas.Std.Array U128 16#usize

/-- Every initialized entry is the complete polynomial multiple selected by its nibble. -/
def TablePrefixCorrect (left : U64) (table : Table) (count : Nat) : Prop :=
  ∀ index : Nat, index < count →
    table.val[index]? =
      some (⟨BulksketchProofs.Field.nibbleMultiple left.bv (BitVec.ofNat 4 index)⟩ : U128)

/-- All sixteen entries are exact, including the zero entry. -/
def TableCorrect (left : U64) (table : Table) : Prop :=
  TablePrefixCorrect left table 16

/-- Source loop state: the native range is bounded and its consumed prefix is correct. -/
def LoopInvariant (left : U64)
    (state : core.ops.range.Range Usize × Table) : Prop :=
  state.1.«end» = 16#usize ∧
    1 ≤ state.1.start.val ∧ state.1.start.val ≤ 16 ∧
      TablePrefixCorrect left state.2 state.1.start.val

end BulksketchBridge.RawMulTable
