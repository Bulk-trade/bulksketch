import BulksketchBridge.RawMulSpec
import BulksketchBridge.RawMulAccumSpec
import BulksketchBridge.RawMulTable
import BulksketchBridge.RawMulAccum
import BulksketchBridge.Gf64Reduce
import BulksketchProofs.Field.CLMul

namespace BulksketchBridge.RawMul

open Aeneas Aeneas.Std

/-- The split output specification retains the entire unreduced product. -/
theorem expectedProduct_join (left right : U64) :
    BulksketchProofs.Field.join128 (expectedProduct left right).lo.bv
      (expectedProduct left right).hi.bv = BulksketchProofs.Field.clmul128 left.bv right.bv :=
  BulksketchProofs.Field.join128_split _

private theorem canonical_mask (word : U64) :
    word &&& ~~~bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK = 0#u64 := by
  apply U64.bv_eq_imp_eq
  simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK,
    core.num.U64.MAX, U64.rMax]

private theorem shiftRight64 (word : U128) :
    word >>> (64#i32) = Result.ok (⟨word.bv >>> (64 : Nat)⟩ : U128) := by rfl

private theorem initial_iterator :
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepU32)
      { start := 0#u32, «end» := 64#u32 } 4#usize =
        Result.ok (RawMulAccum.iteratorAt 0) := by rfl

/-- Both original loops and the final casts return the complete polynomial
product for every pair of native-width operands, without a success premise. -/
theorem raw_mul_refines : ReturnsCompleteProduct := by
  intro left right
  obtain ⟨table, tableNormal, tableCorrect⟩ :=
    RawMulTable.initialized_table_loop_completes left
  have accumulation := RawMulAccum.every_prefix_completes left right table tableCorrect 0 (by decide)
  have prefixZero : RawMulAccum.prefixWord left right 0 = 0#u128 := by rfl
  rw [prefixZero] at accumulation
  simp only [bulksketch.field.gf64.raw_mul,
    lift, bind_ok, canonical_mask, ite_true, tableNormal,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
    initial_iterator]
  rw [accumulation]
  simp only [bind_ok, shiftRight64]
  rfl

/-- The actual unreduced source result has exactly the polynomial convolution
coefficient at every output position, including its zero top coefficient. -/
theorem raw_mul_coefficients : ReturnsCoefficientConvolution := by
  intro left right index hi
  refine ⟨expectedProduct left right, raw_mul_refines left right, ?_⟩
  rw [expectedProduct_join]
  exact BulksketchProofs.Field.clmul128_bits left.bv right.bv index hi

/-- Actual multiplication composes the complete raw product and the actual
Gf64 reduction, producing its canonical-degree polynomial division certificate. -/
theorem mul_division_certificate : ReducedMultiplication := by
  intro left right
  obtain ⟨output, normal, _, certificate⟩ :=
    Gf64Reduce.reduce_refines (expectedProduct left right)
  refine ⟨output, ?_, ?_⟩
  · rw [bulksketch.field.gf64.mul, raw_mul_refines left right]
    simp only [bind_ok, normal]
  · rw [expectedProduct_join] at certificate
    exact certificate

end BulksketchBridge.RawMul
