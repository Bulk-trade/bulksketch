import BulksketchBridge.InverseFieldSpec

/-! New frozen propositions retain every admitted input and callback. Each source
call's normal result is a conclusion. Existing frozen targets are unchanged. -/

namespace BulksketchBridge.InverseChallenges

open Aeneas Aeneas.Std BulksketchBridge.Inverse

def actualSourceReturnsExactChain : Prop :=
  ∀ (T1 T2 : Type)
    (mulDict : core.ops.function.Fn T1 (U64 × U64) U64)
    (frobDict : core.ops.function.Fn T2 (U64 × U32) U64)
    (mulCallback : T1) (frobCallback : T2)
    (multiply : U64 → U64 → U64) (frobenius : U64 → U32 → U64),
    MulNormal mulDict mulCallback multiply →
    FrobeniusNormal frobDict frobCallback frobenius →
    ∀ input : U64,
      bulksketch.field.maps.inverse_with_frobenius
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField mulDict frobDict input
        mulCallback frobCallback = Result.ok (expectedResult multiply frobenius input)

def actualSourceReturnsFieldInverse : Prop :=
  ∀ (T1 T2 : Type)
    (mulDict : core.ops.function.Fn T1 (U64 × U64) U64)
    (frobDict : core.ops.function.Fn T2 (U64 × U32) U64)
    (mulCallback : T1) (frobCallback : T2),
    (∀ left right, mulDict.call mulCallback (left, right) =
      bulksketch.field.gf64.mul
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right) →
    (∀ input count, frobDict.call frobCallback (input, count) =
      bulksketch.field.gf64.frobenius
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input count) →
    ∀ input : U64,
      bulksketch.field.maps.inverse_with_frobenius
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField mulDict frobDict input
        mulCallback frobCallback = Result.ok (expectedFieldInverse input)

/-- A closed, existing-runtime callback instantiation proves that the universal
native-callback premises are satisfiable. This is the original chain body with
actual native mul/Frobenius functions, not the unsupported inverse_using closure. -/
def nativeCallbackInstanceReturnsFieldInverse : Prop :=
  ∀ input : U64,
    bulksketch.field.maps.inverse_with_frobenius
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
      (BuiltinFn (U64 × U64) U64) (BuiltinFn (U64 × U32) U64) input
      (fun arguments => bulksketch.field.gf64.mul
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField arguments.1 arguments.2)
      (fun arguments => bulksketch.field.gf64.frobenius
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField arguments.1 arguments.2) =
      Result.ok (expectedFieldInverse input)

end BulksketchBridge.InverseChallenges
