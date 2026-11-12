import Arithmetic.BmLocatorGenerated
import BulksketchBridge.MutableZip
import BulksketchBridge.InverseFieldSpec

namespace BulksketchBridge.BmMutable

open Aeneas.Std
open bulksketch.backend.contract bulksketch.decode.bm

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
abbrev mulWord := Inverse.multiplyNativeWord
abbrev Iter := core.slice.iter.IterMut U64
abbrev Zip := MutableZip.State U64 U64
abbrev Pending (S : Type) := S × (S → S)

def NativeMul {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ left right, kernels.ArithmeticInst.mul left right =
    bulksketch.field.gf64.mul fieldDictionary left right

/-- Original mutable loops visit ascending positions. Their returned
continuation performs those writes in reverse visitation order on the
supplied later state. -/
def writesFrom {S : Type} (write : Nat → S → S) (index : Nat) : Nat → S → S
  | 0, state => state
  | count + 1, state => write index (writesFrom write (index + 1) count state)

def replaceIter (iter : Iter) (index : Nat) (word : U64) : Iter :=
  { iter with slice := iter.slice.setAtNat index word }

def iterResult (original : Slice U64) (transform : U64 → U64) (start : Nat)
    (back : Iter → Iter) : Pending Iter :=
  (⟨original, original.length⟩, fun later =>
    back (writesFrom (fun index state => replaceIter state index (transform original[index]!))
      start (original.length - start) later))

def shiftedWord (delta left right : U64) : U64 := left ^^^ mulWord delta right

def zipResult (left right : Slice U64) (delta : U64) (start : Nat)
    (back : Zip → Zip) : Pending Zip :=
  let stop := min left.length right.length
  (MutableZip.stateAt left right stop, fun later =>
    back (writesFrom (fun index state =>
      MutableZip.replaceLeft state index (shiftedWord delta left[index]! right[index]!)) start (stop - start) later))

/-- The four original prefix-scaling branches return the exact forward
iterator and backward function for every admitted starting cursor. -/
def ActualBmScaleLoops : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), NativeMul kernels →
    ∀ (original : Slice U64) (start : Nat) (back : Iter → Iter) (scale : U64), start ≤ original.length →
      let expected := iterResult original (mulWord scale) start back
      locator_loop0_loop2 fieldDictionary kernels ⟨original, start⟩ back scale = .ok expected ∧
      locator_loop0_loop4 fieldDictionary kernels ⟨original, start⟩ back scale = .ok expected ∧
      locator_loop0_loop7 fieldDictionary kernels ⟨original, start⟩ back scale = .ok expected ∧
      locator_loop0_loop9 fieldDictionary kernels ⟨original, start⟩ back scale = .ok expected

def ActualBmNormalizeLoop : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), NativeMul kernels →
    ∀ (original : Slice U64) (start : Nat) (back : Iter → Iter) (inverse : U64), start ≤ original.length →
      locator_loop0_loop0 fieldDictionary kernels ⟨original, start⟩ back inverse =
        .ok (iterResult original (fun word => mulWord word inverse) start back)

/-- Both exact source continuations are retained through the shorter Zip
prefix. Only left words in the visited window are written. -/
def ActualBmShiftedXorLoops : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), NativeMul kernels →
    ∀ (left right : Slice U64) (start : Nat) (back : Zip → Zip) (delta : U64),
      start ≤ min left.length right.length →
      let iter := MutableZip.stateAt left right start
      let expected := zipResult left right delta start back
      locator_loop0_loop3 fieldDictionary kernels iter back delta = .ok expected ∧
      locator_loop0_loop5 fieldDictionary kernels iter back = .ok (zipResult left right 0#u64 start back) ∧
      locator_loop0_loop8 fieldDictionary kernels iter back delta = .ok expected ∧
      locator_loop0_loop10 fieldDictionary kernels iter back = .ok (zipResult left right 0#u64 start back)

end BulksketchBridge.BmMutable
