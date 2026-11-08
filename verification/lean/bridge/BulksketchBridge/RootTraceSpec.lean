import Arithmetic.RootTraceGenerated
import BulksketchBridge.FrobeniusTablesSupport

namespace BulksketchBridge.RootTrace

open Aeneas Aeneas.Std
open bulksketch.decode.roots bulksketch.backend.contract

abbrev gf64 := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
abbrev Basis := Array U64 64#usize

def basisSeed (seed : U64) : U64 :=
  if 1#u64 < seed then seed else 1#u64

def basisNext (word : U64) : U64 :=
  let bits : BitVec 64 := word.bv
  ⟨(bits <<< (1 : Nat)) ^^^ ((27 : BitVec 64) &&& ((0 : BitVec 64) - (bits >>> (63 : Nat))))⟩

def basisWord (seed : U64) : Nat → U64
  | 0 => basisSeed seed
  | n + 1 => basisNext (basisWord seed n)

def cachePrefix (seed : U64) (basis : Basis) (length : Nat) : Prop :=
  ∀ i, i < length → FrobeniusTables.entry basis i = basisWord seed i

/-- The exact original closure initializes the basis at one live direction. -/
def ActualSeedClosure : Prop :=
  ∀ {K : Type} (backend : BulkKernels K bulksketch.field.Gf64) (seed : U64) (length : U32),
    let fresh := (Array.repeat 64#usize 0#u64).set 0#usize (basisSeed seed)
    Roots.trace.closure.Insts.CoreOpsFunctionFnOnceTupleArrayU6464.call_once
      gf64 backend (seed, length) () = .ok (fresh, (seed, 1#u32)) ∧
    cachePrefix seed fresh 1

/-- The original loop fills only missing directions through the requested
direction. Previously initialized and still uninitialized entries are framed. -/
def ActualBasisExtension : Prop :=
  ∀ (seed : U64) (direction length : U32) (basis : Basis),
    direction.val < 64 → 1 ≤ length.val → length.val ≤ 64 →
    cachePrefix seed basis length.val →
    ∃ finalLength finalBasis,
      Roots.trace_loop0 gf64 direction length basis = .ok (finalLength, finalBasis) ∧
      finalLength.val = max length.val (direction.val + 1) ∧
      cachePrefix seed finalBasis finalLength.val ∧
      (∀ i, i < length.val ∨ finalLength.val ≤ i →
        FrobeniusTables.entry finalBasis i = FrobeniusTables.entry basis i)

end BulksketchBridge.RootTrace
