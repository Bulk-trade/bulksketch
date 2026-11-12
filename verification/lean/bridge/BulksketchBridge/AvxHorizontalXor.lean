import Arithmetic.AvxHorizontalXorGenerated
import BulksketchBridge.X86PclmulWords
import BulksketchBridge.Algebra.Word

namespace BulksketchBridge.AvxHorizontalXor

open Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxHorizontalRuntime Algebra.Gf64

def parity (value : Word512) : BitVec 64 :=
  ((value 0 false ^^^ value 2 false) ^^^ (value 1 false ^^^ value 3 false)) ^^^
  ((value 0 true ^^^ value 2 true) ^^^ (value 1 true ^^^ value 3 true))

private theorem unsigned_signed (word : BitVec 64) :
    (core.num.U64.from_le_bytes (core.num.I64.to_le_bytes ⟨word⟩)).bv = word := by
  have normal := X86Pclmul.low_refines (word.setWidth 128)
  simp only [bulksketch.backend.x86_pclmul.low, X86PclmulRuntime.moveOut, X86PclmulRuntime.low64,
    BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq,
    X86PclmulRuntime.signedBytes, X86PclmulRuntime.unsignedFromBytes, bind_ok] at normal
  exact congrArg U64.bv (Result.ok_injective normal)

def ActualHorizontalXor : Prop :=
  ∀ value : Word512, bulksketch.backend.x86_vpclmul512.horizontal_xor value = .ok ⟨parity value⟩

theorem horizontal_refines : ActualHorizontalXor := by
  intro value
  have first0 : selectPair 78#i32 0 = 2 := by decide
  have first1 : selectPair 78#i32 1 = 3 := by decide
  have second0 : selectPair 177#i32 0 = 1 := by decide
  simp only [bulksketch.backend.x86_vpclmul512.horizontal_xor, shufflePairs, xorWords,
    bind_ok, shuffleDwords, ite_true, lowPair, lowWord, X86PclmulRuntime.signedBytes,
    X86PclmulRuntime.unsignedFromBytes, show (0 : Fin 4).val < 2 by decide,
    show (1 : Fin 4).val < 2 by decide, first0, first1, second0, Bool.not_false, parity]
  congr 1
  apply U64.bv_eq_imp_eq
  exact unsigned_signed _

end BulksketchBridge.AvxHorizontalXor
