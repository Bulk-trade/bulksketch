import BulksketchBridge.AvxSliceKernelHeap

namespace BulksketchBridge.AvxSliceKernel

open Aeneas.Std Aeneas.Std.AvxSquareRuntime
open AvxSquare X86MaskedMemory X86MaskedMemory.Allocation
open Algebra.Gf64
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

theorem full_scan (op : Operation) (live : LiveAllocations) (la57 : Bool)
    (dstBase srcBase : Address) (permit : Address → Bool) (dst src : Slice U64)
    (heap : AddressHeap) (same : dst.length = src.length)
    (dstView : WriteView live la57 heap permit dstBase (8 * dst.length) 8)
    (dstBytes : FiniteWordWindow heap dstBase dst.length (fun i => dst[i]!.bv))
    (srcView : ReadView live la57 heap srcBase (8 * src.length) 8)
    (srcBytes : FiniteWordWindow heap srcBase src.length (fun i => src[i]!.bv))
    (apart : Disjoint dstBase (8 * dst.length) srcBase (8 * src.length)) :
    let final := evalFrom op dst src 0
    ∃ updated, AllocatedTrace op dstBase srcBase permit src 0 dst heap final updated ∧
      FiniteWordWindow updated dstBase final.length (fun i => final[i]!.bv) ∧
      WriteView live la57 updated permit dstBase (8 * final.length) 8 ∧
      FramesOutside heap updated dstBase (8 * dst.length) := by
  have init : Prefix op dst src dst 0 := by
    refine ⟨rfl, ?_⟩
    intro i _
    rw [ite_eq_right (Nat.not_lt_zero i)]
  exact allocated_slice_scan op live la57 dstBase srcBase permit dst src dst 0 heap same init
    dstView dstBytes srcView srcBytes apart

def ActualAllocatedSquareKernel : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (CL : Bool) (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
      (permit : Address → Bool) (dstBase srcBase : Address) (dst src : Slice U64),
      dst.length = src.length →
      WriteView live la57 heap permit dstBase (8 * dst.length) 8 →
      FiniteWordWindow heap dstBase dst.length (fun i => dst[i]!.bv) →
      ReadView live la57 heap srcBase (8 * src.length) 8 →
      FiniteWordWindow heap srcBase src.length (fun i => src[i]!.bv) →
      Disjoint dstBase (8 * dst.length) srcBase (8 * src.length) →
      let final := evalFrom .square dst src 0
      ∃ updated, square_kernel load store CL dst src = .ok final ∧
        AllocatedTrace .square dstBase srcBase permit src 0 dst heap final updated ∧
        FiniteWordWindow updated dstBase dst.length (fun i => final[i]!.bv) ∧
        WriteView live la57 updated permit dstBase (8 * dst.length) 8 ∧
        FramesOutside heap updated dstBase (8 * dst.length)

theorem allocated_square_kernel : ActualAllocatedSquareKernel := by
  intro load store loadLaw storeLaw CL live la57 heap permit dstBase srcBase dst src same dstView dstBytes
    srcView srcBytes apart final
  obtain ⟨updated, trace, words, view, frame⟩ :=
    full_scan .square live la57 dstBase srcBase permit dst src heap same dstView dstBytes srcView srcBytes apart
  refine ⟨updated, ?_, trace, by simpa only [eval_length] using words, by simpa only [eval_length] using view, frame⟩
  rw [square_kernel_refines load store loadLaw storeLaw CL dst src]
  change Result.ok (model Operation.square.kernel dst.length (pairAt dst src 0 0)).fst.words = _
  rw [model_words .square dst src same 0 _ (by omega)]

def XorLaw (xor : AvxSliceKernelRuntime.Xor) : Prop :=
  ∀ dst src : Slice U64, dst.length = src.length → xor dst src = .ok (evalFrom (.scale 1#u64) dst src 0)

def ScaleTrace (scale : U64) (dstBase srcBase : Address) (permit : Address → Bool)
    (dst src : Slice U64) (before after : AddressHeap) (written : Slice U64) : Prop :=
  if scale = 0#u64 then after = before ∧ written = dst
  else if scale = 1#u64 then
    AvxXorLlbc.run AvxXorLlbc.program (liftPermission permit)
      ⟨dstBase.toNat, dst.len⟩ ⟨srcBase.toNat, dst.len⟩ (liftHeap before) = some (liftHeap after)
  else AllocatedTrace (.scale scale) dstBase srcBase permit src 0 dst before written after

def ActualAllocatedScaleKernel : Prop :=
  ∀ (load : Load) (store : Store) (xor : AvxSliceKernelRuntime.Xor),
    LoadLaw load → StoreLaw store → XorLaw xor →
    ∀ (CL : Bool) (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
      (permit : Address → Bool) (dstBase srcBase : Address) (dst src : Slice U64) (scale : U64),
      dst.length = src.length →
      WriteView live la57 heap permit dstBase (8 * dst.length) 8 →
      FiniteWordWindow heap dstBase dst.length (fun i => dst[i]!.bv) →
      ReadView live la57 heap srcBase (8 * src.length) 8 →
      FiniteWordWindow heap srcBase src.length (fun i => src[i]!.bv) →
      Disjoint dstBase (8 * dst.length) srcBase (8 * src.length) →
      let final := if scale = 0#u64 then dst else evalFrom (.scale scale) dst src 0
      ∃ updated, scale_kernel load store xor CL dst src scale = .ok final ∧
        ScaleTrace scale dstBase srcBase permit dst src heap updated final ∧
        FiniteWordWindow updated dstBase dst.length (fun i => final[i]!.bv) ∧
        WriteView live la57 updated permit dstBase (8 * dst.length) 8 ∧
        FramesOutside heap updated dstBase (8 * dst.length)

private theorem scaled_one_word (dst src : Slice U64) (i : Nat) (inside : i < dst.length) :
    (evalFrom (.scale 1#u64) dst src 0)[i]!.bv = dst[i]!.bv ^^^ src[i]!.bv := by
  rw [eval_word (.scale 1#u64) dst src 0 i inside, ite_eq_left (Nat.zero_le _)]
  have multiplied : multiplyWord src[i]!.bv (1#u64).bv = src[i]!.bv := by
    apply toField_injective
    change toField (multiplyWord src[i]!.bv 1) = _
    rw [toField_mul, toField_one, mul_one]
  change dst[i]!.bv ^^^ multiplyWord src[i]!.bv (1#u64).bv = _
  rw [multiplied]

theorem allocated_scale_kernel : ActualAllocatedScaleKernel := by
  intro load store xor loadLaw storeLaw xorLaw CL live la57 heap permit dstBase srcBase dst src scale
    same dstView dstBytes srcView srcBytes apart final
  have native := scale_kernel_refines load store xor loadLaw storeLaw CL dst src scale
  by_cases zero : scale = 0#u64
  · refine ⟨heap, ?_, ?_, ?_, dstView, fun _ _ => rfl⟩
    · rw [native, ite_eq_left zero]
      simp only [final, zero, ite_true]
    · simp [ScaleTrace, final, zero]
    · simpa only [final, zero, ite_true] using dstBytes
  · by_cases one : scale = 1#u64
    · have finalExact : final = evalFrom (.scale 1#u64) dst src 0 := by
        unfold final
        rw [ite_eq_right zero, one]
      have xorOut := allocated_xor_refines live la57 heap dstBase srcBase dst.len permit
        (fun i => dst[i]!.bv) (fun i => src[i]!.bv)
      rw [Slice.len_val] at xorOut
      obtain ⟨updated, ran, words, frame⟩ := xorOut dstView
        (by rwa [same]) (by rwa [← same] at apart) dstBytes (by rwa [same])
      have finalWords : FiniteWordWindow updated dstBase dst.length (fun i => final[i]!.bv) := by
        intro i inside byte
        change _ = some (wordByte final[i]!.bv byte)
        rw [finalExact, scaled_one_word dst src i inside]
        exact words i inside byte
      refine ⟨updated, ?_, ?_, finalWords, write_view_from_words dstView _ finalWords, frame⟩
      · rw [native, ite_eq_right zero, ite_eq_left one, xorLaw dst src same]
        rw [finalExact]
      · simp only [ScaleTrace, zero, one, ite_false, ite_true]
        exact ran
    · obtain ⟨updated, trace, words, view, frame⟩ :=
        full_scan (.scale scale) live la57 dstBase srcBase permit dst src heap same
          dstView dstBytes srcView srcBytes apart
      refine ⟨updated, ?_, ?_, ?_, by simpa only [eval_length] using view, frame⟩
      · rw [native, ite_eq_right zero, ite_eq_right one,
          show Kernel.scale (broadcastWord scale) = (Operation.scale scale).kernel from rfl,
          model_words (.scale scale) dst src same 0 _ (by omega)]
        simp only [final, zero, ite_false]
      · simpa only [ScaleTrace, zero, one, ite_false, final] using trace
      · simpa only [final, zero, ite_false, eval_length] using words

#print axioms allocated_square_kernel
#print axioms allocated_scale_kernel

end BulksketchBridge.AvxSliceKernel
