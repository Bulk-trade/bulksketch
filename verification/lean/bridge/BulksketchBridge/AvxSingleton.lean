import Arithmetic.AvxSingletonGenerated
import BulksketchBridge.AvxSingletonSchedules
import BulksketchBridge.AvxSingletonBlocks
import BulksketchBridge.AvxEncodeInsert

namespace BulksketchBridge.AvxSingleton

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime Aeneas.Std.AvxEncode18Runtime
open AvxEncode18 AvxSquare AvxUpdateSingleBlock Algebra.Gf64 DenseCoefficient RebuiltLfsr
open X86MaskedMemory Avx512RegisterChallenges AvxEncodeEntry
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

private theorem unpack_normal (a b : Word512) :
    Avx512Register.unpack false a b = .ok (permuteTwoValue a unpackIndices b) := by
  unfold Avx512Register.unpack
  apply congrArg Result.ok
  have equal : flatten (fun pair high => if high then b pair false else a pair false) =
      flatten (permuteTwoValue a unpackIndices b) := by
    funext lane
    simp only [permuteTwoValue, flatten_unflatten]
    fin_cases lane <;> rfl
  exact (unflatten_flatten _).symm.trans ((congrArg unflatten equal).trans (unflatten_flatten _))

private theorem broadcast_normal (index : I64) (base : Word512) :
    bulksketch.backend.x86_vpclmul512.broadcast index base = .ok (permuteValue (spread index) base) := by
  simp only [bulksketch.backend.x86_vpclmul512.broadcast, Avx512Register.broadcast, bind_ok, permute]
  rfl

def ActualNativeAvxBroadcast : Prop :=
  ∀ (index : I64) (base : Word512),
    bulksketch.backend.x86_vpclmul512.broadcast index base = .ok (permuteValue (spread index) base)

theorem native_avx_broadcast : ActualNativeAvxBroadcast := broadcast_normal

private theorem signed_root (id : U64) :
    (core.num.I64.from_le_bytes (core.num.U64.to_le_bytes id)).bv = id.bv := by
  have original := AvxHorner.broadcast_normal id
  simp only [X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes, bind_ok,
    Avx512Register.broadcast] at original
  exact congrFun (congrFun (Result.ok_injective original) 0) false

private theorem prefix_full (odd : Slice U64) (width : Nat) (length : odd.length = width) :
    prefixSlice odd width = odd := by
  apply Slice.ext
  simp [prefixSlice, ← length, Slice.length]

private theorem restore_full (odd updated : Slice U64) (same : updated.length = odd.length) :
    restorePrefix odd updated = updated := by
  apply Slice.ext
  simp only [restorePrefix, Slice.from_val, List.setSlice!, List.take_zero, List.nil_append, Nat.zero_add]
  have noTail : odd.val.drop updated.val.length = [] := List.drop_eq_nil_of_le (by
    change odd.length ≤ updated.length
    omega)
  rw [Nat.sub_zero, Nat.min_eq_left (show updated.val.length ≤ odd.val.length from same.le),
    List.take_length, noTail, List.append_nil]

private theorem scheduled_update (id : U64) (base : Word512) (schedule : List Expr) (count : Nat)
    (basisLaw : ∀ lane : Fin 8, toField (flatten base lane) =
      if lane.val < 7 then toField id.bv ^ (2 ^ (lane.val + 1)) else 0)
    (exponentLaw : ∀ block < schedule.length, ∀ lane : Fin 8,
      exponents schedule[block]! lane = some (2 * (8 * block + lane.val) + 1))
    (odd : Slice U64) (room : odd.length ≤ 8 * count) (countBound : count ≤ schedule.length) :
    Update odd (writeBlocks ((schedule.take count).map (evaluate id base)) odd 0) [id] := by
  let regs := (schedule.take count).map (evaluate id base)
  have countEq : regs.length = count := by
    simp [regs, List.length_take, Nat.min_eq_left countBound]
  refine ⟨blocks_length .., ?_⟩
  intro row inside
  have active : 0 ≤ row ∧ row < 0 + 8 * regs.length := by omega
  have blockRoom : row / 8 < count := by omega
  change toField (writeBlocks regs odd 0)[row]!.bv = _
  rw [blocks_word regs odd 0 row inside, dite_eq_left active, Nat.sub_zero, toField_xor]
  have selected : regs[row / 8]! = evaluate id base schedule[row / 8]! := by
    simp only [regs, List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      ite_eq_left blockRoom]
    have present : row / 8 < schedule.length := by omega
    simp only [List.getElem?_eq_getElem present]
    rfl
  rw [selected, evaluate_lanes id base basisLaw, exponentLaw _ (by omega)]
  simp only [exponentValue, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, AvxTileChunkSum.oddPower]
  congr 2
  omega

private theorem mul_normal (a b : Word512) : multiply true a b = .ok (productsReduced a b) :=
  Avx512Register.multiply_refines true a b

theorem single_normal (load : Load) (store : Store) (loadLaw : LoadLaw load) (storeLaw : StoreLaw store)
    (baseModel : Bases) (id : U64) (base : Word512) (lookup : baseModel id = .ok base)
    (odd : Slice U64) (C : Usize) (width : odd.length = C.val)
    (cap : C = 72#usize ∨ C = 89#usize) :
    insert_single baseModel load store C odd id =
      .ok (writeBlocks ((scheduleSingle.take (if C = 72#usize then 9 else 12)).map (evaluate id base)) odd 0) := by
  have initial := prefix_normal odd C (by omega)
  rw [prefix_full odd C.val width] at initial
  have update (frame : Slice U64) (offset : Usize) (value : Word512)
      (small : offset.val + 8 ≤ Usize.max) (inFrame : offset.val ≤ frame.length) :
      update_single_block load store frame offset value = .ok (blockOutput frame offset.val value) :=
    update_single_block_refines load store loadLaw storeLaw frame offset value small inFrame
  have restore (updated : Slice U64) (same : updated.length = odd.length) :
      restorePrefix odd updated = updated := restore_full odd updated same
  rw [insert_single, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, initial, bind_ok]
  dsimp! only
  simp only [lookup, X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes, signed_root,
    Avx512Register.broadcast, bind_ok, broadcast_normal, unpack_normal, set8, permuteTwo, mul_normal]
  have a : 72#usize > 32#usize := by decide
  have b : 89#usize > 32#usize := by decide
  have c : ¬ 72#usize > 72#usize := by decide
  have d : 89#usize > 72#usize := by decide
  have e : 89#usize ≠ 72#usize := by decide
  rcases cap with rfl | rfl <;>
    simp only [a, b, c, d, e, eq_self, ite_true, ite_false]
  all_goals
    repeat
      (rw [update, bind_ok] <;> try first
        | (simp only [block_length, width]; scalar_tac)
        | scalar_tac)
    rw [restore _ (by simp only [block_length])]
    rfl

/-- Both original const-specialized singleton kernels produce the full
ascending odd-power update, including the single live lane in the 89 tail. -/
def ActualNativeAvxSingleton : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
  ∀ (C : Usize), C = 72#usize ∨ C = 89#usize →
    SingleLaw (insert_single (single_bases INSERT_BASES load) load store C) C.val

theorem native_avx_singleton : ActualNativeAvxSingleton := by
  intro load store loadLaw storeLaw C cap odd id width
  obtain ⟨base, normal, basis⟩ := AvxInsertionBases.static_supplies_bases load loadLaw id
  let count := if C = 72#usize then 9 else 12
  refine ⟨writeBlocks ((scheduleSingle.take count).map (evaluate id base)) odd 0,
    single_normal load store loadLaw storeLaw _ id base normal odd C width cap, ?_⟩
  apply scheduled_update id base scheduleSingle count basis
  · intro block inside lane
    exact single_exponents ⟨block, by simpa using inside⟩ lane
  · rcases cap with rfl | rfl <;> simp [count, width]
  · rcases cap with rfl | rfl <;> simp [count]

#print axioms native_avx_singleton

/-- This is the original range borrow and the following load/XOR/store group.
The continuation receives the restored full frame. -/
private def fullBlock {α : Type} (load : Load) (store : Store) (odd : Slice U64)
    (start stop : Usize) (value : Word512) (next : Slice U64 → Result α) : Result α := do
  let (window, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U64) odd ⟨start, stop⟩
  let old ← load window
  let changed ← Avx512Register.xorWords old value
  let written ← store window changed
  next (back written)

private theorem full_block_normal {α : Type} (load : Load) (store : Store)
    (loadLaw : LoadLaw load) (storeLaw : StoreLaw store)
    (odd : Slice U64) (start stop : Usize) (width : stop.val = start.val + 8) (room : stop.val ≤ odd.length)
    (value : Word512) (next : Slice U64 → Result α) :
    fullBlock load store odd start stop value next = next (blockOutput odd start.val value) := by
  let region := ClosedLeaf.region odd start.val stop.val
  have fits : region.length ≤ 8 := by
    rw [ClosedLeaf.region_length _ _ _ room, width]; omega
  have stopEq : blockStop odd start.val = stop.val := by
    unfold blockStop
    omega
  have read := loadLaw region fits
  have write := storeLaw region (blockRegister odd start.val value) fits
  have exactRegister : (fun pair high => loadWords region pair high ^^^ value pair high) =
      blockRegister odd start.val value := by
    unfold blockRegister
    rw [stopEq]
  unfold fullBlock
  rw [Slice.index_mut_SliceIndexRangeUsizeSliceInst, ClosedLeaf.mutable_region_normal _ _ _ (by omega) room, bind_ok]
  dsimp! only
  change (do
    let old ← load region
    let changed ← Avx512Register.xorWords old value
    let written ← store region changed
    next (odd.setSlice! start.val written.val)) = _
  rw [read, bind_tc_ok, Avx512Register.xorWords, bind_tc_ok, exactRegister, write, bind_tc_ok]
  unfold blockOutput
  rw [stopEq]
  dsimp only
  rw [dite_eq_left fits]

theorem width32_normal (load : Load) (store : Store) (loadLaw : LoadLaw load) (storeLaw : StoreLaw store)
    (baseModel : Bases) (id : U64) (base : Word512) (lookup : baseModel id = .ok base)
    (odd : Slice U64) (width : odd.length = 32) :
    insert_32 baseModel load store odd id =
      .ok (writeBlocks (schedule32.map (evaluate id base)) odd 0) := by
  have initial := prefix_normal odd 32#usize (by exact width.ge)
  rw [prefix_full odd (32#usize).val (by exact width)] at initial
  let values := schedule32.map (evaluate id base)
  rw [insert_32, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, initial, bind_ok]
  dsimp! only
  simp only [lookup, X86PclmulRuntime.unsignedBytes, X86PclmulRuntime.signedFromBytes, signed_root,
    Avx512Register.broadcast, bind_ok, set8, permute, permuteTwo, maskMove, mul_normal]
  change fullBlock load store odd 0#usize 8#usize values[0]! (fun first =>
    fullBlock load store first 8#usize 16#usize values[1]! (fun second =>
      fullBlock load store second 16#usize 24#usize values[2]! (fun third =>
        fullBlock load store third 24#usize 32#usize values[3]! (fun final =>
          Result.ok (restorePrefix odd final))))) = _
  rw [full_block_normal load store loadLaw storeLaw odd 0#usize 8#usize rfl
    (by change 8 ≤ odd.length; omega) values[0]!]
  rw [full_block_normal load store loadLaw storeLaw _ 8#usize 16#usize rfl
    (by simp only [block_length, width]; decide) values[1]!]
  rw [full_block_normal load store loadLaw storeLaw _ 16#usize 24#usize rfl
    (by simp only [block_length, width]; decide) values[2]!]
  rw [full_block_normal load store loadLaw storeLaw _ 24#usize 32#usize rfl
    (by simp only [block_length, width]; decide) values[3]!]
  change Result.ok (restorePrefix odd (writeBlocks values odd 0)) = _
  rw [restore_full odd _ (blocks_length ..)]

/-- The exact 32-word singleton helper contributes one odd power per
slot using its original four register windows and writebacks. -/
def ActualNativeAvxSingleton32 : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    SingleLaw (insert_32 (single_bases INSERT_BASES load) load store) 32

theorem native_avx_singleton32 : ActualNativeAvxSingleton32 := by
  intro load store loadLaw storeLaw odd id width
  obtain ⟨base, normal, basis⟩ := AvxInsertionBases.static_supplies_bases load loadLaw id
  refine ⟨writeBlocks (schedule32.map (evaluate id base)) odd 0,
    width32_normal load store loadLaw storeLaw _ id base normal odd width, ?_⟩
  change Update odd (writeBlocks ((schedule32.take 4).map (evaluate id base)) odd 0) [id]
  apply scheduled_update id base schedule32 4 basis
  · intro block inside lane
    exact width32_exponents ⟨block, by simpa using inside⟩ lane
  · simp [width]
  · simp

#print axioms native_avx_singleton32

end BulksketchBridge.AvxSingleton
