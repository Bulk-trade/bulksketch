import BulksketchBridge.AvxTilePowerLoop
import BulksketchBridge.AvxTileDoubleZip

namespace BulksketchBridge.AvxTileSyndromeLoop

open Aeneas Aeneas.Std Result ControlFlow
open Aeneas.Std.Avx512Register Aeneas.Std.AvxTileRuntime
open BulksketchBridge.AvxTilePowerLoop BulksketchBridge.AvxTileDoubleZip
open bulksketch.backend.x86_vpclmul512

set_option maxHeartbeats 1800000

abbrev OddIter := core.slice.iter.IterMut U64
abbrev OddBack := OddIter → OddIter

def rowUpdate {W : Usize} (zero : Word512) (powers steps : Array Word512 W) :
    U64 × Array Word512 W :=
  let initial : PowerState := ⟨⟨powers.to_slice, 0⟩, ⟨steps.to_slice, 0⟩⟩
  let (sum, final, back) := powerWrites powers.to_slice.length initial id zero
  (⟨AvxHorizontalXor.parity sum⟩, powers.from_slice (back final).fst.slice)

theorem row_body_active {W : Usize} (CL : Bool) (zero : Word512)
    (iter : OddIter) (back : OddBack) (powers steps : Array Word512 W)
    (more : iter.i < iter.slice.length) :
    insert_tile_loop1.body CL zero steps iter back powers =
      .ok (.cont ({ iter with i := iter.i + 1 }, fun later =>
        back (overwrite iter.i later (some (iter.slice[iter.i]! ^^^ (rowUpdate zero powers steps).1))),
        (rowUpdate zero powers steps).2)) := by
  have guard : iter.i < iter.slice.len.val := by simpa using more
  have next : core.slice.iter.IteratorIterMut.next iter =
      .ok (some (iter.slice[iter.i]'more), { iter with i := iter.i + 1 }, overwrite iter.i) := by
    unfold core.slice.iter.IteratorIterMut.next
    split
    · rfl
    · contradiction
  have construct :
      AvxTileRuntime.zipConstruct (mutableWords Word512)
        (SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter Word512 W)
        (⟨powers.to_slice, 0⟩ : PowerIter) steps =
      .ok ((⟨⟨powers.to_slice, 0⟩, ⟨steps.to_slice, 0⟩⟩ : PowerState), fun state => state.fst) := by
    change Aeneas.Std.MutableZip.construct
      (SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter Word512 W) ⟨powers.to_slice, 0⟩ steps = _
    simp only [Aeneas.Std.MutableZip.construct,
      SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
    rfl
  have inner := power_loop_refines CL
    (⟨⟨powers.to_slice, 0⟩, ⟨steps.to_slice, 0⟩⟩ : PowerState) id zero
  change insert_tile_loop1_loop0 CL _ (fun state => state) zero =
    .ok (powerWrites powers.to_slice.length _ id zero) at inner
  rw [insert_tile_loop1.body, next, bind_ok]
  simp only [Array.to_slice_mut, core.slice.Slice.iter_mut, lift, bind_ok]
  dsimp! only
  rw [construct, bind_ok]
  dsimp! only
  rw [inner, bind_ok]
  dsimp! only
  unfold rowUpdate
  dsimp! only
  generalize powerWrites powers.to_slice.length
    (⟨⟨powers.to_slice, 0⟩, ⟨steps.to_slice, 0⟩⟩ : PowerState) id zero = result
  rcases result with ⟨sum, final, restore⟩
  simp only
  rw [AvxHorizontalXor.horizontal_refines sum, bind_ok,
    Slice.Inhabited_getElem_eq_getElem! iter.slice iter.i more]

theorem row_body_done {W : Usize} (CL : Bool) (zero : Word512)
    (iter : OddIter) (back : OddBack) (powers steps : Array Word512 W)
    (done : iter.slice.length ≤ iter.i) :
    insert_tile_loop1.body CL zero steps iter back powers = .ok (.done (iter, back)) := by
  have guard : ¬ iter.i < iter.slice.len.val := by simpa using Nat.not_lt.mpr done
  have next : core.slice.iter.IteratorIterMut.next iter = .ok (none, iter, fun later _ => later) := by
    unfold core.slice.iter.IteratorIterMut.next
    split
    · contradiction
    · rfl
  rw [insert_tile_loop1.body, next, bind_ok]
  rfl

def rowWrites {W : Usize} (zero : Word512) (steps : Array Word512 W) :
    Nat → OddIter → OddBack → Array Word512 W → OddIter × OddBack
  | 0, iter, back, _ => (iter, back)
  | fuel + 1, iter, back, powers =>
    if iter.i < iter.slice.length then
      let (row, next) := rowUpdate zero powers steps
      rowWrites zero steps fuel { iter with i := iter.i + 1 }
        (fun later => back (overwrite iter.i later (some (iter.slice[iter.i]! ^^^ row)))) next
    else (iter, back)

theorem row_loop_refines {W : Usize} (CL : Bool) (zero : Word512)
    (iter : OddIter) (back : OddBack) (powers steps : Array Word512 W) :
    insert_tile_loop1 CL zero iter back powers steps =
      .ok (rowWrites zero steps (iter.slice.length - iter.i) iter back powers) := by
  suffices ∀ fuel iter, iter.slice.length - iter.i = fuel → ∀ back powers,
    insert_tile_loop1 CL zero iter back powers steps =
      .ok (rowWrites zero steps fuel iter back powers) from
    this (iter.slice.length - iter.i) iter rfl back powers
  intro fuel
  induction fuel with
  | zero =>
    intro iter empty back powers
    conv_lhs => unfold insert_tile_loop1 loop
    dsimp only
    rw [row_body_done CL zero iter back powers steps (by omega), bind_ok]
    rfl
  | succ fuel ih =>
    intro iter count back powers
    by_cases more : iter.i < iter.slice.length
    · have cursor : iter.slice.length - (iter.i + 1) = fuel := by omega
      conv_lhs => unfold insert_tile_loop1 loop
      dsimp only
      rw [row_body_active CL zero iter back powers steps more, bind_ok]
      change insert_tile_loop1 CL zero { iter with i := iter.i + 1 } _ _ steps = _
      rw [ih { iter with i := iter.i + 1 } cursor]
      simp only [rowWrites, ite_eq_left more]
    · conv_lhs => unfold insert_tile_loop1 loop
      dsimp only
      rw [row_body_done CL zero iter back powers steps (by omega), bind_ok]
      simp only [rowWrites, ite_eq_right more]

#print axioms row_body_active
#print axioms row_body_done
#print axioms row_loop_refines

end BulksketchBridge.AvxTileSyndromeLoop
