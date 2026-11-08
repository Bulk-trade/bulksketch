open Aeneas
open Types
open Values
open Contexts
open InterpJoinCore
open InterpMatchCtxs
open InterpUtils

let () =
  let crate = match Charon.OfJson.crate_of_json_file Sys.argv.(1) with
    | Ok crate -> crate | Error error -> failwith error in
  let span = (List.hd (FunDeclId.Map.values crate.fun_decls)).item_meta.span in
  let context = initialize_eval_ctx (Some span) (Interp.compute_contexts crate)
    [] [] [] empty_marked_ids in
  let module State : MatchJoinState = struct
    let fresh_abs_kind = Join
    let span = span
    let nabs = ref []
    let with_abs_conts = false
    let symbolic_to_value = ref SymbolicValueId.Map.empty
    let recover = true
  end in
  let module Primitive = MakeJoinMatcher (State) in
  let module Retry = MakeArrayLoanRetryMatcher (Primitive) in
  let module Original = MakeMatcher (Primitive) in
  let slice = TSlice (TScalar (TInteger (Unsigned U64)), None) in
  let bool_slice = TSlice (TScalar TBool, None) in
  let fresh ty = ValuesUtils.mk_tvalue_from_symbolic_value (mk_fresh_symbolic_value span context ty) in
  let shared_id = context.fresh_borrow_id () in
  let mutable_id = context.fresh_borrow_id () in
  let parent = context.fresh_borrow_id () in
  let different_parent = context.fresh_borrow_id () in
  let shared ty value : tvalue = { ty; value = VLoan (VSharedLoan (shared_id, value)) } in
  let mutable_ ty : tvalue = { ty; value = VLoan (VMutLoan mutable_id) } in
  let wrap id (child : tvalue) : tvalue =
    { ty = TRef (RErased, child.ty, RMut); value = VBorrow (VMutBorrow (id, child)) } in
  let test name checks matcher left right expected =
    Config.sanity_checks := checks;
    let outcome = try let _ = matcher context context left right in `UnexpectedMatch with
      | ValueMatchFailure (LoanInLeft id) when id = shared_id -> `EndLeftShared
      | ValueMatchFailure (LoanInRight id) when id = shared_id -> `EndRightShared
      | Errors.RFailure -> `Rejected in
    if outcome <> expected then failwith ("unexpected retry outcome: " ^ name);
    Printf.printf "PASS %s\n%!" name in
  let shared_child = shared slice (fresh slice) in
  let mutable_child = mutable_ slice in
  let left = wrap parent shared_child in
  let right = wrap parent mutable_child in
  test "end-left-shared" true Retry.match_tvalues left right `EndLeftShared;
  test "end-right-shared" true Retry.match_tvalues right left `EndRightShared;
  test "unchecked" false Retry.match_tvalues left right `Rejected;
  test "original-mode" true Original.match_tvalues left right `Rejected;
  test "different-parent" true Retry.match_tvalues left (wrap different_parent mutable_child) `Rejected;
  test "no-mutable-parent" true Retry.match_tvalues shared_child mutable_child `Rejected;
  test "different-element-type" true Retry.match_tvalues (wrap parent (shared bool_slice (fresh bool_slice)))
    (wrap parent (mutable_ bool_slice)) `Rejected;
  test "non-symbolic-payload" true Retry.match_tvalues
    (wrap parent (shared slice { ty = slice; value = VBottom })) right `Rejected;
  test "mismatched-payload-type" true Retry.match_tvalues
    (wrap parent (shared slice (fresh bool_slice))) right `Rejected;
  test "mismatched-symbolic-type" true Retry.match_tvalues
    (wrap parent (shared slice { (fresh bool_slice) with ty = slice })) right `Rejected
