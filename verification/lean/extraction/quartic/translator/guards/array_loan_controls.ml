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
  let width = { kind = CInteger (UnsignedInteger (Usize, Z.of_int 4));
    ty = TScalar (TInteger (Unsigned Usize)) } in
  let scalar = TScalar TBool in
  let array = TArray (scalar, width, None) in
  let nested = TArray (array, width, None) in
  let fresh ty = ValuesUtils.mk_tvalue_from_symbolic_value (mk_fresh_symbolic_value span context ty) in
  let shared_id = context.fresh_borrow_id () in
  let mutable_id = context.fresh_borrow_id () in
  let extra_id = context.fresh_borrow_id () in
  let shared ty value : tvalue = { ty; value = VLoan (VSharedLoan (shared_id, value)) } in
  let mutable_ ty : tvalue = { ty; value = VLoan (VMutLoan mutable_id) } in
  let test name checks matcher left right expected =
    Config.sanity_checks := checks;
    let outcome = try let _ = matcher context context left right in `UnexpectedMatch with
      | ValueMatchFailure (LoanInLeft id) when id = shared_id -> `EndLeftShared
      | ValueMatchFailure (LoanInRight id) when id = shared_id -> `EndRightShared
      | Errors.RFailure -> `Rejected in
    if outcome <> expected then failwith ("unexpected retry outcome: " ^ name);
    Printf.printf "PASS %s\n%!" name in
  let left = shared array (fresh array) in
  let right = mutable_ array in
  test "end-left-shared" true Retry.match_tvalues left right `EndLeftShared;
  test "end-right-shared" true Retry.match_tvalues right left `EndRightShared;
  test "unchecked" false Retry.match_tvalues left right `Rejected;
  test "original-mode" true Original.match_tvalues left right `Rejected;
  test "non-array" true Retry.match_tvalues (shared scalar (fresh scalar)) (mutable_ scalar) `Rejected;
  test "non-scalar-elements" true Retry.match_tvalues (shared nested (fresh nested)) (mutable_ nested) `Rejected;
  test "mismatched-payload-type" true Retry.match_tvalues (shared array (fresh scalar)) right `Rejected;
  test "payload-active-loan" true Retry.match_tvalues
    (shared array { ty = array; value = VLoan (VMutLoan extra_id) }) right `Rejected
