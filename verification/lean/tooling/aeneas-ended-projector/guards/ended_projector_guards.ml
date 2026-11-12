open Aeneas
open Types
open Values
open Contexts
open InterpUtils

let () =
  let crate = match Charon.OfJson.crate_of_json_file Sys.argv.(1) with
    | Ok crate -> crate
    | Error message -> failwith message in
  let span = (List.hd (FunDeclId.Map.values crate.fun_decls)).item_meta.span in
  let base = initialize_eval_ctx (Some span)
    (Interp.compute_contexts crate) [] [] [] empty_marked_ids in
  let region = RVar (Free (base.fresh_region_id ())) in
  let ty = TRef (region, TScalar TBool, RShared) in
  let id = (mk_fresh_symbolic_value span base ty).sv_id in
  let different_id = (mk_fresh_symbolic_value span base ty).sv_id in
  let abs_id = base.fresh_abs_id () in
  let leaf : aended_proj_loans = { proj = id; consumed = []; borrows = [] } in
  let label : mconsumed_symb = { sv_id = id; proj_ty = ty } in
  let child = AProjLoans { proj = { sv_id = id; proj_ty = ty }; consumed = []; borrows = [] } in
  let context marker ty projector =
    let abs : abs = {
      abs_id; kind = Identity; can_end = true; parents = AbsId.Set.empty;
      regions = { owned = RegionSet.singleton region }; ended_subabs = AbsLevelSet.empty;
      avalues = [{ value = ASymbolic (marker, AEndedProjLoans projector); ty }]; cont = None;
    } in
    { base with env = EAbs abs :: base.env } in
  let match_case name checks check_equiv expected left right =
    Config.sanity_checks := checks;
    let no_live_loan _ = failwith "unexpected live loan lookup" in
    let result = InterpMatchCtxs.try_match_ctxs span ~check_equiv empty_ids_sets
      no_live_loan no_live_loan left right in
    if Option.is_some result <> expected then failwith ("unexpected guard outcome: " ^ name);
    Printf.printf "PASS %s\n%!" name in
  let good = context PNone ty leaf in
  match_case "identical-mapping" true false true good good;
  match_case "identical-equivalence" true true true good good;
  match_case "different-ended-id" true false false good (context PNone ty { leaf with proj = different_id });
  match_case "different-type" true false false good (context PNone (TSlice (TScalar TBool, None)) leaf);
  let consumed = context PNone ty { leaf with consumed = [label, child] } in
  match_case "identical-consumed-child" true false false consumed consumed;
  let borrowed = context PNone ty { leaf with borrows = [label, child] } in
  match_case "identical-borrow-child" true false false borrowed borrowed;
  let marked = context PLeft ty leaf in
  match_case "identical-marked-projector" true false false marked marked;
  match_case "unchecked-identical" false false false good good
