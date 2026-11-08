open Aeneas
open Types
open Values
open Contexts
open InterpUtils

let () =
  let crate =
    match Charon.OfJson.crate_of_json_file Sys.argv.(1) with
    | Ok crate -> crate
    | Error message -> failwith message
  in
  let span = (List.hd (FunDeclId.Map.values crate.fun_decls)).item_meta.span in
  let base = InterpUtils.initialize_eval_ctx (Some span)
    (Interp.compute_contexts crate) [] [] [] empty_marked_ids in
  let region = RVar (Free (base.fresh_region_id ())) in
  let abs_id = base.fresh_abs_id () in
  let context (metadata : tvalue) (child : tavalue) =
    let loan : tavalue =
      { value = ALoan (AEndedSharedLoan (metadata, child));
        ty = TRef (region, metadata.ty, RShared) }
    in
    let abs : abs =
      { abs_id; kind = Identity; can_end = true;
        parents = AbsId.Set.empty; regions = { owned = RegionSet.singleton region };
        ended_subabs = AbsLevelSet.empty; avalues = [loan]; cont = None }
    in
    { base with env = EAbs abs :: base.env }
  in
  let symbolic ty = ValuesUtils.mk_tvalue_from_symbolic_value
      (InterpUtils.mk_fresh_symbolic_value span base ty) in
  let bool = TScalar TBool in
  let scalar = symbolic bool in
  let distinct = symbolic bool in
  let ignored value = ValuesUtils.mk_aignored span bool value in
  let inert = ignored (Some scalar) in
  let loan_child : tavalue =
    { value = ALoan (AIgnoredSharedLoan (ignored None)); ty = bool }
  in
  let nonscalar = symbolic TypesUtils.mk_unit_ty in
  let nonscalar_child = ValuesUtils.mk_aignored span nonscalar.ty (Some nonscalar) in
  let match_case name checks check_equiv expected left right =
    Config.sanity_checks := checks;
    let no_borrow _ = failwith "unexpected live loan lookup" in
    let result =
      InterpMatchCtxs.try_match_ctxs span ~check_equiv
        empty_ids_sets no_borrow no_borrow left right
    in
    if Option.is_some result <> expected then failwith ("unexpected result: " ^ name);
    Printf.printf "PASS %s\n%!" name
  in
  match_case "same-scalar-mapping" true false true
    (context scalar inert) (context scalar inert);
  match_case "same-scalar-equivalence" true true true
    (context scalar inert) (context scalar inert);
  match_case "unequal-symbolic-id" true false false
    (context scalar inert) (context distinct (ignored (Some distinct)));
  match_case "distinct-child-payload" true false false
    (context scalar inert) (context scalar (ignored (Some distinct)));
  match_case "nonempty-child-mismatch" true false false
    (context scalar inert) (context scalar (ignored None));
  match_case "loan-child" true false false
    (context scalar loan_child) (context scalar loan_child);
  match_case "nonscalar-metadata" true false false
    (context nonscalar nonscalar_child) (context nonscalar nonscalar_child);
  match_case "same-scalar-unchecked" false false false
    (context scalar inert) (context scalar inert)
