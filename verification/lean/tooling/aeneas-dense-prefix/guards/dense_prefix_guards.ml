open Aeneas
open Types
open Values
open Contexts

(* These deliberately invalid contexts test the actual expansion visitors. *)
let rejected name expected action =
  match action () with
  | _ -> failwith (name ^ " unexpectedly accepted an invalid projector")
  | exception Errors.CFailure { msg; file; _ }
    when msg = expected && Filename.basename file = "InterpExpansion.ml" ->
      Printf.printf "PASS %s\n%!" name

let make_context base span ~kind ~expression ~matching_owner ~matching_child =
  let region = RVar (Free (base.fresh_region_id ())) in
  let ty = TRef (region, TypesUtils.mk_unit_ty, kind) in
  let target = InterpUtils.mk_fresh_symbolic_value span base ty in
  let owner =
    if matching_owner then target
    else InterpUtils.mk_fresh_symbolic_value span base ty
  in
  let child =
    if matching_child then target
    else InterpUtils.mk_fresh_symbolic_value span base ty
  in
  let consumed : mconsumed_symb = { sv_id = child.sv_id; proj_ty = ty } in
  let avalues, cont =
    if expression then
      let loan = EProjLoans { proj = { sv_id = child.sv_id; proj_ty = ty };
                             consumed = []; borrows = [] } in
      let proj = EProjBorrows { proj = { sv_id = owner.sv_id; proj_ty = ty };
                               loans = [ (consumed, loan) ] } in
      let output = Some ({ value = ESymbolic (PNone, proj); ty } : tevalue) in
      ([], Some { output; input = None })
    else
      let loan = AProjLoans { proj = { sv_id = child.sv_id; proj_ty = ty };
                             consumed = []; borrows = [] } in
      let proj = AProjBorrows { proj = { sv_id = owner.sv_id; proj_ty = ty };
                               loans = [ (consumed, loan) ] } in
      ([ ({ value = ASymbolic (PNone, proj); ty } : tavalue) ], None)
  in
  let abs : abs =
    { abs_id = base.fresh_abs_id (); kind = Identity; can_end = true;
      parents = AbsId.Set.empty; regions = { owned = RegionSet.singleton region };
      ended_subabs = AbsLevelSet.empty; avalues; cont }
  in
  ({ base with env = EAbs abs :: base.env }, target)

let () =
  Config.sanity_checks := true;
  let crate =
    match Charon.OfJson.crate_of_json_file Sys.argv.(1) with
    | Ok crate -> crate
    | Error message -> failwith message
  in
  let span = (List.hd (FunDeclId.Map.values crate.fun_decls)).item_meta.span in
  let base = InterpUtils.initialize_eval_ctx (Some span)
    (Interp.compute_contexts crate) [] [] [] empty_marked_ids in
  List.iter (fun expression ->
    let location = if expression then "expression" else "abstraction" in
    List.iter (fun matching_owner ->
      let ctx, target = make_context base span ~kind:RShared ~expression ~matching_owner
        ~matching_child:(not matching_owner) in
      let case, message =
        if matching_owner then ("owner", "Unreachable")
        else ("child", "Internal error, please file an issue")
      in
      rejected ("shared-" ^ location ^ "-" ^ case) message (fun () ->
        InterpExpansion.expand_symbolic_value_no_branching span target None ctx)
    ) [ true; false ]
  ) [ false; true ];
  let ctx, target = make_context base span ~kind:RMut ~expression:false
    ~matching_owner:false ~matching_child:false in
  rejected "non-shared-expansion-with-loans" "Unreachable" (fun () ->
    InterpExpansion.expand_symbolic_value_no_branching span target None ctx)
