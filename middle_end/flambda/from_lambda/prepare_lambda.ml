(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2016--2019 OCamlPro SAS                                    *)
(*   Copyright 2016--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

module L = Lambda

(*
let simplify_primitive (prim : L.primitive) args loc =
  match prim, args with
  (* CR mshinwell: What is happening to this?
  | (Pdivint Safe | Pmodint Safe
      | Pdivbint { is_safe = Safe; size = _; }
      | Pmodbint { is_safe = Safe; size = _; }),
    [arg1; arg2]
      when not !Clflags.unsafe ->
    let numerator = Ident.create_local "numerator" in
    let denominator = Ident.create_local "denominator" in
    let zero = Ident.create_local "zero" in
    let is_zero = Ident.create_local "is_zero" in
    let exn = Ident.create_local "division_by_zero" in
    let zero_const : Lambda.structured_constant =
      match prim with
      | Pdivint _ | Pmodint _ ->
        Const_base (Const_int 0)
      | Pdivbint { size = Pint32; is_safe = _; }
      | Pmodbint { size = Pint32; is_safe = _; } ->
        Const_base (Const_int32 0l)
      | Pdivbint { size = Pint64; is_safe = _; }
      | Pmodbint { size = Pint64; is_safe = _; } ->
        Const_base (Const_int64 0L)
      | Pdivbint { size = Pnativeint; is_safe = _; }
      | Pmodbint { size = Pnativeint; is_safe = _; } ->
        Const_base (Const_nativeint 0n)
      | _ -> assert false
    in
    let prim : Lambda.primitive =
      match prim with
      | Pdivint _ -> Pdivint Unsafe
      | Pmodint _ -> Pmodint Unsafe
      | Pdivbint { size; is_safe = _; } -> Pdivbint { size; is_safe = Unsafe; }
      | Pmodbint { size; is_safe = _; } -> Pmodbint { size; is_safe = Unsafe; }
      | _ -> assert false
    in
    let comparison : Lambda.primitive =
      match prim with
      | Pdivint _ | Pmodint _ -> Pintcomp Ceq
      | Pdivbint { size; is_safe = _; }
      | Pmodbint { size; is_safe = _; } -> Pbintcomp (size, Ceq)
      | _ -> assert false
    in
    let expr =
      L.Llet (Strict, Pgenval, zero, Lconst zero_const,
        (Llet (Strict, Pgenval, exn, Lvar Predef.ident_division_by_zero,
          (Llet (Strict, Pgenval, denominator, arg2,
            (Llet (Strict, Pgenval, numerator, arg1,
              (Llet (Strict, Pgenval, is_zero,
                (Lprim (comparison, [L.Lvar zero; L.Lvar denominator], loc)),
                (Lifthenelse (Lvar is_zero,
                  Lprim (Praise Raise_regular, [L.Lvar exn], loc),
                  (* CR-someday pchambart: find the right event.
                     mshinwell: I briefly looked at this, and couldn't
                     figure it out.
                     lwhite: I don't think any of the existing events
                     are suitable. I had to add a new one for a similar
                     case in the array data types work.
                     mshinwell: deferred CR *)
                  Lprim (prim, [L.Lvar numerator; L.Lvar denominator],
                    loc))))))))))))
    in
    prepare env expr (fun lam -> lam)
  | (Pdivint Safe | Pmodint Safe
      | Pdivbint { is_safe = Safe; size = _; }
      | Pmodbint { is_safe = Safe; size = _; }), _
      when not !Clflags.unsafe ->
    Misc.fatal_error "Pdivint / Pmodint must have exactly two arguments"
   *)
*)

let rec prepare (lam : L.lambda) (k : L.lambda -> L.lambda) =
  match lam with
  | Lvar _ | Lconst _ -> k lam
  | Lapply { ap_func; ap_args; ap_loc; ap_should_be_tailcall; ap_inlined;
      ap_specialised; } ->
    prepare ap_func (fun ap_func ->
      prepare_list ap_args (fun ap_args ->
        k (L.Lapply {
          ap_func;
          ap_args;
          ap_loc = ap_loc;
          ap_should_be_tailcall = ap_should_be_tailcall;
          ap_inlined = ap_inlined;
          ap_specialised = ap_specialised;
        })))
  | Lfunction { kind; params; return; body; attr; loc; } ->
    prepare body (fun body ->
      k (L.Lfunction {
        kind = kind;
        params = params;
        return = return;
        body;
        attr = attr;
        loc = loc;
      }))
  | Llet (let_kind, value_kind, id, defining_expr, body) ->
    prepare defining_expr (fun defining_expr ->
      prepare body (fun body ->
        k (L.Llet (let_kind, value_kind, id, defining_expr, body))))
  | Lletrec (bindings, body) ->
    prepare_list_with_idents bindings (fun bindings ->
        prepare body (fun body ->
          k (L.Lletrec (bindings, body))))
  | Lprim (prim, args, loc) ->
    prepare_list args (fun args ->
      k (Lprim (prim, args, loc)))
  | Lswitch (scrutinee, switch, loc) ->
    prepare scrutinee (fun scrutinee ->
      let const_nums, sw_consts = List.split switch.sw_consts in
      let block_nums, sw_blocks = List.split switch.sw_blocks in
      prepare_option switch.sw_failaction (fun sw_failaction ->
        prepare_list sw_consts (fun sw_consts ->
          prepare_list sw_blocks (fun sw_blocks ->
            let switch : L.lambda_switch =
              { sw_numconsts = switch.sw_numconsts;
                sw_consts = List.combine const_nums sw_consts;
                sw_numblocks = switch.sw_numblocks;
                sw_blocks = List.combine block_nums sw_blocks;
                sw_failaction;
              }
            in
            k (Lswitch (scrutinee, switch, loc))))))
  | Lstringswitch (scrutinee, cases, default, loc) ->
    prepare scrutinee (fun scrutinee ->
      let patterns, actions = List.split cases in
      prepare_list actions (fun actions ->
        prepare_option default (fun default ->
          let cases = List.combine patterns actions in
          k (L.Lstringswitch (scrutinee, cases, default, loc)))))
  | Lstaticraise (cont, args) ->
    prepare_list args (fun args ->
      k (L.Lstaticraise (cont, args)))
  | Lstaticcatch (body, (cont, args), handler) ->
    prepare body (fun body ->
      prepare handler (fun handler ->
        k (L.Lstaticcatch (body, (cont, args), handler))))
  | Ltrywith (body, id, handler) ->
    prepare body (fun body ->
      prepare handler (fun handler ->
        k (L.Ltrywith (body, id, handler))))
  | Lifthenelse (cond, ifso, ifnot) ->
    prepare cond (fun cond ->
      prepare ifso (fun ifso ->
        prepare ifnot (fun ifnot ->
          k (L.Lifthenelse(cond, ifso, ifnot)))))
  | Lsequence (lam1, lam2) ->
    prepare lam1 (fun lam1 ->
      prepare lam2 (fun lam2 ->
        k (L.Lsequence(lam1, lam2))))
  | Lwhile (cond, body) ->
    prepare cond (fun cond ->
      prepare body (fun body ->
        k (Lwhile (cond, body))))
  | Lfor (ident, start, stop, dir, body) ->
    prepare start (fun start ->
      prepare stop (fun stop ->
        prepare body (fun body ->
          k (L.Lfor (ident, start, stop, dir, body)))))
  | Lassign (ident, lam) ->
    prepare lam (fun lam -> k (L.Lassign (ident, lam)))
  | Lsend (meth_kind, meth, obj, args, loc) ->
    prepare meth (fun meth ->
      prepare obj (fun obj ->
        prepare_list args (fun args ->
          k (L.Lsend (meth_kind, meth, obj, args, loc)))))
  | Levent (body, event) ->
    prepare body (fun body -> k (L.Levent (body, event)))
  | Lifused _ -> k lam

and prepare_list lams k =
  match lams with
  | [] -> k []
  | lam::lams ->
    prepare lam (fun lam ->
      prepare_list lams (fun lams -> k (lam::lams)))

and prepare_list_with_idents lams k =
  match lams with
  | [] -> k []
  | (id, lam)::lams ->
    prepare lam (fun lam ->
      prepare_list_with_idents lams (fun lams -> k ((id, lam)::lams)))

and prepare_option lam_opt k =
  match lam_opt with
  | None -> k None
  | Some lam -> prepare lam (fun lam -> k (Some lam))

let run lam =
  prepare lam (fun lam -> lam)
