open! Std

open Parsetree

type node =
  | Dummy
  | Expression of expression
  | Pattern of pattern
  | Case of case
  | Class_expr of class_expr
  | Class_structure of class_structure
  | Class_field of class_field
  | Class_field_kind of class_field_kind
  | Module_expr of module_expr
  | Structure of structure
  | Signature of signature
  | Structure_item of structure_item
  | Signature_item of signature_item
  | Module_binding of module_binding
  | Value_binding of value_binding
  | Module_type of module_type
  | Module_declaration of module_declaration
  | Module_type_declaration of module_type_declaration
  | With_constraint of with_constraint
  | Core_type of core_type
  | Package_type of package_type
  | Row_field of row_field
  | Value_description of value_description
  | Type_declaration of type_declaration
  | Type_extension of type_extension
  | Extension_constructor of extension_constructor
  | Label_declaration of label_declaration
  | Constructor_declaration of constructor_declaration
  | Class_type of class_type
  | Class_signature of class_signature
  | Class_type_field of class_type_field
  | Class_declaration of class_declaration
  | Class_description of class_description
  | Class_type_declaration of class_type_declaration
  | Binding_op of binding_op
  | Include_description of include_description
  | Include_declaration of include_declaration
  | Open_description of open_description
  | Open_declaration of open_declaration
  | Method_call of expression * Asttypes.label * Location.t
  | Record_field of
      [ `Expression of expression | `Pattern of pattern ]
      * Longident.t Location.loc
  | Module_binding_name of module_binding
  | Module_declaration_name of module_declaration
  | Module_type_declaration_name of module_type_declaration
  | Class_declaration_name of class_declaration
  | Class_type_declaration_name of class_type_declaration
  | Class_description_name of class_description
  | Class_field_name of class_field
  | Exp_new_class_name of Longident.t Location.loc * Types.class_declaration
  | Extension of extension

[@@@ocaml.warning "-9"]

let node_real_loc loc0 = function
  | Expression { pexp_loc = loc }
  | Pattern { ppat_loc = loc }
  | Method_call (_, _, loc)
  | Record_field (_, { loc })
  | Class_expr { pcl_loc = loc }
  | Module_expr { pmod_loc = loc }
  | Structure_item { pstr_loc = loc }
  | Signature_item { psig_loc = loc }
  | Module_type { pmty_loc = loc }
  | Core_type { ptyp_loc = loc }
  | Package_type { ppt_loc = loc }
  | Row_field { prf_loc = loc }
  | Class_type { pcty_loc = loc }
  | Class_field { pcf_loc = loc }
  | Module_binding { pmb_loc = loc }
  | Module_declaration { pmd_loc = loc }
  | Module_type_declaration { pmtd_loc = loc }
  | Value_description { pval_loc = loc }
  | Value_binding { pvb_loc = loc }
  | Type_declaration { ptype_loc = loc }
  | Type_extension { ptyext_loc = loc }
  | Label_declaration { pld_loc = loc }
  | Constructor_declaration { pcd_loc = loc }
  | Class_type_field { pctf_loc = loc }
  | Class_declaration { pci_loc = loc }
  | Class_description { pci_loc = loc }
  | Class_type_declaration { pci_loc = loc }
  | Class_declaration_name { pci_name = { loc } }
  | Class_type_declaration_name { pci_name = { loc } }
  | Class_description_name { pci_name = { loc } }
  | Class_field_name
      { pcf_desc = Pcf_val ({ loc }, _, _) | Pcf_method ({ loc }, _, _) }
  | Exp_new_class_name ({ loc }, _)
  | Extension_constructor { pext_loc = loc }
  | Include_description { pincl_loc = loc }
  | Include_declaration { pincl_loc = loc }
  | Open_description { popen_loc = loc }
  | Open_declaration { popen_loc = loc }
  | Binding_op { pbop_loc = loc } -> loc
  | Module_type_declaration_name { pmtd_name = { loc } } -> loc
  | Module_declaration_name { pmd_name = { loc } }
  | Extension ({ loc; _ }, _)
  | Module_binding_name { pmb_name = { loc } } -> loc
  | Structure _
  | Signature _
  | Case _
  | Class_structure _
  | Class_signature _
  | Class_field_kind _
  | With_constraint _
  | Class_field_name _
  | Dummy -> loc0

let node_attributes = function
  | Expression exp -> exp.pexp_attributes
  | Pattern pat -> pat.ppat_attributes
  | Class_expr cl -> cl.pcl_attributes
  | Class_field cf -> cf.pcf_attributes
  | Module_expr me -> me.pmod_attributes
  | Structure_item { pstr_desc = Pstr_eval (_, attr); _ } -> attr
  | Structure_item { pstr_desc = Pstr_attribute a; _ } -> [ a ]
  | Signature_item { psig_desc = Psig_attribute a; _ } -> [ a ]
  | Module_binding mb -> mb.pmb_attributes
  | Value_binding vb -> vb.pvb_attributes
  | Module_type mt -> mt.pmty_attributes
  | Module_declaration md -> md.pmd_attributes
  | Module_type_declaration mtd -> mtd.pmtd_attributes
  | Open_description o -> o.popen_attributes
  | Include_declaration i -> i.pincl_attributes
  | Include_description i -> i.pincl_attributes
  | Core_type ct -> ct.ptyp_attributes
  | Row_field rf -> rf.prf_attributes
  | Value_description vd -> vd.pval_attributes
  | Type_declaration td -> td.ptype_attributes
  | Label_declaration ld -> ld.pld_attributes
  | Constructor_declaration cd -> cd.pcd_attributes
  | Type_extension te -> te.ptyext_attributes
  | Extension_constructor ec -> ec.pext_attributes
  | Class_type ct -> ct.pcty_attributes
  | Class_type_field ctf -> ctf.pctf_attributes
  | Class_declaration ci -> ci.pci_attributes
  | Class_description ci -> ci.pci_attributes
  | Class_type_declaration ci -> ci.pci_attributes
  | Method_call (obj, _, _) -> obj.pexp_attributes
  | Record_field (`Expression obj, _) -> obj.pexp_attributes
  | Record_field (`Pattern obj, _) -> obj.ppat_attributes
  | _ -> []

let has_attr ~name node =
  let attrs = node_attributes node in
  List.exists
    ~f:(fun a ->
      let str, _ = Ast_helper.Attr.as_tuple a in
      str.Location.txt = name)
    attrs

let node_merlin_loc loc0 node =
  let attributes = node_attributes node in
  let relaxed_loc loc attributes =
    let open Parsetree in
    let pred { attr_name = loc; _ } = Location_aux.is_relaxed_location loc in
    match List.find attributes ~f:pred with
    | { attr_name; _ } -> attr_name.Location.loc
    | exception Not_found -> loc
  in
  let loc = relaxed_loc (node_real_loc loc0 node) attributes in
  let extra_loc loc extra =
    List.fold_left ~f:Location_aux.union ~init:loc extra
  in
  match node with
  | Expression { pexp_loc_stack; _ } -> extra_loc loc pexp_loc_stack
  | Pattern { ppat_loc_stack; _ } -> extra_loc loc ppat_loc_stack
  | _ -> loc

let app node f acc = f node acc

type 'a updater = node -> 'a -> 'a
type 'acc folder = 'acc updater -> 'acc -> 'acc
type ('foldable, 'acc) folder_generator = 'foldable -> 'acc folder

let id_fold (_f : _ updater) acc = acc

let ( ** ) f1 f2 (f : _ updater) acc = f2 f (f1 f acc)

let rec list_fold (f' : _ folder_generator) xs f acc =
  match xs with
  | x :: xs -> list_fold f' xs f (f' x f acc)
  | [] -> acc

let of_core_type : (core_type, 'a) folder_generator =
 fun ct -> app (Core_type ct)

let of_expression e = app (Expression e)

let of_pattern (p : pattern) = app (Pattern p)

let of_case c = app (Case c)
let of_label_declaration ct = app (Label_declaration ct)
let of_value_binding vb = app (Value_binding vb)
let of_module_type mt = app (Module_type mt)
let of_module_expr me = app (Module_expr me)
let of_typ_param (ct, _) = of_core_type ct
let of_constructor_arguments = function
  | Cstr_tuple cts -> list_fold of_core_type cts
  | Cstr_record lbls -> list_fold of_label_declaration lbls

(* TODO: this probably should be changed because the loc of Binding_op has
   changed compared to the typedtree version (or we should be more faithful to
   the typedtree version) *)
let of_bop ({ pbop_exp; _ } as bop) =
  app (Binding_op bop) ** of_expression pbop_exp

let of_record_field obj loc (f : _ updater) acc =
  app (Record_field (obj, loc)) f acc

let of_exp_record_field obj lid_loc lbl =
  of_record_field (`Expression obj) lid_loc lbl

let of_package_type pt = app (Package_type pt)

let of_extension e = app (Extension e)

let of_pat_record_field obj loc lbl = of_record_field (`Pattern obj) loc lbl

let of_pattern_desc (desc : pattern_desc) =
  match desc with
  | Ppat_construct (_, None)
  | Ppat_any | Ppat_var _ | Ppat_constant _
  | Ppat_interval (_, _)
  | Ppat_unpack (_, None)
  | Ppat_type _
  | Ppat_variant (_, None) -> id_fold
  | Ppat_alias (p, _)
  | Ppat_variant (_, Some p)
  | Ppat_lazy p
  | Ppat_construct (_, Some (_, p))
  | Ppat_exception p -> of_pattern p
  | Ppat_tuple (ps, _) ->
    list_fold of_pattern (List.map ~f:snd ps) (* todo handle labels *)
  | Ppat_array ps -> list_fold of_pattern ps
  | Ppat_record (ls, _) ->
    list_fold
      (fun (lid, p) -> of_record_field (`Pattern p) lid ** of_pattern p)
      ls
  | Ppat_or (p1, p2) -> of_pattern p1 ** of_pattern p2
  | Ppat_constraint (pat, t) -> of_pattern pat ** of_core_type t
  | Ppat_unpack (_, Some pt) -> of_package_type pt
  | Ppat_effect (p1, p2) -> of_pattern p1 ** of_pattern p2
  | Ppat_extension e -> of_extension e
  | Ppat_open (_, p) -> of_pattern p

let rec of_expression_desc loc = function
  | Pexp_ident _ | Pexp_constant _ | Pexp_variant (_, None) -> id_fold
  | Pexp_extension ({ txt }, PStr []) when String.equal txt Ast_helper.hole_txt
    -> id_fold
  | Pexp_new (_, lid, decl) -> app (Exp_new_class_name (lid, decl))
  | Pexp_let (_, vbs, e) -> of_expression e ** list_fold of_value_binding vbs
  | Pexp_function (params, body) ->
    list_fold of_function_param params ** of_function_body body
  | Pexp_apply (e, ls) ->
    of_expression e
    ** list_fold
         (function
           | _, Omitted () -> id_fold
           | _, Arg e -> of_expression e)
         ls
  | Pexp_match (e, cs, vs, _) ->
    of_expression e ** list_fold of_case cs ** list_fold of_case vs
  | Pexp_try (e, cs, _) -> of_expression e ** list_fold of_case cs
  | Pexp_tuple es ->
    list_fold of_expression (List.map ~f:snd es) (* todo labels ? *)
  | Pexp_construct (_, _, es) | Pexp_array (_, es) -> list_fold of_expression es
  | Pexp_variant (_, Some e)
  | Pexp_assert (e, _)
  | Pexp_lazy e
  | Pexp_setinstvar (_, _, _, e) -> of_expression e
  | Pexp_record { fields; extended_expression } ->
    option_fold of_expression extended_expression
    **
    let fold_field = function
      | _, Typedtree.Kept _ -> id_fold
      | desc, Typedtree.Overridden (lid_loc, e) ->
        of_exp_record_field e lid_loc desc ** of_expression e
    in
    array_fold fold_field fields
  | Pexp_atomic_loc (e, _, _) -> of_expression e
  | Pexp_field (e, lid_loc, lbl) ->
    of_expression e ** of_exp_record_field e lid_loc lbl
  | Pexp_setfield (e1, lid_loc, lbl, e2) ->
    of_expression e1 ** of_expression e2 ** of_exp_record_field e1 lid_loc lbl
  | Pexp_ifthenelse (e1, e2, None) | Pexp_sequence (e1, e2) | Pexp_while (e1, e2)
    -> of_expression e1 ** of_expression e2
  | Pexp_ifthenelse (e1, e2, Some e3) | Pexp_for (_, _, e1, e2, _, e3) ->
    of_expression e1 ** of_expression e2 ** of_expression e3
  | Pexp_send (e, meth) ->
    of_expression e ** of_method_call e meth loc (* TODO ulysse CHECK*)
  | Pexp_override (_, ls) -> list_fold (fun (_, _, e) -> of_expression e) ls
  | Pexp_object (cs, _) -> app (Class_structure cs)
  | Pexp_pack me -> of_module_expr me
  | Pexp_unreachable | Pexp_extension_constructor _ -> id_fold
  | Pexp_letop { let_; ands; body; _ } ->
    (* let+ ..pat1 and pat2 and ... are represented as pattern couples:
       [pat1; [pat2; ...]]. The following function flattens these couples.
       Keeping track of the known size of the tuple prevent wrongly flattening
       the patterns patN when they are tuples themselves. *)
    let rec flatten_patterns ~size acc pat =
      match pat.pat_desc with
      | Ppat_tuple [ (_, tuple); (_, pat) ] when size > 0 ->
        (* todo labeled tuples ? *)
        flatten_patterns ~size:(size - 1) (pat :: acc) tuple
      | _ -> List.rev (pat :: acc)
    in
    let bindops = let_ :: ands in
    let patterns = flatten_patterns ~size:(List.length ands) [] body.c_lhs in
    let of_letop (pat, bindop) = of_bop bindop ** of_pattern pat in
    list_fold of_letop (List.combine patterns bindops)
    ** of_expression body.c_rhs
  | Pexp_struct_item ({ str_desc }, e) ->
    of_structure_item_desc str_desc ** of_expression e

let of_node : (node, 'a) folder_generator = function
  | Dummy -> id_fold
  | Pattern { ppat_desc; _ } -> of_pattern_desc ppat_desc
  | Expression { pexp_desc; _ } -> of_expression_desc pexp_desc
  | Case { c_lhs; c_cont = Some (id, vd); c_guard; c_rhs } ->
    let name = Ident.name id in
    let cont_pat =
      { pat_desc = Tpat_var (id, { txt = name; loc = vd.val_loc }, vd.val_uid);
        pat_loc = vd.val_loc;
        pat_extra = [];
        pat_type = vd.val_type;
        pat_env = c_rhs.exp_env;
        pat_attributes = []
      }
    in
    of_pattern c_lhs ** of_expression c_rhs ** of_pattern cont_pat
    ** option_fold of_expression c_guard
  | Case { c_lhs; c_cont = None; c_guard; c_rhs } ->
    of_pattern c_lhs ** of_expression c_rhs ** option_fold of_expression c_guard
  | Class_expr { cl_desc } -> of_class_expr_desc cl_desc
  | Class_structure { cstr_self; cstr_fields } ->
    of_pattern cstr_self ** list_fold (fun f -> app (Class_field f)) cstr_fields
  | Class_field ({ cf_desc } as cf) ->
    of_class_field_desc cf_desc ** app (Class_field_name cf)
  | Class_field_kind (Tcfk_virtual ct) -> of_core_type ct
  | Class_field_kind (Tcfk_concrete (_, e)) -> of_expression e
  | Module_expr { mod_desc } -> of_module_expr_desc mod_desc
  | Module_type_constraint Tmodtype_implicit -> id_fold
  | Module_type_constraint (Tmodtype_explicit mt) -> of_module_type mt
  | Structure { str_items; str_final_env } ->
    list_fold_with_next
      (fun next item ->
        match next with
        | None -> app (Structure_item (item, str_final_env))
        | Some item' -> app (Structure_item (item, item'.str_env)))
      str_items
  | Structure_item ({ str_desc }, _) -> of_structure_item_desc str_desc
  | Module_binding mb ->
    app (Module_expr mb.mb_expr) ** app (Module_binding_name mb)
  | Value_binding { vb_pat; vb_expr } ->
    of_pattern vb_pat ** of_expression vb_expr
  | Module_type { mty_desc } -> of_module_type_desc mty_desc
  | Signature { sig_items; sig_final_env } ->
    list_fold_with_next
      (fun next item ->
        match next with
        | None -> app (Signature_item (item, sig_final_env))
        | Some item' -> app (Signature_item (item, item'.sig_env)))
      sig_items
  | Signature_item ({ sig_desc; sig_env }, _) ->
    of_signature_item_desc sig_env sig_desc
  | Module_declaration md ->
    of_module_type md.md_type ** app (Module_declaration_name md)
  | Module_type_declaration mtd ->
    option_fold of_module_type mtd.mtd_type
    ** app (Module_type_declaration_name mtd)
  | With_constraint (Twith_type td | Twith_typesubst td) ->
    app (Type_declaration td)
  | With_constraint (Twith_module _ | Twith_modsubst _) -> id_fold
  | With_constraint (Twith_modtype mt | Twith_modtypesubst mt) ->
    of_module_type mt
  | Core_type { ctyp_desc } -> of_core_type_desc ctyp_desc
  | Package_type { tpt_constraints } ->
    list_fold (fun (_, ct) -> of_core_type ct) tpt_constraints
  | Row_field rf ->
    begin match rf.rf_desc with
    | Ttag (_, _, cts) -> list_fold of_core_type cts
    | Tinherit ct -> of_core_type ct
    end
  | Value_description { val_desc } -> of_core_type val_desc
  | Type_declaration { typ_params; typ_constraints; typ_kind; typ_manifest } ->
    let of_typ_cstrs (ct1, ct2, _) = of_core_type ct1 ** of_core_type ct2 in
    option_fold of_core_type typ_manifest
    ** list_fold of_typ_param typ_params
    ** app (Type_kind typ_kind)
    ** list_fold of_typ_cstrs typ_constraints
  | Type_kind (Ttype_abstract | Ttype_open | Ttype_external _) -> id_fold
  | Type_kind (Ttype_variant cds) ->
    list_fold (fun cd -> app (Constructor_declaration cd)) cds
  | Type_kind (Ttype_record lds) -> list_fold of_label_declaration lds
  | Type_extension { tyext_params; tyext_constructors } ->
    list_fold of_typ_param tyext_params
    ** list_fold (fun ec -> app (Extension_constructor ec)) tyext_constructors
  | Extension_constructor { ext_kind = Text_decl (_, carg, cto) } ->
    option_fold of_core_type cto ** of_constructor_arguments carg
  | Extension_constructor { ext_kind = Text_rebind _ } -> id_fold
  | Label_declaration { ld_type } -> of_core_type ld_type
  | Constructor_declaration { cd_args; cd_res } ->
    option_fold of_core_type cd_res ** of_constructor_arguments cd_args
  | Class_type { cltyp_desc } -> of_class_type_desc cltyp_desc
  | Class_signature { csig_self; csig_fields } ->
    of_core_type csig_self
    ** list_fold (fun x -> app (Class_type_field x)) csig_fields
  | Class_type_field { ctf_desc } -> of_class_type_field_desc ctf_desc
  | Class_declaration ({ ci_params; ci_expr } as cd) ->
    app (Class_expr ci_expr)
    ** list_fold of_typ_param ci_params
    ** app (Class_declaration_name cd)
  | Class_description ({ ci_params; ci_expr } as cd) ->
    app (Class_type ci_expr)
    ** list_fold of_typ_param ci_params
    ** app (Class_description_name cd)
  | Class_type_declaration ({ ci_params; ci_expr } as ctd) ->
    app (Class_type ci_expr)
    ** list_fold of_typ_param ci_params
    ** app (Class_type_declaration_name ctd)
  | Method_call _ -> id_fold
  | Record_field _ -> id_fold
  | Module_binding_name _ -> id_fold
  | Module_declaration_name _ -> id_fold
  | Module_type_declaration_name _ -> id_fold
  | Class_declaration_name _ -> id_fold
  | Class_type_declaration_name _ -> id_fold
  | Class_description_name _ -> id_fold
  | Class_field_name _ -> id_fold
  | Exp_new_class_name _ -> id_fold
  | Open_description _ -> id_fold
  | Open_declaration od -> app (Module_expr od.open_expr)
  | Include_declaration i -> of_module_expr i.incl_mod
  | Include_description i -> of_module_type i.incl_mod
  | Binding_op { bop_exp = _ } -> id_fold

let fold_node f env node acc = of_node node env f acc
