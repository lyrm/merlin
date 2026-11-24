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
  | Type_kind of type_kind
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
  | Method_call of expression * string Location.loc
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
  | Exp_new_class_name of Longident.t Location.loc
  | Extension of extension
  | Constraint of expression * type_constraint

[@@@ocaml.warning "-9"]

let node_real_loc loc0 = function
  | Expression { pexp_loc = loc }
  | Pattern { ppat_loc = loc }
  | Method_call (_, { loc })
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
  | Exp_new_class_name { loc }
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
  | Constraint _
  | Type_kind _
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
  | Method_call (obj, _) -> obj.pexp_attributes
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

let option_fold (f : _ folder_generator) = function
  | Some x -> f x
  | None -> id_fold

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
  | Pcstr_tuple cts -> list_fold of_core_type cts
  | Pcstr_record lbls -> list_fold of_label_declaration lbls

(* TODO PEC: this probably should be changed because the loc of Binding_op has
   changed compared to the typedtree version (or we should be more faithful to
   the typedtree version) *)
let of_bop ({ pbop_exp; pbop_pat } as bop) =
  app (Binding_op bop) ** of_expression pbop_exp ** of_pattern pbop_pat

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

let rec of_function_param fp = of_function_param_kind fp.pparam_desc

and of_function_param_kind = function
  | Pparam_val (_, Some exp, pat) -> of_expression exp ** of_pattern pat
  | Pparam_val (_, None, pat) -> of_pattern pat
  | Pparam_newtype _ -> id_fold

and of_function_body = function
  | Pfunction_body exp -> of_expression exp
  | Pfunction_cases (fc, _, _) -> list_fold of_case fc

and of_method_call obj meth (f : _ updater) acc =
  app (Method_call (obj, meth)) f acc

and of_expression_desc = function
  | Pexp_ident _ | Pexp_constant _
  | Pexp_variant (_, None)
  | Pexp_construct (_, None) -> id_fold
  | Pexp_extension ({ txt }, PStr []) when String.equal txt Ast_helper.hole_txt
    -> id_fold (* TODO PEC: do we want a "hole" node? *)
  | Pexp_new lid -> app (Exp_new_class_name lid)
  | Pexp_let (_, vbs, e) -> of_expression e ** list_fold of_value_binding vbs
  | Pexp_function (params, _, body) ->
    (* TODO PEC: type constraints, what is it? *)
    list_fold of_function_param params ** of_function_body body
  | Pexp_apply (e, ls) ->
    of_expression e ** list_fold (fun (_, e) -> of_expression e) ls
  | Pexp_match (e, cs) -> of_expression e ** list_fold of_case cs
  | Pexp_try (e, cs) -> of_expression e ** list_fold of_case cs
  | Pexp_tuple es ->
    list_fold of_expression (List.map ~f:snd es) (* todo labels ? *)
  | Pexp_array es -> list_fold of_expression es
  | Pexp_variant (_, Some e)
  | Pexp_construct (_, Some e)
  | Pexp_assert e
  | Pexp_lazy e
  | Pexp_setinstvar (_, e) -> of_expression e
  | Pexp_record (fields, e) ->
    option_fold of_expression e
    ** list_fold
         (fun (lid_loc, e) -> of_exp_record_field e lid_loc ** of_expression e)
         fields
  | Pexp_field (e, lid_loc) -> of_expression e ** of_exp_record_field e lid_loc
  | Pexp_setfield (e1, lid_loc, e2) ->
    of_expression e1 ** of_expression e2 ** of_exp_record_field e1 lid_loc
  | Pexp_ifthenelse (e1, e2, None) | Pexp_sequence (e1, e2) | Pexp_while (e1, e2)
    -> of_expression e1 ** of_expression e2
  | Pexp_ifthenelse (e1, e2, Some e3) ->
    of_expression e1 ** of_expression e2 ** of_expression e3
  | Pexp_for (p, e1, e2, _, e3) ->
    of_pattern p ** of_expression e1 ** of_expression e2 ** of_expression e3
  | Pexp_send (e, meth) ->
    of_expression e ** of_method_call e meth (* TODO ulysse CHECK*)
  | Pexp_override ls -> list_fold (fun (_, e) -> of_expression e) ls
  | Pexp_object cs -> app (Class_structure cs)
  | Pexp_pack (me, _) ->
    (* TODO PEC what about the second argument package_type ?*)
    of_module_expr me
  | Pexp_unreachable -> id_fold
  | Pexp_letop { let_; ands; body; _ } ->
    let bindops = let_ :: ands in
    list_fold of_bop bindops ** of_expression body
  | Pexp_struct_item ({ pstr_desc }, e) ->
    of_structure_item_desc pstr_desc ** of_expression e
  | Pexp_extension ext -> app (Extension ext)
  | Pexp_constraint (e, ct) -> app (Constraint (e, Pconstraint ct))
  | Pexp_poly (e, ctopt) -> of_expression e ** option_fold of_core_type ctopt
  | Pexp_coerce (e, ctopt, ct) -> app (Constraint (e, Pcoerce (ctopt, ct)))
  | Pexp_newtype (_, e) -> of_expression e

and of_structure_item_desc = function
  | Pstr_eval (e, _) -> of_expression e
  | Pstr_value (_, vbs) -> list_fold of_value_binding vbs
  | Pstr_primitive vd -> app (Value_description vd)
  | Pstr_type (_, tds) -> list_fold (fun td -> app (Type_declaration td)) tds
  | Pstr_typext text -> app (Type_extension text)
  | Pstr_exception texn -> app (Extension_constructor texn.ptyexn_constructor)
  | Pstr_module mb -> app (Module_binding mb)
  | Pstr_recmodule mbs -> list_fold (fun x -> app (Module_binding x)) mbs
  | Pstr_modtype mtd -> app (Module_type_declaration mtd)
  | Pstr_class cds -> list_fold (fun cd -> app (Class_declaration cd)) cds
  | Pstr_class_type ctds ->
    list_fold (fun ctd -> app (Class_type_declaration ctd)) ctds
  | Pstr_include i -> app (Include_declaration i)
  | Pstr_open d -> app (Open_declaration d)
  | Pstr_attribute _ -> id_fold
  | Pstr_extension (ext, _) -> app (Extension ext)

and of_class_expr_desc = function
  | Pcl_structure cs -> app (Class_structure cs)
  | Pcl_fun (_, eopt, p, ce) ->
    option_fold of_expression eopt ** of_pattern p ** app (Class_expr ce)
  | Pcl_apply (ce, es) ->
    list_fold (fun (_, e) -> of_expression e) es ** app (Class_expr ce)
  | Pcl_let (_, vbs, ce) ->
    list_fold of_value_binding vbs ** app (Class_expr ce)
  | Pcl_constraint (ce, ct) -> app (Class_type ct) ** app (Class_expr ce)
  | Pcl_open (_, ce) -> app (Class_expr ce)
  | Pcl_extension ext -> app (Extension ext)
  | Pcl_constr (_, cts) -> list_fold (fun ct -> app (Core_type ct)) cts

and of_class_field_desc = function
  | Pcf_inherit (_, ce, _) -> app (Class_expr ce)
  | Pcf_val (_, _, cfk) | Pcf_method (_, _, cfk) -> app (Class_field_kind cfk)
  | Pcf_constraint (ct1, ct2) -> of_core_type ct1 ** of_core_type ct2
  | Pcf_initializer e -> of_expression e
  | Pcf_extension ext -> app (Extension ext)
  | Pcf_attribute _ -> id_fold (*TODO*)

and of_module_expr_desc = function
  | Pmod_ident _ -> id_fold
  | Pmod_structure str -> app (Structure str)
  | Pmod_functor (Unit, me) -> of_module_expr me
  | Pmod_functor (Named (_, mt), me) -> of_module_type mt ** of_module_expr me
  | Pmod_apply (me1, me2) -> of_module_expr me1 ** of_module_expr me2
  | Pmod_apply_unit me1 -> of_module_expr me1
  | Pmod_constraint (me, mt) -> of_module_expr me ** app (Module_type mt)
  | Pmod_unpack e -> of_expression e
  | Pmod_extension ext -> app (Extension ext)

and of_signature_item_desc = function
  | Psig_attribute _ -> id_fold
  | Psig_open d -> app (Open_description d)
  | Psig_value vd -> app (Value_description vd)
  | Psig_type (_, tds) -> list_fold (fun td -> app (Type_declaration td)) tds
  | Psig_typext text -> app (Type_extension text)
  | Psig_exception texn -> app (Extension_constructor texn.ptyexn_constructor)
  | Psig_module md -> app (Module_declaration md)
  | Psig_recmodule mds -> list_fold (fun md -> app (Module_declaration md)) mds
  | Psig_modtype mtd -> app (Module_type_declaration mtd)
  | Psig_include i -> app (Include_description i)
  | Psig_class cds -> list_fold (fun cd -> app (Class_description cd)) cds
  | Psig_class_type ctds ->
    list_fold (fun ctd -> app (Class_type_declaration ctd)) ctds
  | Psig_typesubst tds ->
    (* FIXME: shitty approximation *)
    list_fold (fun td -> app (Type_declaration td)) tds
  | Psig_extension (ext, _attr) -> app (Extension ext)
  | Psig_modsubst _ms ->
    (* TODO. *)
    id_fold
  | Psig_modtypesubst _mts ->
    (* TODO. *)
    id_fold

and of_module_type_desc = function
  | Pmty_ident _ | Pmty_alias _ -> id_fold
  | Pmty_signature sg -> app (Signature sg)
  | Pmty_functor (Named (_, mt1), mt2) ->
    of_module_type mt1 ** of_module_type mt2
  | Pmty_functor (Unit, mt) -> of_module_type mt
  | Pmty_with (mt, wcs) ->
    list_fold (fun wc -> app (With_constraint wc)) wcs ** of_module_type mt
  | Pmty_typeof me -> of_module_expr me
  | Pmty_extension ext -> app (Extension ext)

and of_core_type_desc = function
  | Ptyp_any | Ptyp_var _ -> id_fold
  | Ptyp_open (_, ct) -> of_core_type ct
  | Ptyp_arrow (_, ct1, ct2) -> of_core_type ct1 ** of_core_type ct2
  | Ptyp_functor (_, _, _, ct) -> of_core_type ct (* todo *)
  | Ptyp_tuple cts ->
    list_fold of_core_type (List.map ~f:snd cts) (* todo labels *)
  | Ptyp_constr (_, cts) | Ptyp_class (_, cts) -> list_fold of_core_type cts
  | Ptyp_object (cts, _) ->
    list_fold
      (fun of_ ->
        match of_.pof_desc with
        | Otag (_, ct) | Oinherit ct -> of_core_type ct)
      cts
  | Ptyp_poly (_, ct) | Ptyp_alias (ct, _) -> of_core_type ct
  | Ptyp_variant (rfs, _, _) -> list_fold (fun rf -> app (Row_field rf)) rfs
  | Ptyp_package pt -> app (Package_type pt)
  | Ptyp_extension ext -> app (Extension ext)

and of_class_type_desc = function
  | Pcty_constr (_, cts) -> list_fold of_core_type cts
  | Pcty_signature cs -> app (Class_signature cs)
  | Pcty_arrow (_, ct, clt) -> of_core_type ct ** app (Class_type clt)
  | Pcty_open (_, ct) -> app (Class_type ct)
  | Pcty_extension ext -> app (Extension ext)

and of_class_type_field_desc = function
  | Pctf_inherit ct -> app (Class_type ct)
  | Pctf_val (_, _, _, ct) | Pctf_method (_, _, _, ct) -> of_core_type ct
  | Pctf_constraint (ct1, ct2) -> of_core_type ct1 ** of_core_type ct2
  | Pctf_attribute _ -> id_fold
  | Pctf_extension ext -> app (Extension ext)

let of_node : (node, 'a) folder_generator = function
  | Dummy -> id_fold
  | Pattern { ppat_desc; _ } -> of_pattern_desc ppat_desc
  | Expression { pexp_desc; _ } -> of_expression_desc pexp_desc
  | Case { pc_lhs; pc_guard; pc_rhs } ->
    of_pattern pc_lhs ** of_expression pc_rhs
    ** option_fold of_expression pc_guard
  | Class_expr { pcl_desc; _ } -> of_class_expr_desc pcl_desc
  | Class_structure { pcstr_self; pcstr_fields } ->
    of_pattern pcstr_self
    ** list_fold (fun f -> app (Class_field f)) pcstr_fields
  | Class_field ({ pcf_desc } as cf) ->
    of_class_field_desc pcf_desc ** app (Class_field_name cf)
  | Class_field_kind (Cfk_virtual ct) -> of_core_type ct
  | Class_field_kind (Cfk_concrete (_, e)) -> of_expression e
  | Module_expr { pmod_desc } -> of_module_expr_desc pmod_desc
  | Module_type { pmty_desc } -> of_module_type_desc pmty_desc
  | Structure strs -> list_fold (fun str -> app (Structure_item str)) strs
  | Structure_item { pstr_desc } -> of_structure_item_desc pstr_desc
  | Module_binding mb ->
    app (Module_expr mb.pmb_expr) ** app (Module_binding_name mb)
  | Value_binding { pvb_pat; pvb_expr } ->
    of_pattern pvb_pat ** of_expression pvb_expr
  | Signature sigs -> list_fold (fun item -> app (Signature_item item)) sigs
  | Signature_item { psig_desc } -> of_signature_item_desc psig_desc
  | Module_declaration md ->
    of_module_type md.pmd_type ** app (Module_declaration_name md)
  | Module_type_declaration mtd ->
    option_fold of_module_type mtd.pmtd_type
    ** app (Module_type_declaration_name mtd)
  | With_constraint (Pwith_type (_, td) | Pwith_typesubst (_, td)) ->
    app (Type_declaration td)
  | With_constraint (Pwith_module _ | Pwith_modsubst _) -> id_fold
  | With_constraint (Pwith_modtype (_, mt) | Pwith_modtypesubst (_, mt)) ->
    of_module_type mt
  | Core_type { ptyp_desc } -> of_core_type_desc ptyp_desc
  | Package_type { ppt_constraints } ->
    list_fold (fun (_, ct) -> of_core_type ct) ppt_constraints
  | Row_field rf ->
    begin match rf.prf_desc with
    | Rtag (_, _, cts) -> list_fold of_core_type cts
    | Rinherit ct -> of_core_type ct
    end
  | Value_description { pval_type } -> of_core_type pval_type
  | Type_declaration
      { ptype_params; ptype_constraints; ptype_kind; ptype_manifest } ->
    let of_typ_cstrs (ct1, ct2, _) = of_core_type ct1 ** of_core_type ct2 in
    option_fold of_core_type ptype_manifest
    ** list_fold of_typ_param ptype_params
    ** app (Type_kind ptype_kind)
    ** list_fold of_typ_cstrs ptype_constraints
  | Type_kind (Ptype_abstract | Ptype_open | Ptype_external _) -> id_fold
  | Type_kind (Ptype_variant cds) ->
    list_fold (fun cd -> app (Constructor_declaration cd)) cds
  | Type_kind (Ptype_record lds) -> list_fold of_label_declaration lds
  | Type_extension { ptyext_params; ptyext_constructors } ->
    list_fold of_typ_param ptyext_params
    ** list_fold (fun ec -> app (Extension_constructor ec)) ptyext_constructors
  | Extension_constructor { pext_kind = Pext_decl (_, carg, cto) } ->
    option_fold of_core_type cto ** of_constructor_arguments carg
  | Extension_constructor { pext_kind = Pext_rebind _ } -> id_fold
  | Label_declaration { pld_type } -> of_core_type pld_type
  | Constructor_declaration { pcd_args; pcd_res } ->
    option_fold of_core_type pcd_res ** of_constructor_arguments pcd_args
  | Class_type { pcty_desc } -> of_class_type_desc pcty_desc
  | Class_signature { pcsig_self; pcsig_fields } ->
    of_core_type pcsig_self
    ** list_fold (fun x -> app (Class_type_field x)) pcsig_fields
  | Class_type_field { pctf_desc } -> of_class_type_field_desc pctf_desc
  | Class_declaration ({ pci_params; pci_expr } as cd) ->
    app (Class_expr pci_expr)
    ** list_fold of_typ_param pci_params
    ** app (Class_declaration_name cd)
  | Class_description ({ pci_params; pci_expr } as cd) ->
    app (Class_type pci_expr)
    ** list_fold of_typ_param pci_params
    ** app (Class_description_name cd)
  | Class_type_declaration ({ pci_params; pci_expr } as ctd) ->
    app (Class_type pci_expr)
    ** list_fold of_typ_param pci_params
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
  | Open_declaration od -> app (Module_expr od.popen_expr)
  | Include_declaration i -> of_module_expr i.pincl_mod
  | Include_description i -> of_module_type i.pincl_mod
  | Binding_op _ -> id_fold
  | Extension (_, PStr str) -> app (Structure str)
  | Extension (_, PSig sg) -> app (Signature sg)
  | Extension (_, PTyp ct) -> of_core_type ct
  | Extension (_, PPat (pat, exp_opt)) ->
    of_pattern pat ** option_fold of_expression exp_opt
  | Constraint (e, Pconstraint ct) -> of_expression e ** of_core_type ct
  | Constraint (e, Pcoerce (ctopt, ct)) ->
    of_expression e ** option_fold of_core_type ctopt ** of_core_type ct

let fold_node f env node acc = of_node node env f acc
