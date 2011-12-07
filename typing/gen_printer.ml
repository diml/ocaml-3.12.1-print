(*
 * gen_printer.ml
 * --------------
 * Copyright : (c) 2011, Jeremie Dimino <jeremie@dimino.org>
 * Licence   : BSD3
 *)

open Primitive
open Asttypes
open Parsetree
open Typedtree
open Types
open Predef

module MakeGen(Loc : sig val loc : Location.t end) = struct
  open Loc

  let exp_string str =
    { pexp_desc = Pexp_constant (Const_string str);
      pexp_loc = loc }

  let exp_fun pat exp =
    { pexp_desc = Pexp_function ("", None, [(pat, exp)]);
      pexp_loc = loc }

  let exp_function l =
    { pexp_desc = Pexp_function ("", None, l);
      pexp_loc = loc }

  let exp_apply exp args =
    { pexp_desc = Pexp_apply (exp, List.map (fun arg -> ("", arg)) args);
      pexp_loc = loc }

  let exp_tuple = function
    | [x] ->
        x
    | l ->
        { pexp_desc = Pexp_tuple l;
          pexp_loc = loc }

  let longident_of_list = function
    | [] -> assert false
    | x :: l -> List.fold_left (fun acc x -> Longident.Ldot (acc, x)) (Longident.Lident x) l

  let exp_ident id =
    { pexp_desc = Pexp_ident (longident_of_list id);
      pexp_loc = loc }

  let exp_var name =
    { pexp_desc = Pexp_ident (Longident.Lident name);
      pexp_loc = loc }

  let exp_append a b =
    exp_apply
      (exp_ident ["Pervasives"; "^"])
      [a; b]

  let rec exp_concat sep = function
    | [] -> exp_string ""
    | [x] -> x
    | x :: l -> exp_append x (exp_append (exp_string sep) (exp_concat sep l))

  let exp_enclose sep b e l =
    exp_append (exp_string b) (exp_append (exp_concat sep l) (exp_string e))

  let exp_field e id =
    { pexp_desc = Pexp_field (e, longident_of_list id);
      pexp_loc = loc }

  let pat_any =
    { ppat_desc = Ppat_any;
      ppat_loc = loc }

  let pat_construct id args =
    { ppat_desc = Ppat_construct (longident_of_list id, args, false);
      ppat_loc = loc }

  let pat_var name =
    { ppat_desc = Ppat_var name;
      ppat_loc = loc }

  let pat_tuple = function
    | [x] ->
        x
    | l ->
        { ppat_desc = Ppat_tuple l;
          ppat_loc = loc }

  let gen_vars l =
    let rec map i l =
      match l with
        | [] -> []
        | _ :: l -> ("$" ^ string_of_int i) :: map (i + 1) l
    in
    map 0 l

  let rec gen env typ =
    match typ.desc with
      | Tvar ->
          exp_fun pat_any (exp_string "<poly>")
      | Tarrow _ ->
          exp_fun pat_any (exp_string "<fun>")
      | Ttuple l ->
          let vars = gen_vars l in
          exp_fun
            (pat_tuple (List.map pat_var vars))
            (exp_enclose
               ", " "(" ")"
               (List.map2 (fun var typ -> exp_apply (gen env typ) [exp_var var]) vars l))
      | Tconstr (path, _, _) ->
          if path = path_int then
            exp_fun (pat_var "$") (exp_apply (exp_ident ["Pervasives"; "string_of_int"]) [exp_var "$"])
          else if path = path_string then
            exp_fun
              (pat_var "$")
              (exp_append
                 (exp_string "\"")
                 (exp_append
                    (exp_apply (exp_ident ["String"; "escaped"]) [exp_var "$"])
                    (exp_string "\"")))
          else begin
            match try Some (Env.find_type path env) with Not_found -> None with
              | None ->
                  exp_fun pat_any (exp_string "<abstract>")
              | Some { type_kind = Type_variant l } ->
                  exp_function
                    (List.map
                       (function
                          | (name, []) ->
                              (pat_construct [name] None,
                               exp_string name)
                          | (name, args) ->
                              let vars = gen_vars args in
                              (pat_construct [name] (Some (pat_tuple (List.map pat_var vars))),
                               exp_append
                                 (exp_string (name ^ " "))
                                 (exp_enclose
                                    ", " "(" ")"
                                    (List.map2 (fun var typ -> exp_apply (gen env typ) [exp_var var]) vars args))))
                       l)
              | Some { type_kind = Type_record (l, _) } ->
                  exp_fun
                    (pat_var "$")
                    (exp_enclose
                       "; " "{ " " }"
                       (List.map
                          (fun (name, _, typ) ->
                             exp_append
                               (exp_string (name ^ " = "))
                               (exp_apply (gen env typ) [exp_field (exp_var "$") [name]]))
                          l))
              | Some { type_kind = Type_abstract; type_manifest = None } ->
                  exp_fun pat_any (exp_string "<abstract>")
              | Some { type_kind = Type_abstract; type_manifest = Some typ } ->
                  gen env typ
          end
      | Tobject _ ->
          exp_fun pat_any (exp_string "<object>")
      | Tfield _ ->
          exp_fun pat_any (exp_string "<field>")
      | Tnil ->
          exp_fun pat_any (exp_string "<nil>")
      | Tlink typ ->
          gen env typ
      | Tsubst typ ->
          gen env typ
      | Tvariant _ ->
          exp_fun pat_any (exp_string "<variant>")
      | Tunivar ->
          exp_fun pat_any (exp_string "<poly>")
      | Tpoly _ ->
          exp_fun pat_any (exp_string "<poly>")
      | Tpackage _ ->
          exp_fun pat_any (exp_string "<module>")
end

let rec expanse_structure l =
  List.map expanse_structure_item l

and expanse_structure_item = function
  | Tstr_eval e ->
      Tstr_eval (expanse_expression e)
  | Tstr_value (f, l) ->
      Tstr_value (f, List.map (fun (p, e) -> (p, expanse_expression e)) l)
  | Tstr_module (id, me) ->
      Tstr_module (id, expanse_module_expr me)
  | Tstr_recmodule l ->
      Tstr_recmodule (List.map (fun (id, me) -> (id, expanse_module_expr me)) l)
  | Tstr_class l ->
      Tstr_class (List.map (fun (id, n, l, ce, v) -> (id, n, l, expanse_class_expr ce, v)) l)
  | Tstr_include (me, l) ->
      Tstr_include (expanse_module_expr me, l)
  | item ->
      item

and expanse_expression e =
  match e.exp_desc with
    | Texp_ident (_, { val_kind = Val_prim { prim_name = "%show" } }) -> begin
        let module Gen = MakeGen(struct let loc = e.exp_loc end) in
        match e.exp_type.desc with
          | Tarrow (_, typ, _, _) ->
(*              Printtyp.type_expr Format.std_formatter typ;
              Format.pp_print_newline Format.std_formatter ();
              Printast.implementation Format.std_formatter [{ pstr_desc = Pstr_eval (Gen.gen e.exp_env typ); pstr_loc = e.exp_loc }];
              Format.pp_print_newline Format.std_formatter ();*)
              Typecore.type_expression e.exp_env (Gen.gen e.exp_env typ)
          | _ ->
              failwith "invalid type for %show"
      end
    | _ ->
        { e with exp_desc = expanse_expression_desc e.exp_desc }

and expanse_expression_desc = function
  | Texp_let (f, l, e) ->
      Texp_let (f, List.map (fun (p, e) -> (p, expanse_expression e)) l, expanse_expression e)
  | Texp_function (l, p) ->
      Texp_function (List.map (fun (p, e) -> (p, expanse_expression e)) l, p)
  | Texp_apply (e, l) ->
      Texp_apply (expanse_expression e, List.map (function
                                                    | (Some e, o) -> (Some (expanse_expression e), o)
                                                    | (None, o) -> (None, o)) l)
  | Texp_match (e, l, p) ->
      Texp_match (expanse_expression e,
                  List.map (fun (p, e) -> (p, expanse_expression e)) l,
                  p)
  | Texp_try (e, l) ->
      Texp_try (expanse_expression e,
                List.map (fun (p, e) -> (p, expanse_expression e)) l)
  | Texp_tuple l ->
      Texp_tuple (List.map expanse_expression l)
  | Texp_construct (c, l) ->
      Texp_construct (c, List.map expanse_expression l)
  | Texp_variant (lbl, Some e) ->
      Texp_variant (lbl, Some (expanse_expression e))
  | Texp_record (l, o) ->
      Texp_record
        (List.map (fun (lbl, e) -> (lbl, expanse_expression e)) l,
         match o with
           | Some e -> Some (expanse_expression e)
           | None -> None)
  | Texp_field (e, lbl) ->
      Texp_field (expanse_expression e, lbl)
  | Texp_setfield (e, lbl, e') ->
      Texp_setfield (expanse_expression e, lbl, expanse_expression e')
  | Texp_array l ->
      Texp_array (List.map expanse_expression l)
  | Texp_ifthenelse (e, ethen, eelse) ->
      Texp_ifthenelse
        (expanse_expression e,
         expanse_expression ethen,
         match eelse with
           | Some e -> Some (expanse_expression e)
           | None -> None)
  | Texp_sequence (e1, e2) ->
      Texp_sequence (expanse_expression e1, expanse_expression e2)
  | Texp_while (e, e') ->
      Texp_while (expanse_expression e, expanse_expression e')
  | Texp_for (id, e, e', d, e'') ->
      Texp_for (id,
                expanse_expression e,
                expanse_expression e',
                d,
                expanse_expression e'')
  | Texp_when (e, e') ->
      Texp_when (expanse_expression e,
                 expanse_expression e')
  | Texp_send (e, m) ->
      Texp_send (expanse_expression e, m)
  | Texp_setinstvar (p, p', e) ->
      Texp_setinstvar (p, p', expanse_expression e)
  | Texp_override (p, l) ->
      Texp_override (p, List.map (fun (p, e) -> (p, expanse_expression e)) l)
  | Texp_letmodule (id, me, e) ->
      Texp_letmodule (id, expanse_module_expr me, expanse_expression e)
  | Texp_assert e ->
      Texp_assert (expanse_expression e)
  | Texp_lazy e ->
      Texp_lazy (expanse_expression e)
  | Texp_object (cstr, csig, l) ->
      Texp_object (expanse_class_structure cstr, csig, l)
  | Texp_pack me ->
      Texp_pack (expanse_module_expr me)
  | e ->
      e

and expanse_module_expr me =
  { me with mod_desc = expanse_module_expr_desc me.mod_desc }

and expanse_module_expr_desc = function
  | Tmod_ident id ->
      Tmod_ident id
  | Tmod_structure s ->
      Tmod_structure (expanse_structure s)
  | Tmod_functor (id, mt, me) ->
      Tmod_functor (id, mt, expanse_module_expr me)
  | Tmod_apply (me, me', mc) ->
      Tmod_apply (expanse_module_expr me,
                  expanse_module_expr me',
                  mc)
  | Tmod_constraint (me, mt, mc) ->
      Tmod_constraint (expanse_module_expr me, mt, mc)
  | Tmod_unpack (e, mt) ->
      Tmod_unpack (expanse_expression e, mt)

and expanse_class_structure c =
  { c with cl_field = List.map expanse_class_field c.cl_field }

and expanse_class_field = function
  | Cf_inher (ce, l, l') ->
      Cf_inher (expanse_class_expr ce, l, l')
  | Cf_val (n, id, Some e, b) ->
      Cf_val (n, id, Some (expanse_expression e), b)
  | Cf_val (n, id, None, b) ->
      Cf_val (n, id, None, b)
  | Cf_meth (n, e) ->
      Cf_meth (n, expanse_expression e)
  | Cf_let (f, l, l') ->
      Cf_let (f,
              List.map (fun (p, e) -> (p, expanse_expression e)) l,
              List.map (fun (i, e) -> (i, expanse_expression e)) l')
  | Cf_init e ->
      Cf_init (expanse_expression e)

and expanse_class_expr ce =
  { ce with cl_desc = expanse_class_expr_desc ce.cl_desc }

and expanse_class_expr_desc = function
  | Tclass_ident id ->
      Tclass_ident id
  | Tclass_structure cs ->
      Tclass_structure (expanse_class_structure cs)
  | Tclass_fun (pat, l, ce, par) ->
      Tclass_fun (pat,
                  List.map (fun (i, e) -> (i, expanse_expression e)) l,
                  expanse_class_expr ce,
                  par)
  | Tclass_apply (ce, l) ->
      Tclass_apply (expanse_class_expr ce,
                    List.map (function
                                | (Some e, o) -> (Some (expanse_expression e), o)
                                | (None, o) -> (None, o)) l)
  | Tclass_let (f, l, l', ce) ->
      Tclass_let (f,
                  List.map (fun (p, e) -> (p, expanse_expression e)) l,
                  List.map (fun (i, e) -> (i, expanse_expression e)) l',
                  expanse_class_expr ce)
  | Tclass_constraint (ce, l, l', c) ->
      Tclass_constraint (expanse_class_expr ce, l, l', c)

let expanse = expanse_structure
