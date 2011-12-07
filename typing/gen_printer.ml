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

type ('a, 'b) either =
  | Inl of 'a
  | Inr of 'b

module PathMap : sig
  type 'a t
  val empty : 'a t
  val add : Path.t -> 'a -> 'a t -> 'a t
  val find : Path.t -> 'a t -> ('a, int) either
end = struct
  type 'a t = (Path.t * 'a) list
  let empty = []
  let add p x l = (p, x) :: l
  let find p l =
    let rec aux n l =
      match l with
        | [] -> Inr n
        | (p', x) :: l -> if Path.same p p' then Inl x else aux (n + 1) l
    in
    aux 0 l
end

module IntSet = Set.Make(struct type t = int let compare a b = a - b end)

module MakeGen(Loc : sig val loc : Location.t end) = struct
  open Loc

  let exp_letrec l e =
    { pexp_desc = Pexp_let (Recursive, l, e);
      pexp_loc = loc }

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

  let exp_field e li =
    { pexp_desc = Pexp_field (e, li);
      pexp_loc = loc }

  let pat_any =
    { ppat_desc = Ppat_any;
      ppat_loc = loc }

  let pat_construct li args =
    { ppat_desc = Ppat_construct (li, args, false);
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

  let rec longident_of_path = function
    | Path.Pident id -> Longident.Lident (Ident.name id)
    | Path.Pdot (a, b, _) -> Longident.Ldot (longident_of_path a, b)
    | Path.Papply (a, b) -> Longident.Lapply (longident_of_path a, longident_of_path b)

  let rec replace_last li repl =
    match li with
      | Longident.Lident _ -> Longident.Lident repl
      | Longident.Ldot (li, _) -> Longident.Ldot (li, repl)
      | Longident.Lapply (li1, li2) -> Longident.Lapply (li1, replace_last li2 repl)

  let rec gen env printer_names printer_exprs params typ =
    match typ.desc with
      | Tvar ->
          (printer_names,
           printer_exprs,
           if IntSet.mem typ.id params then
             exp_var ("$p" ^ string_of_int typ.id)
           else
             exp_fun pat_any (exp_string "<poly>"))
      | Tarrow _ ->
          (printer_names,
           printer_exprs,
           exp_fun pat_any (exp_string "<fun>"))
      | Ttuple l ->
          let vars = gen_vars l in
          let printer_names, printer_exprs, printers = gen_printers env printer_names printer_exprs params l in
          (printer_names,
           printer_exprs,
           exp_fun
             (pat_tuple (List.map pat_var vars))
             (exp_enclose
                ", " "(" ")"
                (List.map2 (fun var printer -> exp_apply printer [exp_var var]) vars printers)))
      | Tconstr (path, args, _) -> begin
          match PathMap.find path printer_names with
            | Inl name ->
                let printer_names, printer_exprs, printers = gen_printers env printer_names printer_exprs params args in
                (printer_names,
                 printer_exprs,
                 exp_fun (pat_var "$") (exp_apply (exp_var name) (printers @ [exp_var "$"])))
            | Inr n ->
                let name = "$print" ^ string_of_int n in
                let printer_names = PathMap.add path name printer_names in
                let printer_names, printer_exprs, printer = gen_constr_printer env printer_names printer_exprs path in
                let printer_exprs = (name, printer) :: printer_exprs in
                let printer_names, printer_exprs, printers = gen_printers env printer_names printer_exprs params args in
                (printer_names,
                 printer_exprs,
                 exp_fun (pat_var "$") (exp_apply (exp_var name) (printers @ [exp_var "$"])))
        end
      | Tobject _ ->
          (printer_names,
           printer_exprs,
           exp_fun pat_any (exp_string "<object>"))
      | Tfield _ ->
          (printer_names,
           printer_exprs,
           exp_fun pat_any (exp_string "<field>"))
      | Tnil ->
          (printer_names,
           printer_exprs,
           exp_fun pat_any (exp_string "<nil>"))
      | Tlink typ ->
          gen env printer_names printer_exprs params typ
      | Tsubst typ ->
          gen env printer_names printer_exprs params typ
      | Tvariant _ ->
          (printer_names,
           printer_exprs,
           exp_fun pat_any (exp_string "<variant>"))
      | Tunivar ->
          (printer_names,
           printer_exprs,
           exp_fun pat_any (exp_string "<poly>"))
      | Tpoly _ ->
          (printer_names,
           printer_exprs,
           exp_fun pat_any (exp_string "<poly>"))
      | Tpackage _ ->
          (printer_names,
           printer_exprs,
           exp_fun pat_any (exp_string "<module>"))

  and gen_printers env printer_names printer_exprs params typs =
    match typs with
      | [] ->
          (printer_names, printer_exprs, [])
      | typ :: typs ->
          let printer_names, printer_exprs, p = gen env printer_names printer_exprs params typ in
          let printer_names, printer_exprs, l = gen_printers env printer_names printer_exprs params typs in
          (printer_names, printer_exprs, p :: l)

  and gen_constr_printer env printer_names printer_exprs path =
    if path = path_int then
      (printer_names,
       printer_exprs,
       exp_ident ["Pervasives"; "string_of_int"])
    else if path = path_string then
      (printer_names,
       printer_exprs,
       exp_fun
         (pat_var "$")
         (exp_append
            (exp_string "\"")
            (exp_append
               (exp_apply (exp_ident ["String"; "escaped"]) [exp_var "$"])
               (exp_string "\""))))
    else begin
      let li = longident_of_path path in
      match try Some (Env.find_type path env) with Not_found -> None with
        | None ->
            (printer_names,
             printer_exprs,
             exp_fun pat_any (exp_string "<abstract>"))
        | Some decl ->
            let mkfun e =
              let rec aux = function
                | [] ->
                    e
                | { id } :: params ->
                    exp_fun (pat_var ("$p" ^ string_of_int id)) (aux params)
              in
              aux decl.type_params
            in
            let params = List.fold_left (fun set typ -> IntSet.add typ.id set) IntSet.empty decl.type_params in
            match decl with
              | { type_kind = Type_variant l } ->
                  let rec aux printer_names printer_exprs l =
                    match l with
                      | [] ->
                          (printer_names, printer_exprs, [])
                      | (name, []) :: l ->
                          let printer_names, printer_exprs, l = aux printer_names printer_exprs l in
                          (printer_names,
                           printer_exprs,
                           (pat_construct (replace_last li name) None,
                            exp_string name) :: l)
                      | (name, args) :: l ->
                          let printer_names, printer_exprs, l = aux printer_names printer_exprs l in
                          let vars = gen_vars args in
                          let printer_names, printer_exprs, printers = gen_printers env printer_names printer_exprs params args in
                          (printer_names,
                           printer_exprs,
                           (pat_construct (replace_last li name) (Some (pat_tuple (List.map pat_var vars))),
                            exp_append
                              (exp_string (name ^ " "))
                              (exp_enclose
                                 ", " "(" ")"
                                 (List.map2 (fun var printer -> exp_apply printer [exp_var var]) vars printers))) :: l)
                  in
                  let printer_names, printer_exprs, l = aux printer_names printer_exprs l in
                  (printer_names,
                   printer_exprs,
                   mkfun (exp_function l))
              | { type_kind = Type_record (l, _) } ->
                  let rec aux printer_names printer_exprs l =
                    match l with
                      | [] ->
                          (printer_names, printer_exprs, [])
                      | (name, _, typ) :: l ->
                          let printer_names, printer_exprs, printer = gen env printer_names printer_exprs params typ in
                          let printer_names, printer_exprs, l = aux printer_names printer_exprs l in
                          (printer_names,
                           printer_exprs,
                           exp_append
                             (exp_string (name ^ " = "))
                             (exp_apply printer [exp_field (exp_var "$") (replace_last li name)]) :: l)
                  in
                  let printer_names, printer_exprs, l = aux printer_names printer_exprs l in
                  (printer_names,
                   printer_exprs,
                   mkfun
                     (exp_fun
                        (pat_var "$")
                        (exp_enclose "; " "{ " " }" l)))
              | { type_kind = Type_abstract; type_manifest = None } ->
                  (printer_names,
                   printer_exprs,
                   mkfun (exp_fun pat_any (exp_string "<abstract>")))
              | { type_kind = Type_abstract; type_manifest = Some typ } ->
                  let printer_names, printer_exprs, printer = gen env printer_names printer_exprs params typ in
                  (printer_names,
                   printer_exprs,
                   mkfun printer)
    end
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
        match e.exp_type.desc with
          | Tarrow (_, typ, _, _) ->
              let module Gen = MakeGen(struct let loc = e.exp_loc end) in
              let printer_names, printer_exprs, printer = Gen.gen e.exp_env PathMap.empty [] IntSet.empty typ in
              Typecore.type_expression
                e.exp_env
                (Gen.exp_letrec
                   (List.map (fun (name, expr) -> (Gen.pat_var name, expr)) printer_exprs)
                   printer)
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