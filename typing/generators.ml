(*
 * generators.ml
 * -------------
 * Copyright : (c) 2011, Jeremie Dimino <jeremie@dimino.org>
 * Licence   : BSD3
 *)

open Asttypes
open Parsetree

(* +-----------------------------------------------------------------+
   | %show                                                           |
   +-----------------------------------------------------------------+ *)

module MakeShow(Loc : Gen_printer.Loc) = struct
  module Helpers = Gen_printer.MakeHelpers(Loc)

  open Helpers

  let typ t = typ_arrow t (typ_constr (Longident.Lident "string") [])

  let get_param = function
    | { Types.desc = Types.Tarrow (_, typ, _, _) } -> typ
    | _ -> failwith "invalid type for %show"

  let prefix = "string_of_"

  let exp_append a b =
    exp_apply
      (exp_ident ["Pervasives"; "^"])
      [a; b]

  let rec exp_concat sep = function
    | [] ->
        exp_string ""
    | [x] ->
        x
    | x :: l ->
        if sep = "" then
          exp_append x (exp_concat "" l)
        else
          exp_append x (exp_append (exp_string sep) (exp_concat sep l))

  let exp_enclose sep b e l =
    exp_append (exp_string b) (exp_append (exp_concat sep l) (exp_string e))

  let int =
    exp_ident ["Pervasives"; "string_of_int"]

  let char =
    exp_fun
      (pat_var "$")
      (exp_concat ""
         [exp_string "\"";
          exp_apply (exp_ident ["Char"; "escaped"]) [exp_var "$"];
          exp_string "\""])

  let string =
    exp_fun
      (pat_var "$")
      (exp_concat ""
         [exp_string "\"";
          exp_apply (exp_ident ["String"; "escaped"]) [exp_var "$"];
          exp_string "\""])

  let float =
    exp_ident ["Pervasives"; "string_of_float"]

  let bool =
    exp_ident ["Pervasives"; "string_of_bool"]

  let unit =
    exp_fun pat_any (exp_string "()")

  let exn =
    exp_ident ["Printexc"; "to_string"]

  let nativeint =
    exp_fun
      (pat_var "$")
      (exp_concat ""
         [exp_apply (exp_ident ["Nativeint"; "to_string"]) [exp_var "$"];
          exp_string "n"])

  let int32 =
    exp_fun
      (pat_var "$")
      (exp_concat ""
         [exp_apply (exp_ident ["Int32"; "to_string"]) [exp_var "$"];
          exp_string "l"])

  let int64 =
    exp_fun
      (pat_var "$")
      (exp_concat ""
         [exp_apply (exp_ident ["Int64"; "to_string"]) [exp_var "$"];
          exp_string "L"])

  let lazy_t =
    exp_fun
      (pat_var "$p0")
      (exp_fun
         (pat_lazy (pat_var "$"))
         (exp_apply (exp_var "$p0") [exp_var "$"]))

  let list =
    exp_fun
      (pat_var "$p0")
      (exp_function
         [(pat_construct (Longident.Lident "[]") None,
           exp_string "[]");
          (pat_construct (Longident.Lident "::") (Some (pat_tuple [pat_var "$0"; pat_var "$1"])),
           exp_concat ""
             [exp_string "[";
              exp_apply (exp_var "$p0") [exp_var "$0"];
              exp_letrec
                [(pat_var "$aux",
                  exp_function
                    [(pat_construct (Longident.Lident "[]") None,
                      exp_string "");
                     (pat_construct (Longident.Lident "::") (Some (pat_tuple [pat_var "$0"; pat_var "$1"])),
                      exp_concat ""
                        [exp_string "; ";
                         exp_apply (exp_var "$p0") [exp_var "$0"];
                         exp_apply (exp_var "$aux") [exp_var "$1"]])])]
                (exp_apply (exp_var "$aux") [exp_var "$1"]);
              exp_string "]"])])

  let array =
    exp_fun
      (pat_var "$p0")
      (exp_function
         [(pat_array [],
           exp_string "[||]");
          (pat_var "$",
           exp_concat ""
             [exp_string "[|";
              exp_apply (exp_var "$p0") [exp_apply (exp_ident ["Array"; "get"]) [exp_var "$"; exp_int 0]];
              exp_letrec
                [(pat_var "$aux",
                  exp_fun
                    (pat_var "$i")
                    (exp_ifthenelse
                       (exp_apply
                          (exp_ident ["Pervasives"; "="])
                          [exp_var "$i";
                           exp_apply (exp_ident ["Array"; "length"]) [exp_var "$"]])
                       (exp_string "")
                       (exp_concat ""
                          [exp_string "; ";
                           exp_apply (exp_var "$p0") [exp_apply (exp_ident ["Array"; "get"]) [exp_var "$"; exp_var "$i"]];
                           exp_apply (exp_var "$aux") [exp_apply (exp_ident ["Pervasives"; "succ"]) [exp_var "$i"]]])))]
                (exp_apply (exp_var "$aux") [exp_int 1]);
              exp_string "|]"])])

  let var =
    exp_fun pat_any (exp_string "<poly>")

  let abstract =
    exp_fun pat_any (exp_string "<abstract>")

  let arrow =
    exp_fun pat_any (exp_string "<arrow>")

  let tuple printers =
    let vars = gen_vars printers in
    exp_fun
      (pat_tuple (List.map pat_var vars))
      (exp_enclose
         ", " "(" ")"
         (List.map2 (fun var printer -> exp_apply printer [exp_var var]) vars printers))

  let obj =
    exp_fun pat_any (exp_string "<object>")

  let poly_variant l =
    exp_function
      (List.map
         (function
            | (name, None) ->
                (pat_variant name None,
                 exp_string ("`" ^ name))
            | (name, Some printer) ->
                (pat_variant name (Some (pat_var "$")),
                 exp_append
                   (exp_string ("`" ^ name ^ " "))
                   (exp_apply printer [exp_var "$"])))
         l)


  let package =
    exp_fun pat_any (exp_string "<package>")

  let variant l =
    exp_function
      (List.map
         (function
            | (li, name, []) ->
                (pat_construct li None,
                 exp_string name)
            | (li, name, printers) ->
                let vars = gen_vars printers in
                (pat_construct li (Some (pat_tuple (List.map pat_var vars))),
                 exp_append
                   (exp_string (name ^ " "))
                   (exp_enclose
                      ", " "(" ")"
                      (List.map2 (fun var printer -> exp_apply printer [exp_var var]) vars printers))))
         l)

  let record l =
    exp_fun
      (pat_var "$")
      (exp_enclose "; " "{ " " }"
         (List.map
            (fun (li, name, printer) ->
               exp_append
                 (exp_string (name ^ " = "))
                 (exp_apply printer [exp_field (exp_var "$") li]))
            l))
end

module Show = Gen_printer.GeneratorOfCombinators(MakeShow)

let () = Gen_printer.register_generator "%show" Show.generate


(* +-----------------------------------------------------------------+
   | %pretty_print                                                   |
   +-----------------------------------------------------------------+ *)

module MakePrettyPrint(Loc : Gen_printer.Loc) = struct
  module Helpers = Gen_printer.MakeHelpers(Loc)

  open Helpers

  let typ t =
    typ_arrow
      (typ_constr (Longident.Ldot (Longident.Lident "Format", "formatter")) [])
      (typ_arrow t (typ_constr (Longident.Lident "unit") []))

  let get_param = function
    | { Types.desc = Types.Tarrow (_, _, { Types.desc = Types.Tarrow (_, typ, _, _) }, _) } -> typ
    | _ -> failwith "invalid type for %pretty_print"

  let prefix = "pp_print_"

  let exp_print_string e =
    exp_apply
      (exp_ident ["Format"; "pp_print_string"])
      [exp_var "$ppf"; e]

  let exp_print_space =
    exp_apply (exp_ident ["Format"; "pp_print_space"]) [exp_var "$ppf"; exp_unit]

  let exp_open_box n =
    exp_apply (exp_ident ["Format"; "pp_open_box"]) [exp_var "$ppf"; exp_int n]

  let exp_close_box =
    exp_apply (exp_ident ["Format"; "pp_close_box"]) [exp_var "$ppf"; exp_unit]

  let exp_enclose sep a b l =
    exp_seq
      (List.flatten
         [[exp_open_box (String.length b);
           exp_print_string (exp_string a)];
          (match l with
             | [] ->
                 []
             | [_] ->
                 l
             | e :: l ->
                 e :: List.flatten (List.map (fun e ->
                                                [exp_print_string (exp_string sep);
                                                 exp_print_space;
                                                 e]) l));
          [exp_print_string (exp_string b);
           exp_close_box]])

  let int =
    exp_ident ["Format"; "pp_print_int"]

  let char =
    exp_fun
      (pat_var "$ppf")
      (exp_fun
         (pat_var "$")
         (exp_seq
            [exp_print_string (exp_string "\"");
             exp_print_string (exp_apply (exp_ident ["Char"; "escaped"]) [exp_var "$"]);
             exp_print_string (exp_string "\"")]))

  let string =
    exp_fun
      (pat_var "$ppf")
      (exp_fun
         (pat_var "$")
         (exp_seq
            [exp_print_string (exp_string "\"");
             exp_print_string (exp_apply (exp_ident ["String"; "escaped"]) [exp_var "$"]);
             exp_print_string (exp_string "\"")]))

  let float =
    exp_ident ["Format"; "pp_print_float"]

  let bool =
    exp_ident ["Format"; "pp_print_bool"]

  let unit =
    exp_fun
      (pat_var "$ppf")
      (exp_fun
         pat_any
         (exp_print_string (exp_string "()")))

  let exn =
    exp_fun
      (pat_var "$ppf")
      (exp_fun
         (pat_var "$")
         (exp_print_string
            (exp_apply (exp_ident ["Printexc"; "to_string"]) [exp_var "$"])))

  let nativeint =
    exp_fun
      (pat_var "$ppf")
      (exp_fun
         (pat_var "$")
         (exp_seq
            [exp_print_string (exp_apply (exp_ident ["Nativeint"; "to_string"]) [exp_var "$"]);
             exp_print_string (exp_string "n")]))

  let int32 =
    exp_fun
      (pat_var "$ppf")
      (exp_fun
         (pat_var "$")
         (exp_seq
            [exp_print_string (exp_apply (exp_ident ["Int32"; "to_string"]) [exp_var "$"]);
             exp_print_string (exp_string "l")]))

  let int64 =
    exp_fun
      (pat_var "$ppf")
      (exp_fun
         (pat_var "$")
         (exp_seq
            [exp_print_string (exp_apply (exp_ident ["Int64"; "to_string"]) [exp_var "$"]);
             exp_print_string (exp_string "L")]))

  let lazy_t =
    exp_fun
      (pat_var "$p0")
      (exp_fun
         (pat_var "$ppf")
         (exp_fun
            (pat_lazy (pat_var "$"))
            (exp_apply (exp_var "$p0") [exp_var "$ppf"; exp_var "$"])))

  let list =
    exp_fun
      (pat_var "$p0")
      (exp_fun
         (pat_var "$ppf")
         (exp_function
            [(pat_construct (Longident.Lident "[]") None,
              exp_print_string (exp_string "[]"));
             (pat_construct (Longident.Lident "::") (Some (pat_tuple [pat_var "$0"; pat_var "$1"])),
              exp_seq
                [exp_open_box 1;
                 exp_print_string (exp_string "[");
                 exp_apply (exp_var "$p0") [exp_var "$ppf"; exp_var "$0"];
                 exp_letrec
                   [(pat_var "$aux",
                     exp_function
                       [(pat_construct (Longident.Lident "[]") None,
                         exp_unit);
                        (pat_construct (Longident.Lident "::") (Some (pat_tuple [pat_var "$0"; pat_var "$1"])),
                         exp_seq
                           [exp_print_string (exp_string ";");
                            exp_print_space;
                            exp_apply (exp_var "$p0") [exp_var "$ppf"; exp_var "$0"];
                            exp_apply (exp_var "$aux") [exp_var "$1"]])])]
                   (exp_apply (exp_var "$aux") [exp_var "$1"]);
                 exp_print_string (exp_string "]");
                 exp_close_box])]))

  let array =
    exp_fun
      (pat_var "$p0")
      (exp_fun
         (pat_var "$ppf")
         (exp_function
            [(pat_array [],
              exp_print_string (exp_string "[||]"));
             (pat_var "$",
              exp_seq
                [exp_open_box 2;
                 exp_print_string (exp_string "[|");
                 exp_apply (exp_var "$p0") [exp_var "$ppf"; exp_apply (exp_ident ["Array"; "get"]) [exp_var "$"; exp_int 0]];
                 exp_letrec
                   [(pat_var "$aux",
                     exp_fun
                       (pat_var "$i")
                       (exp_ifthenelse
                          (exp_apply
                             (exp_ident ["Pervasives"; "="])
                             [exp_var "$i";
                              exp_apply (exp_ident ["Array"; "length"]) [exp_var "$"]])
                          exp_unit
                          (exp_seq
                             [exp_print_string (exp_string ";");
                              exp_print_space;
                              exp_apply (exp_var "$p0") [exp_var "$ppf"; exp_apply (exp_ident ["Array"; "get"]) [exp_var "$"; exp_var "$i"]];
                              exp_apply (exp_var "$aux") [exp_apply (exp_ident ["Pervasives"; "succ"]) [exp_var "$i"]]])))]
                   (exp_apply (exp_var "$aux") [exp_int 1]);
                 exp_print_string (exp_string "|]");
                 exp_close_box])]))

  let var =
    exp_fun (pat_var "$ppf") (exp_fun pat_any (exp_print_string (exp_string "<poly>")))

  let abstract =
    exp_fun (pat_var "$ppf") (exp_fun pat_any (exp_print_string (exp_string "<abstract>")))

  let arrow =
    exp_fun (pat_var "$ppf") (exp_fun pat_any (exp_print_string (exp_string "<arrow>")))

  let tuple printers =
    let vars = gen_vars printers in
    exp_fun
      (pat_var "$ppf")
      (exp_fun
         (pat_tuple (List.map pat_var vars))
         (exp_enclose
            "," "(" ")"
            (List.map2 (fun var printer -> exp_apply printer [exp_var "$ppf"; exp_var var]) vars printers)))

  let obj =
    exp_fun (pat_var "$ppf") (exp_fun pat_any (exp_print_string (exp_string "<object>")))

  let poly_variant l =
    exp_fun
      (pat_var "$ppf")
      (exp_function
         (List.map
            (function
               | (name, None) ->
                   (pat_variant name None,
                    exp_print_string (exp_string ("`" ^ name)))
               | (name, Some printer) ->
                   (pat_variant name (Some (pat_var "$")),
                    exp_seq
                      [exp_open_box 2;
                       exp_print_string (exp_string ("`" ^ name));
                       exp_print_space;
                       exp_apply printer [exp_var "$ppf"; exp_var "$"];
                       exp_close_box]))
            l))

  let package =
    exp_fun (pat_var "$ppf") (exp_fun pat_any (exp_print_string (exp_string "<package>")))

  let variant l =
    exp_fun
      (pat_var "$ppf")
      (exp_function
         (List.map
            (function
               | (li, name, []) ->
                   (pat_construct li None,
                    exp_print_string (exp_string name))
               | (li, name, printers) ->
                   let vars = gen_vars printers in
                   (pat_construct li (Some (pat_tuple (List.map pat_var vars))),
                    exp_seq
                      [exp_open_box 2;
                       exp_print_string (exp_string name);
                       exp_print_space;
                       exp_enclose
                         "," "(" ")"
                         (List.map2 (fun var printer -> exp_apply printer [exp_var "$ppf"; exp_var var]) vars printers);
                       exp_close_box]))
            l))

  let record l =
    exp_fun
      (pat_var "$ppf")
      (exp_fun
         (pat_var "$")
         (exp_enclose ";" "{ " " }"
            (List.map
               (fun (li, name, printer) ->
                  exp_seq
                    [exp_open_box 1;
                     exp_print_string (exp_string name);
                     exp_print_space;
                     exp_print_string (exp_string "=");
                     exp_print_space;
                     (exp_apply printer [exp_var "$ppf"; exp_field (exp_var "$") li]);
                     exp_close_box])
               l)))
end

module PrettyPrint = Gen_printer.GeneratorOfCombinators(MakePrettyPrint)

let () = Gen_printer.register_generator "%pretty_print" PrettyPrint.generate
