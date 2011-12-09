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
                 exp_concat ""
                   [exp_string ("`" ^ name ^ " (");
                    exp_apply printer [exp_var "$"];
                    exp_string ")"]))
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
