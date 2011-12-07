(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id: opttopdirs.mli 8477 2007-11-06 15:16:56Z frisch $ *)

(* The toplevel directives. *)

open Format

val dir_quit : unit -> unit
val dir_directory : string -> unit
val dir_cd : string -> unit
val dir_load : formatter -> string -> unit
val dir_use : formatter -> string -> unit
val dir_install_printer : formatter -> Longident.t -> unit
val dir_remove_printer : formatter -> Longident.t -> unit

type 'a printer_type_new = Format.formatter -> 'a -> unit
type 'a printer_type_old = 'a -> unit

(* For topmain.ml. Maybe shouldn't be there *)
val load_file : formatter -> string -> bool
