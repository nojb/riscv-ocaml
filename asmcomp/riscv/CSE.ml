(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*               Nicolas Ojeda Bar <n.oje.bar@gmail.com>               *)
(*                                                                     *)
(*  Copyright 2106 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* CSE for the RISC-V *)

open Arch
open Mach
open CSEgen

class cse = object (_self)

inherit cse_generic as super

method! class_of_operation op =
  match op with
  | Ispecific(Imultaddf _ | Imultsubf _) -> Op_pure
  | _ -> super#class_of_operation op

method! is_cheap_operation op =
  match op with
  | Iconst_int n -> n <= 0x7FFn && n >= -0x800n
  | _ -> false

end

let fundecl f =
  (new cse)#fundecl f
