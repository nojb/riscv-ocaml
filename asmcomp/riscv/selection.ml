(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*               Nicolas Ojeda Bar <n.oje.bar@gmail.com>               *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Instruction selection for the RISC-V processor *)

open Cmm
open Arch
open Mach

(* Instruction selection *)

class selector = object (self)

inherit Selectgen.selector_generic as super

method is_immediate n = (n <= 0x7FF) && (n >= -0x800)

method select_addressing chunk = function
  | Cop(Cadda, [arg; Cconst_int n]) when self#is_immediate n ->
      (Iindexed n, arg)
  | Cop(Cadda, [arg1; Cop(Caddi, [arg2; Cconst_int n])]) when self#is_immediate n ->
      (Iindexed n, Cop(Caddi, [arg1; arg2]))
  | arg ->
      (Iindexed 0, arg)

method! select_operation op args =
  match (op, args) with
  (* RISC-V does not support immediate operands for multiply high *)
  | (Cmulhi, _) -> (Iintop Imulh, args)
  (* The and, or and xor instructions have a different range of immediate
     operands than the other instructions *)
  | (Cand, _) -> self#select_logical Iand args
  | (Cor, _) -> self#select_logical Ior args
  | (Cxor, _) -> self#select_logical Ixor args
  (* Recognize (neg-)mult-add and (neg-)mult-sub instructions *)
  | (Caddf, [Cop(Cmulf, [arg1; arg2]); arg3])
  | (Caddf, [arg3; Cop(Cmulf, [arg1; arg2])]) ->
      (Ispecific (Imultaddf false), [arg1; arg2; arg3])
  | (Csubf, [Cop(Cmulf, [arg1; arg2]); arg3]) ->
      (Ispecific (Imultsubf false), [arg1; arg2; arg3])
  | (Cnegf, [Cop(Csubf, [Cop(Cmulf, [arg1; arg2]); arg3])]) ->
      (Ispecific (Imultsubf true), [arg1; arg2; arg3])
  | (Cnegf, [Cop(Caddf, [Cop(Cmulf, [arg1; arg2]); arg3])]) ->
      (Ispecific (Imultaddf true), [arg1; arg2; arg3])
  (* RISC-V does not support immediate operands for comparison operators *)
  | (Ccmpi comp, args) -> (Iintop(Icomp (Isigned comp)), args)
  | (Ccmpa comp, args) -> (Iintop(Icomp (Iunsigned comp)), args)
  | _ ->
      super#select_operation op args

method select_logical op = function
  | [arg; Cconst_int n] when n >= 0 && n <= 0xFFF ->
      (Iintop_imm(op, n), [arg])
  | [Cconst_int n; arg] when n >= 0 && n <= 0xFFF ->
      (Iintop_imm(op, n), [arg])
  | args ->
      (Iintop op, args)

(* Instruction selection for conditionals *)

method select_condition = function
  | Cop(Ccmpi cmp, args) ->
      (Iinttest(Isigned cmp), Ctuple args)
  | Cop(Ccmpa cmp, args) ->
      (Iinttest(Iunsigned cmp), Ctuple args)
  | Cop(Ccmpf cmp, args) ->
      (Ifloattest(cmp, false), Ctuple args)
  | Cop(Cand, [arg; Cconst_int 1]) ->
      (Ioddtest, arg)
  | arg ->
      (Itruetest, arg)

end

let fundecl f = (new selector)#emit_fundecl f
