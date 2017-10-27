(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*               Nicolas Ojeda Bar <n.oje.bar@gmail.com>               *)
(*                                                                     *)
(*  Copyright 2016 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Description of the RISC-V *)

open Misc
open Cmm
open Reg
open Arch
open Mach

(* Instruction selection *)

let word_addressed = false

(* Registers available for register allocation *)

(* Integer register map:
    zero                     always zero
    ra                       return address
    sp, gp, tp               stack pointer, global pointer, thread pointer (preserved by C)
    a0 - a7      0 - 7       arguments/results
    s2 - s9      8 - 15      arguments/results (preserved by C)
    t2 - t6      16 - 20     temporary
    t0           21          temporary (used by assembler)
    t1           22          temporary (reserved for code gen)
    s0           23          frame pointer (preserved by C)
    s1           24          trap pointer (preserved by C)
    s10          25          allocation pointer (preserved by C)
    s11          26          allocation limit (preserved by C)
  Floating-point register map:
    ft0 - ft7    100 - 107   temporary
    fs0 - fs1    108 - 109   general purpose (preserved by C)
    fa0 - fa7    110 - 117   arguments/results
    fs2 - fs9    118 - 125   arguments/results (preserved by C)
    fs10 - fs11  126 - 127   general purpose (preserved by C)
    ft8 - ft11   128 - 131   temporary
*)

let int_reg_name =
  [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
     "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9";
     "t2"; "t3"; "t4"; "t5"; "t6";
     "t0"; "t1";
     "s0"; "s1"; "s10"; "s11" |]

let float_reg_name =
  [| "ft0"; "ft1"; "ft2"; "ft3"; "ft4"; "ft5"; "ft6"; "ft7";
     "fs0"; "fs1";
     "fa0"; "fa1"; "fa2"; "fa3"; "fa4"; "fa5"; "fa6"; "fa7";
     "fs2"; "fs3"; "fs4"; "fs5"; "fs6"; "fs7"; "fs8"; "fs9"; "fs10"; "fs11";
     "ft8"; "ft9"; "ft10"; "ft11" |]

let num_register_classes = 2

let register_class r =
  match r.typ with
  | Val | Int | Addr -> 0
  | Float -> 1

let num_available_registers = [| 21; 32 |]

let first_available_register = [| 0; 100 |]

let register_name r =
  if r < 100 then int_reg_name.(r) else float_reg_name.(r - 100)

let rotate_registers = true

(* Representation of hard registers by pseudo-registers *)

let hard_int_reg =
  let v = Array.make 27 Reg.dummy in
  for i = 0 to 26 do
    v.(i) <- Reg.at_location Int (Reg i)
  done;
  v

let hard_float_reg =
  let v = Array.make 32 Reg.dummy in
  for i = 0 to 31 do
    v.(i) <- Reg.at_location Float (Reg(100 + i))
  done;
  v

let all_phys_regs =
  Array.append hard_int_reg hard_float_reg

let phys_reg n =
  if n < 100 then hard_int_reg.(n) else hard_float_reg.(n - 100)

let stack_slot slot ty =
  Reg.at_location ty (Stack slot)

(* Calling conventions *)

let calling_conventions
    first_int last_int first_float last_float make_stack arg =
  let loc = Array.make (Array.length arg) Reg.dummy in
  let int = ref first_int in
  let float = ref first_float in
  let ofs = ref 0 in
  for i = 0 to Array.length arg - 1 do
    match arg.(i).typ with
    | Val | Int | Addr as ty ->
        if !int <= last_int then begin
          loc.(i) <- phys_reg !int;
          incr int
        end else begin
          loc.(i) <- stack_slot (make_stack !ofs) ty;
          ofs := !ofs + size_int
        end
    | Float ->
        if !float <= last_float then begin
          loc.(i) <- phys_reg !float;
          incr float
        end else begin
          loc.(i) <- stack_slot (make_stack !ofs) Float;
          ofs := !ofs + size_float
        end
  done;
  (loc, Misc.align !ofs 16) (* Keep stack 16-aligned. *)

let incoming ofs = Incoming ofs
let outgoing ofs = Outgoing ofs
let not_supported _ = fatal_error "Proc.loc_results: cannot call"

let max_arguments_for_tailcalls = 16

let loc_spacetime_node_hole = Reg.dummy  (* Spacetime unsupported *)

(* OCaml calling convention:
     first integer args in a0 .. a7, s2 .. s9
     first float args in fa0 .. fa7, fs2 .. fs9
     remaining args on stack.
   Return values in a0 .. a7, s2 .. s9 or fa0 .. fa7, fs2 .. fs9. *)

let single_regs arg = Array.map (fun arg -> [| arg |]) arg
let ensure_single_regs res =
  Array.map (function
      | [| res |] -> res
      | _ -> failwith "proc.ensure_single_regs"
    ) res

let loc_arguments arg =
  calling_conventions 0 15 110 125 outgoing arg

let loc_parameters arg =
  let (loc, _ofs) =
    calling_conventions 0 15 110 125 incoming arg
  in
  loc

let loc_results res =
  let (loc, _ofs) =
    calling_conventions 0 15 110 125 not_supported res
  in
  loc

(* C calling convention:
     first integer args in a0 .. a7
     first float args in fa0 .. fa7
     remaining args on stack.
   Return values in a0 .. a1 or fa0 .. fa1. *)

let external_calling_conventions
    first_int last_int first_float last_float make_stack arg =
  let loc = Array.make (Array.length arg) [| Reg.dummy |] in
  let int = ref first_int in
  let float = ref first_float in
  let ofs = ref 0 in
  for i = 0 to Array.length arg - 1 do
    match arg.(i) with
    | [| arg |] ->
        begin match arg.typ with
        | Val | Int | Addr as ty ->
            if !int <= last_int then begin
              loc.(i) <- [| phys_reg !int |];
              incr int;
              incr float;
            end else begin
              loc.(i) <- [| stack_slot (make_stack !ofs) ty |];
              ofs := !ofs + size_int
            end
        | Float ->
            if !float <= last_float then begin
              loc.(i) <- [| phys_reg !float |];
              incr float;
              incr int;
            end else begin
              loc.(i) <- [| stack_slot (make_stack !ofs) Float |];
              ofs := !ofs + size_float
            end
        end
    | [| arg1; arg2 |] ->
        (* Passing of 64-bit quantities to external functions on 32-bit
           platform. *)
        assert (size_int = 4);
        begin match arg1.typ, arg2.typ with
        | Int, Int ->
            int := Misc.align !int 2;
            if !int <= last_int - 1 then begin
              let reg_lower = phys_reg !int in
              let reg_upper = phys_reg (!int + 1) in
              loc.(i) <- [| reg_lower; reg_upper |];
              int := !int + 2
            end else begin
              let size_int64 = 8 in
              ofs := Misc.align !ofs size_int64;
              let ofs_lower = !ofs in
              let ofs_upper = !ofs + size_int in
              let stack_lower = stack_slot (make_stack ofs_lower) Int in
              let stack_upper = stack_slot (make_stack ofs_upper) Int in
              loc.(i) <- [| stack_lower; stack_upper |];
              ofs := !ofs + size_int64
            end
        | _ ->
            let f = function Int -> "I" | Addr -> "A" | Val -> "V" | Float -> "F" in
            fatal_error (Printf.sprintf "Proc.calling_conventions: bad register \
                                         type(s) for multi-register argument: %s, %s"
                           (f arg1.typ) (f arg2.typ))
        end
    | _ ->
        fatal_error "Proc.calling_conventions: bad number of register for \
                     multi-register argument"
  done;
  (loc, Misc.align !ofs 16) (* Keep stack 16-aligned. *)

let loc_external_arguments arg =
  external_calling_conventions 0 7 110 117 outgoing arg

let loc_external_results res =
  let (loc, _ofs) =
    external_calling_conventions 0 1 110 111 not_supported (single_regs res)
  in
  ensure_single_regs loc

(* Exceptions are in GPR 3 *)

let loc_exn_bucket = phys_reg 0

(* Volatile registers: none *)

let regs_are_volatile _ = false

(* Registers destroyed by operations *)

let destroyed_at_c_call =
  Array.of_list(List.map phys_reg
    [0; 1; 2; 3; 4; 5; 6; 7; 16; 17; 18; 19; 20; (* 21; 22; *)
     100; 101; 102; 103; 104; 105; 106; 107; 110; 111; 112; 113; 114; 115; 116;
     117; 128; 129; 130; 131])

let destroyed_at_oper = function
  | Iop(Icall_ind _ | Icall_imm _ | Iextcall{alloc = true; _}) -> all_phys_regs
  | Iop(Iextcall{alloc = false; _}) -> destroyed_at_c_call
  | _ -> [||]

let destroyed_at_raise = all_phys_regs

(* Maximal register pressure *)

let safe_register_pressure = function
  | Iextcall _ -> 15
  | _ -> 21

let max_register_pressure = function
  | Iextcall _ -> [| 15; 18 |]
  | _ -> [| 21; 30 |]

(* Pure operations (without any side effect besides updating their result
   registers). *)

let op_is_pure = function
  | Icall_ind _ | Icall_imm _ | Itailcall_ind _ | Itailcall_imm _
  | Iextcall _ | Istackoffset _ | Istore _ | Ialloc _
  | Iintop(Icheckbound _) | Iintop_imm(Icheckbound _, _) -> false
  | Ispecific(Imultaddf _ | Imultsubf _) -> true
  | _ -> true

(* Layout of the stack *)

let num_stack_slots = [| 0; 0 |]
let contains_calls = ref false

(* Calling the assembler *)

let assemble_file infile outfile =
  Ccomp.command
    (Config.asm ^ " -o " ^ Filename.quote outfile ^ " " ^ Filename.quote infile)

let init () = ()
