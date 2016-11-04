/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*               Nicolas Ojeda Bar <n.oje.bar@gmail.com>               */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* Asm part of the runtime system, RISC-V processor, 64-bit mode */
/* Must be preprocessed by cpp */

#define TRAP_PTR s1
#define ALLOC_PTR s10
#define ALLOC_LIMIT s11
#define TMP0 t0
#define TMP1 t1
#define ARG t2

#ifdef MODEL_riscv64
#define STORE sd
#define LOAD ld
#else
#define STORE sw
#define LOAD lw
#endif

#define LOADGLOBAL(reg,symb,tmp) \
	la	tmp, symb; \
	LOAD	reg, 0(tmp)

#define STOREGLOBAL(reg,symb,tmp) \
	la	tmp, symb; \
	STORE	reg, 0(tmp)

	.section	.text

/* Invoke the garbage collector. */

	.globl	caml_system__code_begin
caml_system__code_begin:

        .align	2
        .globl	caml_call_gc
        .type	caml_call_gc, @function
caml_call_gc:
        /* Record return address */
        STOREGLOBAL(ra, caml_last_return_address, TMP0)
        /* Record lowest stack address */
        mv	TMP1, sp
        STOREGLOBAL(TMP1, caml_bottom_of_stack, TMP0)
.Lcaml_call_gc:
	/* Set up stack space, saving return address */
        /* (1 reg for RA, 1 reg for FP, 21 allocatable int regs, 20 caller-save float regs) * 8 */
        /* + 1 for alignment */
        addi	sp, sp, -0x160
        mv	s0, sp
        STORE	ra, 0x8(sp)
        STORE	s0, 0x0(sp)
        /* Save allocatable integer registers on the stack,
           in the order given in proc.ml */
        STORE	a0, 0x10(sp)
        STORE	a1, 0x18(sp)
        STORE	a2, 0x20(sp)
        STORE	a3, 0x28(sp)
        STORE	a4, 0x30(sp)
        STORE	a5, 0x38(sp)
        STORE	a6, 0x40(sp)
        STORE	a7, 0x48(sp)
        STORE	s2, 0x50(sp)
        STORE	s3, 0x58(sp)
        STORE	s4, 0x60(sp)
        STORE	s5, 0x68(sp)
        STORE	s6, 0x70(sp)
        STORE	s7, 0x78(sp)
        STORE	s8, 0x80(sp)
        STORE	s9, 0x88(sp)
        STORE	t2, 0x90(sp)
        STORE	t3, 0x98(sp)
        STORE	t4, 0xa0(sp)
        STORE	t5, 0xa8(sp)
        STORE	t6, 0xb0(sp)
        /* Save caller-save floating-point registers on the stack
           (callee-saves are preserved by caml_garbage_collection) */
        fsd	ft0, 0xb8(sp)
        fsd	ft1, 0xc0(sp)
        fsd	ft2, 0xc8(sp)
        fsd	ft3, 0xd0(sp)
        fsd	ft4, 0xd8(sp)
        fsd	ft5, 0xe0(sp)
        fsd	ft6, 0xe8(sp)
        fsd	ft7, 0xf0(sp)
        fsd	fa0, 0xf8(sp)
        fsd	fa1, 0x100(sp)
        fsd	fa2, 0x108(sp)
        fsd	fa3, 0x110(sp)
        fsd	fa4, 0x118(sp)
        fsd	fa5, 0x120(sp)
        fsd	fa6, 0x128(sp)
        fsd	fa7, 0x130(sp)
        fsd	ft8, 0x138(sp)
        fsd	ft9, 0x140(sp)
        fsd	ft9, 0x148(sp)
        fsd	ft10, 0x150(sp)
        fsd	ft11, 0x158(sp)
        /* Store pointer to saved integer registers in caml_gc_regs */
        addi	TMP1, sp, 16
        STOREGLOBAL(TMP1, caml_gc_regs, TMP0)
        /* Save current allocation pointer for debugging purposes */
        STOREGLOBAL(ALLOC_PTR, caml_young_ptr, TMP0)
        /* Save trap pointer in case an exception is raised during GC */
        STOREGLOBAL(TRAP_PTR, caml_exception_pointer, TMP0)
        /* Call the garbage collector */
        call	caml_garbage_collection
        /* Restore registers */
        LOAD	a0, 0x10(sp)
        LOAD	a1, 0x18(sp)
        LOAD	a2, 0x20(sp)
        LOAD	a3, 0x28(sp)
        LOAD	a4, 0x30(sp)
        LOAD	a5, 0x38(sp)
        LOAD	a6, 0x40(sp)
        LOAD	a7, 0x48(sp)
        LOAD	s2, 0x50(sp)
        LOAD	s3, 0x58(sp)
        LOAD	s4, 0x60(sp)
        LOAD	s5, 0x68(sp)
        LOAD	s6, 0x70(sp)
        LOAD	s7, 0x78(sp)
        LOAD	s8, 0x80(sp)
        LOAD	s9, 0x88(sp)
        LOAD	t2, 0x90(sp)
        LOAD	t3, 0x98(sp)
        LOAD	t4, 0xa0(sp)
        LOAD	t5, 0xa8(sp)
        LOAD	t6, 0xb0(sp)
        fld	ft0, 0xb8(sp)
        fld	ft1, 0xc0(sp)
        fld	ft2, 0xc8(sp)
        fld	ft3, 0xd0(sp)
        fld	ft4, 0xd8(sp)
        fld	ft5, 0xe0(sp)
        fld	ft6, 0xe8(sp)
        fld	ft7, 0xf0(sp)
        fld	fa0, 0xf8(sp)
        fld	fa1, 0x100(sp)
        fld	fa2, 0x108(sp)
        fld	fa3, 0x110(sp)
        fld	fa4, 0x118(sp)
        fld	fa5, 0x120(sp)
        fld	fa6, 0x128(sp)
        fld	fa7, 0x130(sp)
        fld	ft8, 0x138(sp)
        fld	ft9, 0x140(sp)
        fld	ft9, 0x148(sp)
        fld	ft10, 0x150(sp)
        fld	ft11, 0x158(sp)
        /* Reload new allocation pointer and allocation limit */
        LOADGLOBAL(ALLOC_PTR, caml_young_ptr, TMP0)
        LOADGLOBAL(ALLOC_LIMIT, caml_young_limit, TMP0)
        /* Free stack space and return to caller */
        LOAD	ra, 0x8(sp)
        LOAD	s0, 0x0(sp)
        addi	sp, sp, 0x160
        ret
        .size	caml_call_gc, .-caml_call_gc

/* Call a C function from OCaml */
/* Function to call is in ARG */

        .align	2
	.globl	caml_c_call
	.type	caml_c_call, @function
caml_c_call:
        /* Preserve return address in callee-save register s2 */
        mv	s2, ra
        /* Record lowest stack address and return address */
        STOREGLOBAL(ra, caml_last_return_address, TMP0)
        mv	TMP1, sp
        STOREGLOBAL(TMP1, caml_bottom_of_stack, TMP0)
        /* Make the exception handler alloc ptr available to the C code */
        STOREGLOBAL(ALLOC_PTR, caml_young_ptr, TMP0)
        STOREGLOBAL(TRAP_PTR, caml_exception_pointer, TMP0)
        /* Call the function */
        jalr	ARG
        /* Reload alloc ptr and alloc limit */
        LOADGLOBAL(ALLOC_PTR, caml_young_ptr, TMP0)
        LOADGLOBAL(TRAP_PTR, caml_exception_pointer, TMP0)
        /* Return */
        jr	s2
        .size	caml_c_call, .-caml_c_call

/* Raise an exception from OCaml */
        .align	2
	.globl	caml_raise_exn
	.type	caml_raise_exn, @function
caml_raise_exn:
        /* Test if backtrace is active */
        LOADGLOBAL(TMP1, caml_backtrace_active, TMP0)
        bnez	TMP1, 2f
1:      /* Cut stack at current trap handler */
        mv	sp, TRAP_PTR
        /* Pop previous handler and jump to it */
        ld	TMP1, 8(sp)
        ld	TRAP_PTR, 0(sp)
        addi	sp, sp, 16
        jr	TMP1
2:      /* Preserve exception bucket in callee-save register s2 */
        mv	s2, a0
        /* Stash the backtrace */
        mv	a1, ra
        mv	a2, sp
        mv	a3, TRAP_PTR
        call	caml_stash_backtrace
        /* Restore exception bucket and raise */
        mv	a0, s2
        j	1b
        .size	caml_raise_exn, .-caml_raise_exn

	.globl	caml_reraise_exn
	.type	caml_reraise_exn, @function

/* Raise an exception from C */

        .align	2
	.globl	caml_raise_exception
	.type	caml_raise_exception, @function
caml_raise_exception:
	LOADGLOBAL(TRAP_PTR, caml_exception_pointer, TMP0)
        LOADGLOBAL(ALLOC_PTR, caml_young_ptr, TMP0)
        LOADGLOBAL(ALLOC_LIMIT, caml_young_limit, TMP0)
        LOADGLOBAL(TMP1, caml_backtrace_active, TMP0)
        bnez	TMP1, 2f
1:      /* Cut stack at current trap handler */
        mv	sp, TRAP_PTR
        LOAD	TMP1, 8(sp)
        LOAD	TRAP_PTR, 0(sp)
        addi	sp, sp, 16
        jr	TMP1
2:      /* Preserve exception bucket in callee-save register s2 */
        mv	s2, a0
        LOADGLOBAL(a1, caml_last_return_address, TMP0)
        LOADGLOBAL(a2, caml_bottom_of_stack, TMP0)
        mv	a3, TRAP_PTR
        call	caml_stash_backtrace
        mv	a0, s2
        j	1b
        .size	caml_raise_exception, .-caml_raise_exception

/* Start the OCaml program */

        .align	2
	.globl	caml_start_program
	.type	caml_start_program, @function
caml_start_program:

        la	ARG, caml_program
        /* Code shared with caml_callback* */
        /* Address of OCaml code to call is in ARG */
        /* Arguments to the OCaml code are in a0 ... a7 */
.Ljump_to_caml:
	/* Set up stack frame and save callee-save registers */
	addi	sp, sp, -0xd0
	STORE	ra, 0xc0(sp)
	STORE	s0, 0x0(sp)
	STORE	s1, 0x8(sp)
	STORE	s2, 0x10(sp)
	STORE	s3, 0x18(sp)
	STORE	s4, 0x20(sp)
	STORE	s5, 0x28(sp)
	STORE	s6, 0x30(sp)
	STORE	s7, 0x38(sp)
	STORE	s8, 0x40(sp)
	STORE	s9, 0x48(sp)
	STORE	s10, 0x50(sp)
	STORE	s11, 0x58(sp)
	fsd	fs0, 0x60(sp)
	fsd	fs1, 0x68(sp)
	fsd	fs2, 0x70(sp)
	fsd	fs3, 0x78(sp)
	fsd	fs4, 0x80(sp)
	fsd	fs5, 0x88(sp)
	fsd	fs6, 0x90(sp)
	fsd	fs7, 0x98(sp)
	fsd	fs8, 0xa0(sp)
	fsd	fs9, 0xa8(sp)
	fsd	fs10, 0xb0(sp)
	fsd	fs11, 0xb8(sp)
	addi	sp, sp, -32
        /* Setup a callback link on the stack */
	LOADGLOBAL(a0, caml_bottom_of_stack, TMP0)
	STORE	a0, 0(sp)
	LOADGLOBAL(a1, caml_last_return_address, TMP0)
	STORE	a1, 8(sp)
	LOADGLOBAL(a2, caml_gc_regs, TMP0)
	STORE	a2, 16(sp)
	/* set up a trap frame */
	addi	sp, sp, -16
	LOADGLOBAL(TMP1, caml_exception_pointer, TMP0)
	STORE	TMP1, 0(sp)
	lla	TMP0, .Ltrap_handler
	STORE	TMP0, 8(sp)
	mv	TRAP_PTR, sp
	LOADGLOBAL(ALLOC_PTR, caml_young_ptr, TMP0)
	LOADGLOBAL(ALLOC_LIMIT, caml_young_limit, TMP0)
	STOREGLOBAL(x0, caml_last_return_address, TMP0)
	jalr	ARG
.Lcaml_retaddr:	/* pop trap frame, restoring caml_exception_pointer */
	LOAD	TMP1, 0(sp)
	STOREGLOBAL(TMP1, caml_exception_pointer, TMP0)
	addi	sp, sp, 16
.Lreturn_result:	/* pop callback link, restoring global variables */
	LOAD	TMP1, 0(sp)
	STOREGLOBAL(TMP1, caml_bottom_of_stack, TMP0)
	LOAD	TMP1, 8(sp)
	STOREGLOBAL(TMP1, caml_last_return_address, TMP0)
	LOAD	TMP1, 16(sp)
	STOREGLOBAL(TMP1, caml_gc_regs, TMP0)
	addi	sp, sp, 32
	/* Update allocation pointer */
	STOREGLOBAL(ALLOC_PTR, caml_young_ptr, TMP0)
	/* reload callee-save registers and return */
	LOAD	ra, 0xc0(sp)
	LOAD	s0, 0x0(sp)
	LOAD	s1, 0x8(sp)
	LOAD	s2, 0x10(sp)
	LOAD	s3, 0x18(sp)
	LOAD	s4, 0x20(sp)
	LOAD	s5, 0x28(sp)
	LOAD	s6, 0x30(sp)
	LOAD	s7, 0x38(sp)
	LOAD	s8, 0x40(sp)
	LOAD	s9, 0x48(sp)
	LOAD	s10, 0x50(sp)
	LOAD	s11, 0x58(sp)
	fld	fs0, 0x60(sp)
	fld	fs1, 0x68(sp)
	fld	fs2, 0x70(sp)
	fld	fs3, 0x78(sp)
	fld	fs4, 0x80(sp)
	fld	fs5, 0x88(sp)
	fld	fs6, 0x90(sp)
	fld	fs7, 0x98(sp)
	fld	fs8, 0xa0(sp)
	fld	fs9, 0xa8(sp)
	fld	fs10, 0xb0(sp)
	fld	fs11, 0xb8(sp)
	addi	sp, sp, 0xd0
	ret
.Ltrap_handler:
	STOREGLOBAL(TRAP_PTR, caml_exception_pointer, TMP0)
	ori	a0, a0, 2
	j	.Lreturn_result
	.size	caml_start_program, .-caml_start_program

/* Callback from C to OCaml */

        .align	2
	.globl	caml_callback_exn
	.type	caml_callback_exn, @function
caml_callback_exn:
        /* Initial shuffling of arguments (a0 = closure, a1 = first arg) */
        mv	TMP1, a0
        mv	a0, a1		/* a0 = first arg */
        mv	a1, TMP1	/* a1 = closure environment */
        LOAD	ARG, 0(TMP1)	/* code pointer */
        j	.Ljump_to_caml
        .size	caml_callback_exn, .-caml_callback_exn

        .align	2
	.globl	caml_callback2_exn
	.type	caml_callback2_exn, @function
caml_callback2_exn:
        /* Initial shuffling of arguments (a0 = closure, a1 = arg1, a2 = arg2) */
        mv	TMP1, a0
        mv	a0, a1
        mv	a1, a2
        mv	a2, TMP1
        la	ARG, caml_apply2
        j	.Ljump_to_caml
        .size	caml_callback2_exn, .-caml_callback2_exn

        .align	2
	.globl	caml_callback3_exn
	.type	caml_callback3_exn, @function
caml_callback3_exn:
        /* Initial shuffling of argumnets */
        /* (a0 = closure, a1 = arg1, a2 = arg2, a3 = arg3) */
        mv	TMP1, a0
        mv	a0, a1
        mv	a1, a2
        mv	a2, a3
        mv	a3, TMP1
        la	ARG, caml_apply3
        j	.Ljump_to_caml
        .size	caml_callback3_exn, .-caml_callback3_exn

        .align	2
	.globl	caml_ml_array_bound_error
	.type	caml_ml_array_bound_error, @function
caml_ml_array_bound_error:
        /* Load address of [caml_array_bound_error] in ARG */
        la	ARG, caml_array_bound_error
        /* Call that function */
        j	caml_c_call

	.globl	caml_system__code_end
caml_system__code_end:

/* GC roots for callback */

	.section .data
        .align	3
	.globl	caml_system__frametable
	.type	caml_system__frametable, @object
caml_system__frametable:
	.quad	1		/* one descriptor */
	.quad	.Lcaml_retaddr  /* return address into callback */
	.short	-1		/* negative frame size => use callback link */
	.short	0		/* no roots */
	.align	3
	.size	caml_system__frametable, .-caml_system__frametable
