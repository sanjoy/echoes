	.globl	_epoch, _call_rt_alloc_app_node, _call_rt_alloc_base_node
#ifndef __clang__
	.type	epoch, @function
#endif

#ifdef __clang__
_epoch:
#else
epoch:
#endif
	push %rbp
	push %rbx
	push %rcx
	push %rdx
	push %rsi
	push %r8
	push %r9
	push %r10
	push %r11
	push %r12
	push %r13
	push %r14
	push %r15

	movq %rdi, %r15
	call closure_body_0

	pop %r15
	pop %r14
	pop %r13
	pop %r12
	pop %r11
	pop %r10
	pop %r9
	pop %r8
	pop %rsi
	pop %rdx
	pop %rcx
	pop %rbx
	pop %rbp

	retq

#ifndef __clang__
	.type	call_rt_alloc_base_node, @function
#endif

#ifdef __clang__
_call_rt_alloc_base_node:
#else
call_rt_alloc_base_node:
#endif
	/* runtime_allocate_* expects the VMGlobals struct as first
	   argument. */
	pushq %rdi
	movq %r15, %rdi
	callq _runtime_allocate_base_node
	popq %rdi
	retq

#ifndef __clang__
	.type	call_rt_alloc_app_node, @function
#endif

#ifdef __clang__
_call_rt_alloc_app_node:
#else
call_rt_alloc_app_node:
#endif
	/* runtime_allocate_* expects the VMGlobals struct as first
	   argument. */
	pushq %rdi
	movq %r15, %rdi
	callq _runtime_allocate_app_node
	popq %rdi
	retq
