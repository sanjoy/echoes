	.globl	epoch, call_rt_alloc_app_node, call_rt_alloc_base_node
	.type	epoch, @function

epoch:
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

	.type	call_rt_alloc_base_node, @function

call_rt_alloc_base_node:
	/* runtime_allocate_* expects the VMGlobals struct as first
	   argument. */
	pushq %rdi
	movq %r15, %rdi
	callq runtime_allocate_base_node
	popq %rdi
	retq

	.type	call_rt_alloc_app_node, @function

call_rt_alloc_app_node:
	/* runtime_allocate_* expects the VMGlobals struct as first
	   argument. */
	pushq %rdi
	movq %r15, %rdi
	callq runtime_allocate_app_node
	popq %rdi
	retq
