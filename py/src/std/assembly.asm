.intel_syntax noprefix

.global zero, one, one_fifth, half
// for export
.section .data
zero:
.double 0.0
one:
.double 1.0
one_fifth:
.double 0.2
half:
.double 0.5

.section .text
.global relu, hard_sigmoid, gcd_long, gcd_qword, gcd_int, gcd_dword
.global stosb, stosw, stosd, stosq, scasd, repe_scasd, movsd, movsq, bsr_dword

.global sum8args

.ifdef linux

bsr_dword:
	bsr eax, edi
	ret

//determine the gcd of (rcx, rdx): gcd(rcx, rdx) = gcd(rdx, rcx % rdx)
gcd_qword:
	mov rcx, rdi
	mov rdx, rsi
gcd_qword_linux:
	mov rax, rcx
	or rdx, rdx
	jz jmp_ret
	mov rcx, rdx
	mov rdx, 0
	div rcx
// rax = quo, rdx = rem//
	jmp gcd_qword_linux

gcd_long:
	mov rcx, rdi
	mov rdx, rsi
gcd_long_linux:
	mov rax, rcx
	or rdx, rdx
	jz jmp_ret
	mov rcx, rdx
	cqo
// Convert Quadword to Double Quadword, ie, Sign-extends the contents of RAX to RDX:RAX.
	idiv rcx
// rax = quo, rdx = rem//
	jmp gcd_long_linux


//determine the gcd of (rcx, rdx): gcd(rcx, rdx) = gcd(rdx, rcx % rdx)
gcd_int:
	mov rcx, rdi
	mov rdx, rsi
gcd_int_linux:
	mov eax, ecx
	or edx, edx
	jz jmp_ret
	mov ecx, edx
	cdq
// Convert Doubleword to Quadword, ie, Sign-extends register EAX and saves the results in register pair EDX:EAX.
	idiv ecx
// eax = quo, edx = rem//
	jmp gcd_int_linux

//determine the gcd of (rcx, rdx): gcd(rcx, rdx) = gcd(rdx, rcx % rdx)
gcd_dword:
	mov rcx, rdi
	mov rdx, rsi
gcd_dword_linux:
	mov eax, ecx
	or edx, edx
	jz jmp_ret
	mov ecx, edx
	xor edx, edx
	div ecx
// eax = quo, edx = rem//
	jmp gcd_dword_linux

stosb:
//	mov rdi, rdi
	mov al, sil
	mov rcx, rdx
	rep stosb
	ret

stosw:
//	mov rdi, rdi
	mov ax, si
	mov rcx, rdx
	rep stosw
	ret

stosd:
//	mov rdi, rdi
	mov eax, esi
	mov rcx, rdx
	rep stosd
	ret

stosq:
//	mov rdi, rdi
	mov rax, rsi
	mov rcx, rdx
	rep stosq
	ret

scasd:
	mov eax, esi
	mov rcx, rdx
//	repeat while the current element of the string is not equal to eax
	repne scasd
	mov rax, rdi
	ret

repe_scasd:
	mov eax, esi
	mov rcx, rdx
//	repeat while the current element of the string is equal to eax
	repe scasd
	mov rax, rdi
	ret

movsq:
//	mov rdi, rdi
//	mov rsi, rsi
	mov rcx, rdx
	rep movsq
	mov rax, rdi
	ret

movsd:
//  mov rdi, rdi
//  mov rsi, rsi
    mov rcx, rdx
    rep movsd
    mov rax, rdi
    ret

sum8args:
	mov rax, rdi
	add rax, rsi
	add rax, rdx
	add rax, rcx
	add rax, r8
	add rax, r9
	add rax, [rsp+8]
	add rax, [rsp+16]
	ret

relu:
	mov eax, 0
	cvtsi2sd xmm1, eax
	maxsd xmm0, xmm1
	ret

hard_sigmoid:
	mov eax, 2
	cvtsi2sd xmm1, eax
	mulsd xmm0, xmm1
// 2x

	mov eax, 5
	cvtsi2sd xmm1, eax
	addsd xmm0, xmm1
// 2x + 5

	mov eax, 10
	cvtsi2sd xmm1, eax
	divsd xmm0, xmm1
// (2x + 5) / 10

	mov eax, 1
	cvtsi2sd xmm1, eax
	minsd xmm0, xmm1
// min(y, 1)

	mov eax, 0
	cvtsi2sd xmm1, eax
	maxsd xmm0, xmm1
// max(y, 0)
	ret

.else
//windows version of assembly language

bsr_dword:
	bsr eax, ecx
	ret

//determine the gcd of (rcx, rdx): gcd(rcx, rdx) = gcd(rdx, rcx % rdx)
gcd_qword:
	mov rax, rcx
	or rdx, rdx
	jz jmp_ret
	mov rcx, rdx
	mov rdx, 0
	div rcx
// rax = quo, rdx = rem//
	jmp gcd_qword

gcd_long:
	mov rax, rcx
	or rdx, rdx
	jz jmp_ret
	mov rcx, rdx
	cqo
// Convert Quadword to Double Quadword, ie, Sign-extends the contents of RAX to RDX:RAX.
	idiv rcx
// rax = quo, rdx = rem//
	jmp gcd_long


//determine the gcd of (rcx, rdx): gcd(rcx, rdx) = gcd(rdx, rcx % rdx)
gcd_int:
	mov eax, ecx
	or edx, edx
	jz jmp_ret
	mov ecx, edx
	cdq
// Convert Doubleword to Quadword, ie, Sign-extends register EAX and saves the results in register pair EDX:EAX.
	idiv ecx
// eax = quo, edx = rem//
	jmp gcd_int


//determine the gcd of (rcx, rdx): gcd(rcx, rdx) = gcd(rdx, rcx % rdx)
gcd_dword:
	mov eax, ecx
	or edx, edx
	jz jmp_ret
	mov ecx, edx
	xor edx, edx
	div ecx
// eax = quo, edx = rem//
	jmp gcd_dword


stosb:
.ifdef _DEBUG
	mov rdi, rcx
	mov al, dl
	mov rcx, r8
	rep stosb
.else
	push rdi
	mov rdi, rcx
	mov al, dl
	mov rcx, r8
	rep stosb
	pop rdi
.endif
	ret

stosw:
.ifdef _DEBUG
	mov rdi, rcx
	mov ax, dx
	mov rcx, r8
	rep stosw
.else
	push rdi
	mov rdi, rcx
	mov ax, dx
	mov rcx, r8
	rep stosw
	pop rdi
.endif
	ret

stosd:
.ifdef _DEBUG
	mov rdi, rcx
	mov eax, edx
	mov rcx, r8
	rep stosd
.else
	push rdi
	mov rdi, rcx
	mov eax, edx
	mov rcx, r8
	rep stosd
	pop rdi
.endif
	ret

stosq:
.ifdef _DEBUG
    mov rdi, rcx
    mov rax, rdx
    mov rcx, r8
    rep stosq
.else
    push rdi
    mov rdi, rcx
    mov rax, rdx
    mov rcx, r8
    rep stosq
    pop rdi
.endif
    ret

scasd:
.ifdef _DEBUG
	mov rdi, rcx
	mov eax, edx
	mov rcx, r8
	repne scasd
	mov rax, rdi
.else
	push rdi

	mov rdi, rcx
	mov eax, edx
	mov rcx, r8
	repne scasd
	mov rax, rdi

	pop rdi
.endif
	ret

repe_scasd:
.ifdef _DEBUG
	mov rdi, rcx
	mov eax, edx
	mov rcx, r8
	repe scasd
	mov rax, rdi
.else
	push rdi

	mov rdi, rcx
	mov eax, edx
	mov rcx, r8
	repe scasd
	mov rax, rdi

	pop rdi
.endif
	ret

movsq:
.ifdef _DEBUG
	mov rdi, rcx
	mov rsi, rdx
	mov rcx, r8
	rep movsq
	mov rax, rdi
.else
	push rdi
	push rsi

	mov rdi, rcx
	mov rsi, rdx
	mov rcx, r8
	rep movsq
	mov rax, rdi

	pop rsi
	pop rdi
.endif
	ret

movsd:
.ifdef _DEBUG
    mov rdi, rcx
    mov rsi, rdx
    mov rcx, r8
    rep movsd
    mov rax, rdi
.else
    push rdi
    push rsi

    mov rdi, rcx
    mov rsi, rdx
    mov rcx, r8
    rep movsd
    mov rax, rdi

    pop rsi
    pop rdi
.endif
    ret

sum8args:
	mov rax, rcx
	add rax, rdx
	add rax, r8
	add rax, r9
	add rax, [rsp+40]
	add rax, [rsp+48]
	add rax, [rsp+56]
	add rax, [rsp+64]
	ret

relu:
	maxsd xmm0, [zero]
	ret

hard_sigmoid:
	mulsd xmm0, [one_fifth]
// 0.2x

	addsd xmm0, [half]
// 0.2x + 0.5

	minsd xmm0, [one]
// min(y, 1)

	maxsd xmm0, [zero]
// max(y, 0)
	ret
.endif


jmp_ret:
	ret

CalcSum_:
	cvtss2sd xmm0,xmm0
	addsd xmm0,xmm1

	cvtss2sd xmm2,xmm2
	addsd xmm0,xmm2
	addsd xmm0,xmm3

	cvtss2sd xmm4, dword [rsp+40]
	addsd xmm0, xmm4
	addsd xmm0, qword [rsp+48]
	ret

CalcDist_:
	cvtsi2sd xmm4,ecx
	subsd xmm1, xmm4
	mulsd xmm1, xmm1

	cvtsi2sd xmm5,r8
	subsd xmm3,xmm5
	mulsd xmm3,xmm3

	movss xmm0, dword [rsp+40]
	cvtss2sd xmm0,xmm0
	movsx eax, word ptr [rsp+48]
	cvtsi2sd xmm4,eax
	subsd xmm4,xmm0
	mulsd xmm4,xmm4

	addsd xmm1, xmm3
	addsd xmm4, xmm1
	sqrtsd xmm0,xmm4
	ret

//reference book: Apress.Modern.X86.Assembly.Language.Programming.32-bit.64-bit
//https://blog.csdn.net/celerychen2009/article/details/8934972
//https://stackoverflow.com/questions/40820814/relocation-r-x86-64-32s-against-bss-can-not-be-used-when-making-a-shared-obj
//https://stackoverflow.com/questions/6093547/what-do-r-x86-64-32s-and-r-x86-64-64-relocation-mean
//http://www.csee.umbc.edu/~chang/cs313.f04/nasmdoc/html/nasmdoc8.html//section-8.2
//https://eli.thegreenplace.net/2011/11/03/position-independent-code-pic-in-shared-libraries/
//https://www.nasm.us/xdoc/2.11.02/html/nasmdoc6.html//section-6.2.1
//https://blog.csdn.net/sivolin/article/details/41895701
//https://www.cnblogs.com/volva/p/11814998.html
//https://blog.csdn.net/roger_ranger/article/details/78854348
//http://sourceware.org/binutils/docs-2.17/as/index.html
//https://www.cnblogs.com/binsys/articles/1303927.html
//https://www.ibm.com/developerworks/cn/linux/l-gas-nasm.html
