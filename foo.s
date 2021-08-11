
;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include "compiler.s"

section .bss
malloc_pointer:
    resq 1

section .data
const_tbl:
MAKE_VOID
MAKE_NIL
MAKE_BOOL(1)
MAKE_BOOL(0)
MAKE_LITERAL_STRING 119,104,97,116,101,118,101,114
MAKE_LITERAL_SYMBOL(const_tbl+6)
MAKE_LITERAL_INT(0)
MAKE_LITERAL_INT(1)
MAKE_LITERAL_STRING 116,104,105,115,32,115,104,111,117,108,100,32,98,101,32,97,110,32,101,114,114,111,114,44,32,98,117,116,32,121,111,117,32,100,111,110,39,116,32,115,117,112,112,111,114,116,32,101,120,99,101,112,116,105,111,110,115
MAKE_LITERAL_CHAR(0)
MAKE_LITERAL_INT(5)
MAKE_LITERAL_FLOAT(5.5)
MAKE_LITERAL_CHAR(104)
MAKE_LITERAL_STRING 32,104,101,108,108,111,32,116,104,105,115,32,105,115,32,116,104,101,32,102,105,110,97,108,32,112,114,111,106,101,99,116
MAKE_LITERAL_VECTOR 
MAKE_LITERAL_VECTOR const_tbl+118
MAKE_LITERAL_INT(4)
MAKE_LITERAL_VECTOR const_tbl+118,const_tbl+205
MAKE_LITERAL_INT(6)
MAKE_LITERAL_VECTOR const_tbl+205,const_tbl+118,const_tbl+239
MAKE_LITERAL_INT(7)
MAKE_LITERAL_INT(8)
MAKE_LITERAL_INT(9)
MAKE_LITERAL_VECTOR const_tbl+118,const_tbl+239,const_tbl+281,const_tbl+290,const_tbl+299
MAKE_LITERAL_PAIR(const_tbl+118,const_tbl+1)
MAKE_LITERAL_PAIR(const_tbl+281,const_tbl+1)
MAKE_LITERAL_PAIR(const_tbl+239,const_tbl+374)
MAKE_LITERAL_PAIR(const_tbl+239,const_tbl+391)
MAKE_LITERAL_PAIR(const_tbl+239,const_tbl+408)
MAKE_LITERAL_STRING 104,101,108,108,111,116,104,105,115,105,115,116,104,101,102,105,110,97,108,112,114,111,106,101,99,116,49,50,51,52,53,54,55,56,57,49,48
MAKE_LITERAL_SYMBOL(const_tbl+442)
MAKE_LITERAL_INT(55)
MAKE_LITERAL_FLOAT(4.4)
MAKE_LITERAL_STRING 103,111,116,99,104,97
MAKE_LITERAL_CHAR(9)
MAKE_LITERAL_VECTOR const_tbl+497,const_tbl+506,const_tbl+515,const_tbl+2,const_tbl+4,const_tbl+530
MAKE_LITERAL_PAIR(const_tbl+530,const_tbl+1)
MAKE_LITERAL_PAIR(const_tbl+4,const_tbl+589)
MAKE_LITERAL_PAIR(const_tbl+2,const_tbl+606)
MAKE_LITERAL_PAIR(const_tbl+515,const_tbl+623)
MAKE_LITERAL_PAIR(const_tbl+506,const_tbl+640)
MAKE_LITERAL_PAIR(const_tbl+497,const_tbl+657)

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID const_tbl+0
%define SOB_NIL const_tbl+1
%define SOB_TRUE const_tbl+2
%define SOB_FALSE const_tbl+4

fvar_tbl:
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED
dq T_UNDEFINED

global main

section .text
main:
    ;; set up the heap
    mov rdi, GB(4)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push 0
    push qword SOB_NIL
    push qword T_UNDEFINED
    push rsp

    call code_fragment
    add rsp, 4*8
    ret

code_fragment:
    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we emulate the missing (define ...) expressions
    ;; for all the primitive procedures.
    MAKE_CLOSURE(rax, SOB_NIL, is_boolean)
    mov FVAR(0), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_float)
    mov FVAR(1), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_integer)
    mov FVAR(2), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_pair)
    mov FVAR(3), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_null)
    mov FVAR(4), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_char)
    mov FVAR(5), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_vector)
    mov FVAR(6), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_string)
    mov FVAR(7), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_procedure)
    mov FVAR(8), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_symbol)
    mov FVAR(9), rax
    MAKE_CLOSURE(rax, SOB_NIL, string_length)
    mov FVAR(10), rax
    MAKE_CLOSURE(rax, SOB_NIL, string_ref)
    mov FVAR(11), rax
    MAKE_CLOSURE(rax, SOB_NIL, string_set)
    mov FVAR(12), rax
    MAKE_CLOSURE(rax, SOB_NIL, make_string)
    mov FVAR(13), rax
    MAKE_CLOSURE(rax, SOB_NIL, vector_length)
    mov FVAR(14), rax
    MAKE_CLOSURE(rax, SOB_NIL, vector_ref)
    mov FVAR(15), rax
    MAKE_CLOSURE(rax, SOB_NIL, vector_set)
    mov FVAR(16), rax
    MAKE_CLOSURE(rax, SOB_NIL, make_vector)
    mov FVAR(17), rax
    MAKE_CLOSURE(rax, SOB_NIL, symbol_to_string)
    mov FVAR(18), rax
    MAKE_CLOSURE(rax, SOB_NIL, char_to_integer)
    mov FVAR(19), rax
    MAKE_CLOSURE(rax, SOB_NIL, integer_to_char)
    mov FVAR(20), rax
    MAKE_CLOSURE(rax, SOB_NIL, is_eq)
    mov FVAR(21), rax
    MAKE_CLOSURE(rax, SOB_NIL, bin_add)
    mov FVAR(22), rax
    MAKE_CLOSURE(rax, SOB_NIL, bin_mul)
    mov FVAR(23), rax
    MAKE_CLOSURE(rax, SOB_NIL, bin_sub)
    mov FVAR(24), rax
    MAKE_CLOSURE(rax, SOB_NIL, bin_div)
    mov FVAR(25), rax
    MAKE_CLOSURE(rax, SOB_NIL, bin_lt)
    mov FVAR(26), rax
    MAKE_CLOSURE(rax, SOB_NIL, bin_equ)
    mov FVAR(27), rax
    MAKE_CLOSURE(rax, SOB_NIL, car)
    mov FVAR(28), rax
    MAKE_CLOSURE(rax, SOB_NIL, cdr)
    mov FVAR(29), rax
    MAKE_CLOSURE(rax, SOB_NIL, set_car)
    mov FVAR(30), rax
    MAKE_CLOSURE(rax, SOB_NIL, set_cdr)
    mov FVAR(31), rax
    MAKE_CLOSURE(rax, SOB_NIL, cons)
    mov FVAR(32), rax
    MAKE_CLOSURE(rax, SOB_NIL, apply)
    mov FVAR(33), rax
 
mov rax, FVAR(32)
push rax
mov rax, FVAR(29)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(4)
push rax
push 4
MAKE_CLOSURE(rax, SOB_NIL, Lcode11)
jmp Lcont11

Lcode11:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env12:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env12, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm12
copy_parms_into_vector12:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector12,rcx

skip_copy_parm12:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode12)
jmp Lcont12

Lcode12:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list12

put_args_in_list12:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont12

loop12:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop12, rcx

cont12:
add r9, 8
mov qword[r9],r12
jmp continue12

add_empty_list12:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down12:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down12,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue12:
mov rax, qword[rbp+8*(4+0)]
push rax
mov rax, const_tbl+1
push rax
push 2
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env13:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env13, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm13
copy_parms_into_vector13:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector13,rcx

skip_copy_parm13:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode13)
jmp Lcont13

Lcode13:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 32
mov r9, qword[rbp+8*2]
mov rcx,3
mov r10,rcx

copy_env14:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env14, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm14
copy_parms_into_vector14:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector14,rcx

skip_copy_parm14:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode14)
jmp Lcont14

Lcode14:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse15 
;IF THEN
mov rax, qword[rbp+8*(4+0)]
jmp Lexit15 
;IF ELSE
Lelse15:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 40
mov r9, qword[rbp+8*2]
mov rcx,4
mov r10,rcx

copy_env16:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env16, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm16
copy_parms_into_vector16:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector16,rcx

skip_copy_parm16:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode16)
jmp Lcont16

Lcode16:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 48
mov r9, qword[rbp+8*2]
mov rcx,5
mov r10,rcx

copy_env17:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env17, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm17
copy_parms_into_vector17:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector17,rcx

skip_copy_parm17:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode17)
jmp Lcont17

Lcode17:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 4] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse18 
;IF THEN
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 4] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 4] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit18 
;IF ELSE
Lelse18:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 4] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 4] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 4] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit18: 
leave
ret

Lcont17:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
mov rax, qword[rbp+8*(4+0)]
mov rax, qword[rax] 
leave
ret

Lcont16:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit15: 
leave
ret

Lcont14:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
mov rax, qword[rbp+8*(4+0)]
mov rax, qword[rax] 
leave
ret

Lcont13:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont12:
leave
ret

Lcont11:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(34), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(27)
push rax
push 1
MAKE_CLOSURE(rax, SOB_NIL, Lcode21)
jmp Lcont21

Lcode21:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env22:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env22, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm22
copy_parms_into_vector22:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector22,rcx

skip_copy_parm22:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode22)
jmp Lcont22

Lcode22:
push rbp
mov rbp,rsp
mov rax, const_tbl+32
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont22:
leave
ret

Lcont21:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(39), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

MAKE_CLOSURE(rax, SOB_NIL, Lcode31)
jmp Lcont31

Lcode31:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list31

put_args_in_list31:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont31

loop31:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop31, rcx

cont31:
add r9, 8
mov qword[r9],r12
jmp continue31

add_empty_list31:
mov qword[rbp+3*8],1
sub rbp,8
sub rsp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down31:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down31,rcx

sub r12,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue31:
mov rax, qword[rbp+8*(4+0)]
leave
ret

Lcont31:
mov FVARLABEL(41), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(29)
push rax
mov rax, FVAR(3)
push rax
mov rax, FVAR(4)
push rax
push 3
MAKE_CLOSURE(rax, SOB_NIL, Lcode41)
jmp Lcont41

Lcode41:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env42:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env42, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm42
copy_parms_into_vector42:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector42,rcx

skip_copy_parm42:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode42)
jmp Lcont42

Lcode42:
push rbp
mov rbp,rsp
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx

 cmp rax, SOB_FALSE 
jne Lexit43 
cmp rax, SOB_FALSE 
jne Lexit43 
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse44 
;IF THEN
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 1
mov rax, FVAR(42)

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit44 
;IF ELSE
Lelse44:
mov rax, const_tbl+4
Lexit44: 
Lexit43: 
leave
ret

Lcont42:
leave
ret

Lcont41:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(42), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(22)
push rax
mov rax, FVAR(29)
push rax
mov rax, FVAR(3)
push rax
mov rax, FVAR(4)
push rax
push 4
MAKE_CLOSURE(rax, SOB_NIL, Lcode51)
jmp Lcont51

Lcode51:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env52:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env52, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm52
copy_parms_into_vector52:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector52,rcx

skip_copy_parm52:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode52)
jmp Lcont52

Lcode52:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
mov rax, const_tbl+23
push rax
push 2
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env53:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env53, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm53
copy_parms_into_vector53:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector53,rcx

skip_copy_parm53:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode53)
jmp Lcont53

Lcode53:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+1)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+1)], rax 
mov rax, SOB_VOID
;box' start
mov rax, const_tbl+32
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 32
mov r9, qword[rbp+8*2]
mov rcx,3
mov r10,rcx

copy_env54:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env54, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm54
copy_parms_into_vector54:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector54,rcx

skip_copy_parm54:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode54)
jmp Lcont54

Lcode54:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse55 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
jmp Lexit55 
;IF ELSE
Lelse55:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse56 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, const_tbl+41
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit56 
;IF ELSE
Lelse56:
mov rax, const_tbl+50
Lexit56: 
Lexit55: 
leave
ret

Lcont54:
push rax 
mov rax, qword[rbp+8*(4+1)]
pop qword [rax]
mov rax, SOB_VOID
mov rax, const_tbl+32
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 2
mov rax, qword[rbp+8*(4+1)]
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont53:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont52:
leave
ret

Lcont51:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(47), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(47)
push rax
mov rax, FVAR(27)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(13)
push rax
mov rax, FVAR(4)
push rax
push 5
MAKE_CLOSURE(rax, SOB_NIL, Lcode61)
jmp Lcont61

Lcode61:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env62:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env62, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm62
copy_parms_into_vector62:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector62,rcx

skip_copy_parm62:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode62)
jmp Lcont62

Lcode62:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,1
je add_empty_list62

put_args_in_list62:
mov r10,1
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont62

loop62:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop62, rcx

cont62:
add r9, 8
mov qword[r9],r12
jmp continue62

add_empty_list62:
mov qword[rbp+3*8],2
sub rbp,8
mov rcx,5
mov r12,rbp
add r12,8

shift_down62:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down62,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue62:
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse63 
;IF THEN
mov rax, const_tbl+116
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit63 
;IF ELSE
Lelse63:
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, const_tbl+41
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse64 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit64 
;IF ELSE
Lelse64:
mov rax, const_tbl+50
Lexit64: 
Lexit63: 
leave
ret

Lcont62:
leave
ret

Lcont61:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(13), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(4)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(17)
push rax
mov rax, FVAR(47)
push rax
push 4
MAKE_CLOSURE(rax, SOB_NIL, Lcode71)
jmp Lcont71

Lcode71:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env72:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env72, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm72
copy_parms_into_vector72:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector72,rcx

skip_copy_parm72:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode72)
jmp Lcont72

Lcode72:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,1
je add_empty_list72

put_args_in_list72:
mov r10,1
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont72

loop72:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop72, rcx

cont72:
add r9, 8
mov qword[r9],r12
jmp continue72

add_empty_list72:
mov qword[rbp+3*8],2
sub rbp,8
mov rcx,5
mov r12,rbp
add r12,8

shift_down72:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down72,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue72:
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse73 
;IF THEN
mov rax, const_tbl+32
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit73 
;IF ELSE
Lelse73:
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, const_tbl+41
push rax
push 2
mov rax, FVAR(27)

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse74 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit74 
;IF ELSE
Lelse74:
mov rax, const_tbl+50
Lexit74: 
Lexit73: 
leave
ret

Lcont72:
leave
ret

Lcont71:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(17), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(21)
push rax
push 1
MAKE_CLOSURE(rax, SOB_NIL, Lcode81)
jmp Lcont81

Lcode81:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env82:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env82, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm82
copy_parms_into_vector82:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector82,rcx

skip_copy_parm82:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode82)
jmp Lcont82

Lcode82:
push rbp
mov rbp,rsp
;IF TEST
mov rax, const_tbl+2
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse83 
;IF THEN
mov rax, const_tbl+4
jmp Lexit83 
;IF ELSE
Lelse83:
mov rax, const_tbl+2
Lexit83: 
leave
ret

Lcont82:
leave
ret

Lcont81:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(64), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(2)
push rax
mov rax, FVAR(1)
push rax
push 2
MAKE_CLOSURE(rax, SOB_NIL, Lcode91)
jmp Lcont91

Lcode91:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env92:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env92, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm92
copy_parms_into_vector92:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector92,rcx

skip_copy_parm92:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode92)
jmp Lcont92

Lcode92:
push rbp
mov rbp,rsp
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx

 cmp rax, SOB_FALSE 
jne Lexit93 
cmp rax, SOB_FALSE 
jne Lexit93 
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit93: 
leave
ret

Lcont92:
leave
ret

Lcont91:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(66), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(29)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(33)
push rax
mov rax, FVAR(32)
push rax
mov rax, FVAR(4)
push rax
push 5
MAKE_CLOSURE(rax, SOB_NIL, Lcode101)
jmp Lcont101

Lcode101:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env102:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env102, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm102
copy_parms_into_vector102:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector102,rcx

skip_copy_parm102:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode102)
jmp Lcont102

Lcode102:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,2
je add_empty_list102

put_args_in_list102:
mov r10,2
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont102

loop102:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop102, rcx

cont102:
add r9, 8
mov qword[r9],r12
jmp continue102

add_empty_list102:
mov qword[rbp+3*8],3
sub rbp,8
mov rcx,6
mov r12,rbp
add r12,8

shift_down102:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down102,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue102:
;IF TEST
mov rax, qword[rbp+8*(4+2)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse103 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env108:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env108, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm108
copy_parms_into_vector108:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector108,rcx

skip_copy_parm108:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode108)
jmp Lcont108

Lcode108:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 32
mov r9, qword[rbp+8*2]
mov rcx,3
mov r10,rcx

copy_env109:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env109, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm109
copy_parms_into_vector109:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector109,rcx

skip_copy_parm109:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode109)
jmp Lcont109

Lcode109:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 40
mov r9, qword[rbp+8*2]
mov rcx,4
mov r10,rcx

copy_env1010:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env1010, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm1010
copy_parms_into_vector1010:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector1010,rcx

skip_copy_parm1010:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode1010)
jmp Lcont1010

Lcode1010:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse1011 
;IF THEN
mov rax, const_tbl+1
jmp Lexit1011 
;IF ELSE
Lelse1011:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit1011: 
leave
ret

Lcont1010:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 1
mov rax, qword[rbp+8*(4+0)]
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont109:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont108:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit103 
;IF ELSE
Lelse103:
mov rax, qword[rbp+8*(4+2)]
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
push 2
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env104:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env104, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm104
copy_parms_into_vector104:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector104,rcx

skip_copy_parm104:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode104)
jmp Lcont104

Lcode104:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 32
mov r9, qword[rbp+8*2]
mov rcx,3
mov r10,rcx

copy_env105:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env105, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm105
copy_parms_into_vector105:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector105,rcx

skip_copy_parm105:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode105)
jmp Lcont105

Lcode105:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 40
mov r9, qword[rbp+8*2]
mov rcx,4
mov r10,rcx

copy_env106:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env106, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm106
copy_parms_into_vector106:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector106,rcx

skip_copy_parm106:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode106)
jmp Lcont106

Lcode106:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse107 
;IF THEN
mov rax, const_tbl+1
jmp Lexit107 
;IF ELSE
Lelse107:
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 4] 
push rax
push 2
mov rax, FVAR(69)

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 3] 
push rax
push 2
mov rax, FVAR(69)

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
push rax
push 3
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 3] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit107: 
leave
ret

Lcont106:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 2
mov rax, qword[rbp+8*(4+0)]
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont105:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont104:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit103: 
leave
ret

Lcont102:
leave
ret

Lcont101:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(69), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(22)
push rax
mov rax, FVAR(47)
push rax
mov rax, FVAR(17)
push rax
mov rax, FVAR(29)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(3)
push rax
mov rax, FVAR(4)
push rax
push 7
MAKE_CLOSURE(rax, SOB_NIL, Lcode111)
jmp Lcont111

Lcode111:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env112:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env112, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm112
copy_parms_into_vector112:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector112,rcx

skip_copy_parm112:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode112)
jmp Lcont112

Lcode112:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env113:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env113, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm113
copy_parms_into_vector113:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector113,rcx

skip_copy_parm113:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode113)
jmp Lcont113

Lcode113:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 32
mov r9, qword[rbp+8*2]
mov rcx,3
mov r10,rcx

copy_env114:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env114, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm114
copy_parms_into_vector114:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector114,rcx

skip_copy_parm114:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode114)
jmp Lcont114

Lcode114:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse115 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
jmp Lexit115 
;IF ELSE
Lelse115:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse116 
;IF THEN
mov rax, qword[rbp+8*(4+2)]
push rax
mov rax, const_tbl+41
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 6] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+2)]
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
push 3
mov rax, FVAR(16)

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 3
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(6)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit116 
;IF ELSE
Lelse116:
mov rax, const_tbl+50
Lexit116: 
Lexit115: 
leave
ret

Lcont114:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
mov rax, const_tbl+32
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 5] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 3
mov rax, qword[rbp+8*(4+0)]
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(6)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont113:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont112:
leave
ret

Lcont111:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(77), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(24)
push rax
mov rax, FVAR(14)
push rax
mov rax, FVAR(32)
push rax
mov rax, FVAR(15)
push rax
mov rax, FVAR(26)
push rax
push 5
MAKE_CLOSURE(rax, SOB_NIL, Lcode121)
jmp Lcont121

Lcode121:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env122:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env122, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm122
copy_parms_into_vector122:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector122,rcx

skip_copy_parm122:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode122)
jmp Lcont122

Lcode122:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env123:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env123, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm123
copy_parms_into_vector123:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector123,rcx

skip_copy_parm123:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode123)
jmp Lcont123

Lcode123:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 32
mov r9, qword[rbp+8*2]
mov rcx,3
mov r10,rcx

copy_env124:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env124, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm124
copy_parms_into_vector124:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector124,rcx

skip_copy_parm124:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode124)
jmp Lcont124

Lcode124:
push rbp
mov rbp,rsp
;IF TEST
mov rax, const_tbl+32
push rax
mov rax, qword[rbp+8*(4+2)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse125 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
jmp Lexit125 
;IF ELSE
Lelse125:
mov rax, const_tbl+41
push rax
mov rax, qword[rbp+8*(4+2)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword[rbp+8*(4+2)]
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 3
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(6)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit125: 
leave
ret

Lcont124:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
mov rax, const_tbl+41
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, const_tbl+1
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 3
mov rax, qword[rbp+8*(4+0)]
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(6)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont123:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont122:
leave
ret

Lcont121:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(86), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(77)
push rax
push 1
MAKE_CLOSURE(rax, SOB_NIL, Lcode131)
jmp Lcont131

Lcode131:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env132:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env132, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm132
copy_parms_into_vector132:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector132,rcx

skip_copy_parm132:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode132)
jmp Lcont132

Lcode132:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list132

put_args_in_list132:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont132

loop132:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop132, rcx

cont132:
add r9, 8
mov qword[r9],r12
jmp continue132

add_empty_list132:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down132:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down132,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue132:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont132:
leave
ret

Lcont131:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(92), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(29)
push rax
mov rax, FVAR(33)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(22)
push rax
mov rax, FVAR(4)
push rax
push 5
MAKE_CLOSURE(rax, SOB_NIL, Lcode141)
jmp Lcont141

Lcode141:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env142:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env142, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm142
copy_parms_into_vector142:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector142,rcx

skip_copy_parm142:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode142)
jmp Lcont142

Lcode142:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env143:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env143, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm143
copy_parms_into_vector143:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector143,rcx

skip_copy_parm143:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode143)
jmp Lcont143

Lcode143:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list143

put_args_in_list143:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont143

loop143:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop143, rcx

cont143:
add r9, 8
mov qword[r9],r12
jmp continue143

add_empty_list143:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down143:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down143,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue143:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse144 
;IF THEN
mov rax, const_tbl+32
jmp Lexit144 
;IF ELSE
Lelse144:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit144: 
leave
ret

Lcont143:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
mov rax, qword[rbp+8*(4+0)]
mov rax, qword[rax] 
leave
ret

Lcont142:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont141:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(22), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(29)
push rax
mov rax, FVAR(33)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(23)
push rax
mov rax, FVAR(4)
push rax
push 5
MAKE_CLOSURE(rax, SOB_NIL, Lcode151)
jmp Lcont151

Lcode151:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env152:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env152, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm152
copy_parms_into_vector152:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector152,rcx

skip_copy_parm152:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode152)
jmp Lcont152

Lcode152:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env153:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env153, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm153
copy_parms_into_vector153:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector153,rcx

skip_copy_parm153:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode153)
jmp Lcont153

Lcode153:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list153

put_args_in_list153:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont153

loop153:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop153, rcx

cont153:
add r9, 8
mov qword[r9],r12
jmp continue153

add_empty_list153:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down153:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down153,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue153:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse154 
;IF THEN
mov rax, const_tbl+41
jmp Lexit154 
;IF ELSE
Lelse154:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit154: 
leave
ret

Lcont153:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
mov rax, qword[rbp+8*(4+0)]
mov rax, qword[rax] 
leave
ret

Lcont152:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont151:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(23), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(29)
push rax
mov rax, FVAR(47)
push rax
mov rax, FVAR(33)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(22)
push rax
mov rax, FVAR(24)
push rax
mov rax, FVAR(4)
push rax
push 7
MAKE_CLOSURE(rax, SOB_NIL, Lcode161)
jmp Lcont161

Lcode161:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env162:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env162, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm162
copy_parms_into_vector162:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector162,rcx

skip_copy_parm162:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode162)
jmp Lcont162

Lcode162:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env163:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env163, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm163
copy_parms_into_vector163:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector163,rcx

skip_copy_parm163:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode163)
jmp Lcont163

Lcode163:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list163

put_args_in_list163:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont163

loop163:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop163, rcx

cont163:
add r9, 8
mov qword[r9],r12
jmp continue163

add_empty_list163:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down163:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down163,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue163:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse164 
;IF THEN
mov rax, const_tbl+32
jmp Lexit164 
;IF ELSE
Lelse164:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 6] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit164: 
leave
ret

Lcont163:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env165:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env165, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm165
copy_parms_into_vector165:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector165,rcx

skip_copy_parm165:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode165)
jmp Lcont165

Lcode165:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list165

put_args_in_list165:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont165

loop165:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop165, rcx

cont165:
add r9, 8
mov qword[r9],r12
jmp continue165

add_empty_list165:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down165:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down165,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue165:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse166 
;IF THEN
mov rax, const_tbl+50
jmp Lexit166 
;IF ELSE
Lelse166:
;IF TEST
mov rax, const_tbl+41
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 5] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, FVAR(27)

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse167 
;IF THEN
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, const_tbl+32
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit167 
;IF ELSE
Lelse167:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 6] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit167: 
Lexit166: 
leave
ret

Lcont165:
leave
ret

Lcont162:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont161:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(24), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(29)
push rax
mov rax, FVAR(47)
push rax
mov rax, FVAR(33)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(23)
push rax
mov rax, FVAR(25)
push rax
mov rax, FVAR(4)
push rax
push 7
MAKE_CLOSURE(rax, SOB_NIL, Lcode171)
jmp Lcont171

Lcode171:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env172:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env172, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm172
copy_parms_into_vector172:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector172,rcx

skip_copy_parm172:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode172)
jmp Lcont172

Lcode172:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list172

put_args_in_list172:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont172

loop172:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop172, rcx

cont172:
add r9, 8
mov qword[r9],r12
jmp continue172

add_empty_list172:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down172:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down172,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue172:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse173 
;IF THEN
mov rax, const_tbl+50
jmp Lexit173 
;IF ELSE
Lelse173:
;IF TEST
mov rax, const_tbl+41
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 5] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, FVAR(27)

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse174 
;IF THEN
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, const_tbl+41
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit174 
;IF ELSE
Lelse174:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 6] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 2] 
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit174: 
Lexit173: 
leave
ret

Lcont172:
leave
ret

Lcont171:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(25), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(29)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(27)
push rax
mov rax, FVAR(4)
push rax
push 4
MAKE_CLOSURE(rax, SOB_NIL, Lcode181)
jmp Lcont181

Lcode181:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env182:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env182, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm182
copy_parms_into_vector182:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector182,rcx

skip_copy_parm182:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode182)
jmp Lcont182

Lcode182:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env183:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env183, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm183
copy_parms_into_vector183:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector183,rcx

skip_copy_parm183:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode183)
jmp Lcont183

Lcode183:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse184 
;IF THEN
mov rax, const_tbl+2
jmp Lexit184 
;IF ELSE
Lelse184:
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse185 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit185 
;IF ELSE
Lelse185:
mov rax, const_tbl+4
Lexit185: 
Lexit184: 
leave
ret

Lcont183:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env186:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env186, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm186
copy_parms_into_vector186:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector186,rcx

skip_copy_parm186:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode186)
jmp Lcont186

Lcode186:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list186

put_args_in_list186:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont186

loop186:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop186, rcx

cont186:
add r9, 8
mov qword[r9],r12
jmp continue186

add_empty_list186:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down186:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down186,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue186:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse187 
;IF THEN
mov rax, const_tbl+50
jmp Lexit187 
;IF ELSE
Lelse187:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit187: 
leave
ret

Lcont186:
leave
ret

Lcont182:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont181:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(27), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(29)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(26)
push rax
mov rax, FVAR(4)
push rax
push 4
MAKE_CLOSURE(rax, SOB_NIL, Lcode191)
jmp Lcont191

Lcode191:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env192:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env192, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm192
copy_parms_into_vector192:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector192,rcx

skip_copy_parm192:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode192)
jmp Lcont192

Lcode192:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env193:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env193, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm193
copy_parms_into_vector193:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector193,rcx

skip_copy_parm193:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode193)
jmp Lcont193

Lcode193:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse194 
;IF THEN
mov rax, const_tbl+2
jmp Lexit194 
;IF ELSE
Lelse194:
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse195 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit195 
;IF ELSE
Lelse195:
mov rax, const_tbl+4
Lexit195: 
Lexit194: 
leave
ret

Lcont193:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env196:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env196, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm196
copy_parms_into_vector196:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector196,rcx

skip_copy_parm196:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode196)
jmp Lcont196

Lcode196:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list196

put_args_in_list196:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont196

loop196:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop196, rcx

cont196:
add r9, 8
mov qword[r9],r12
jmp continue196

add_empty_list196:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down196:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down196,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue196:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse197 
;IF THEN
mov rax, const_tbl+50
jmp Lexit197 
;IF ELSE
Lelse197:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit197: 
leave
ret

Lcont196:
leave
ret

Lcont192:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont191:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(26), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(29)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(64)
push rax
mov rax, FVAR(27)
push rax
mov rax, FVAR(26)
push rax
mov rax, FVAR(4)
push rax
push 6
MAKE_CLOSURE(rax, SOB_NIL, Lcode201)
jmp Lcont201

Lcode201:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env202:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env202, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm202
copy_parms_into_vector202:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector202,rcx

skip_copy_parm202:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode202)
jmp Lcont202

Lcode202:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env203:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env203, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm203
copy_parms_into_vector203:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector203,rcx

skip_copy_parm203:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode203)
jmp Lcont203

Lcode203:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse204 
;IF THEN
mov rax, const_tbl+2
jmp Lexit204 
;IF ELSE
Lelse204:
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx

 cmp rax, SOB_FALSE 
jne Lexit206 
cmp rax, SOB_FALSE 
jne Lexit206 
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
Lexit206: 
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse205 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 5] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit205 
;IF ELSE
Lelse205:
mov rax, const_tbl+4
Lexit205: 
Lexit204: 
leave
ret

Lcont203:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env207:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env207, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm207
copy_parms_into_vector207:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector207,rcx

skip_copy_parm207:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode207)
jmp Lcont207

Lcode207:
push rbp
mov rbp,rsp
mov r9,[rbp+3*8]
cmp r9,0
je add_empty_list207

put_args_in_list207:
mov r10,0
sub r9,r10
mov rcx,r9
dec rcx
mov r9,[rbp+3*8]
add r9,3
shl r9,3
add r9,rbp
mov r11, qword[r9]
MAKE_PAIR(r15,r11,SOB_NIL)
mov r12,r15
sub r9, 8
cmp rcx, 0
je cont207

loop207:
mov r11, qword[r9]
MAKE_PAIR(r15,r11,r12)
mov r12,r15
sub r9, 8
loop loop207, rcx

cont207:
add r9, 8
mov qword[r9],r12
jmp continue207

add_empty_list207:
mov qword[rbp+3*8],1
sub rbp,8
mov rcx,4
mov r12,rbp
add r12,8

shift_down207:
mov r8,qword[r12]
sub r12,8
mov qword[r12],r8
add r12,16
loop shift_down207,rcx

sub r12,8
sub rsp,8
mov r10, SOB_NIL 
mov qword[r12],r10
continue207:
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse208 
;IF THEN
mov rax, const_tbl+50
jmp Lexit208 
;IF ELSE
Lelse208:
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 5] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit208: 
leave
ret

Lcont207:
leave
ret

Lcont202:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont201:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(134), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, FVAR(24)
push rax
mov rax, FVAR(19)
push rax
mov rax, FVAR(29)
push rax
mov rax, FVAR(28)
push rax
mov rax, FVAR(21)
push rax
mov rax, FVAR(6)
push rax
mov rax, FVAR(7)
push rax
mov rax, FVAR(5)
push rax
mov rax, FVAR(3)
push rax
mov rax, FVAR(1)
push rax
mov rax, FVAR(2)
push rax
mov rax, FVAR(14)
push rax
mov rax, FVAR(15)
push rax
mov rax, FVAR(11)
push rax
mov rax, FVAR(10)
push rax
mov rax, FVAR(64)
push rax
mov rax, FVAR(27)
push rax
mov rax, FVAR(26)
push rax
push 18
MAKE_CLOSURE(rax, SOB_NIL, Lcode211)
jmp Lcont211

Lcode211:
push rbp
mov rbp,rsp
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env212:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env212, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm212
copy_parms_into_vector212:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector212,rcx

skip_copy_parm212:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode212)
jmp Lcont212

Lcode212:
push rbp
mov rbp,rsp
mov rax, const_tbl+23
push rax
push 1
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env213:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env213, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm213
copy_parms_into_vector213:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector213,rcx

skip_copy_parm213:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode213)
jmp Lcont213

Lcode213:
push rbp
mov rbp,rsp
;box' start
mov rax, qword[rbp+8*(4+0)]
MALLOC r8, 8 

                mov [r8], rax 

                mov rax,r8 
;box' end
mov qword[rbp+8*(4+0)], rax 
mov rax, SOB_VOID
MALLOC r8, 32
mov r9, qword[rbp+8*2]
mov rcx,3
mov r10,rcx

copy_env214:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env214, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm214
copy_parms_into_vector214:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector214,rcx

skip_copy_parm214:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode214)
jmp Lcont214

Lcode214:
push rbp
mov rbp,rsp
;IF TEST
mov rax, const_tbl+32
push rax
mov rax, qword[rbp+8*(4+3)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse215 
;IF THEN
mov rax, const_tbl+2
jmp Lexit215 
;IF ELSE
Lelse215:
;IF TEST
mov rax, qword[rbp+8*(4+3)]
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
push 2
mov rax, qword[rbp+8*(4+2)]

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+3)]
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword[rbp+8*(4+2)]

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, FVAR(141)

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse216 
;IF THEN
mov rax, const_tbl+41
push rax
mov rax, qword[rbp+8*(4+3)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 2] 
mov rax, qword [rax + 8 * 17] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+2)]
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 4
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(7)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
jmp Lexit216 
;IF ELSE
Lelse216:
mov rax, const_tbl+4
Lexit216: 
Lexit215: 
leave
ret

Lcont214:
push rax 
mov rax, qword[rbp+8*(4+0)]
pop qword [rax]
mov rax, SOB_VOID
;IF TEST
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 2] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse217 
;IF THEN
mov rax, const_tbl+4
jmp Lexit217 
;IF ELSE
Lelse217:
mov rax, const_tbl+41
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 3] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 17] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 2] 
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 1] 
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 
push rax
push 4
mov rax, qword[rbp+8*(4+0)]
mov rax, qword[rax] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(7)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit217: 
leave
ret

Lcont213:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont212:
push rax
push 1
MALLOC r8, 16
mov r9, qword[rbp+8*2]
mov rcx,1
mov r10,rcx

copy_env218:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env218, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm218
copy_parms_into_vector218:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector218,rcx

skip_copy_parm218:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode218)
jmp Lcont218

Lcode218:
push rbp
mov rbp,rsp
MALLOC r8, 24
mov r9, qword[rbp+8*2]
mov rcx,2
mov r10,rcx

copy_env219:
dec rcx
mov r11,qword[r9+rcx*8]
inc rcx
mov qword[r8+r10*8],r11
dec r10
loop copy_env219, rcx

mov rax,qword[rbp+3*8]
mov r11,8
mul r11
MALLOC r13,rax
mov rcx,qword[rbp+3*8]
mov r11,4
mov r12,0

cmp rcx,0
je skip_copy_parm219
copy_parms_into_vector219:
mov r10,qword[rbp+r11*8]
mov qword[r13+r12*8],r10
inc r12
inc r11
loop copy_parms_into_vector219,rcx

skip_copy_parm219:
mov qword[r8],r13
MAKE_CLOSURE(rax, r8, Lcode219)
jmp Lcont219

Lcode219:
push rbp
mov rbp,rsp
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 7] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2122 
;IF THEN
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 7] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2123 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
jmp Lexit2123 
;IF ELSE
Lelse2123:
mov rax, const_tbl+4
Lexit2123: 
jmp Lexit2122 
;IF ELSE
Lelse2122:
mov rax, const_tbl+4
Lexit2122: 

 cmp rax, SOB_FALSE 
jne Lexit2110 
cmp rax, SOB_FALSE 
jne Lexit2110 
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 8] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2111 
;IF THEN
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 8] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2112 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
jmp Lexit2112 
;IF ELSE
Lelse2112:
mov rax, const_tbl+4
Lexit2112: 
jmp Lexit2111 
;IF ELSE
Lelse2111:
mov rax, const_tbl+4
Lexit2111: 
cmp rax, SOB_FALSE 
jne Lexit2110 
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 9] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2113 
;IF THEN
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 9] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2114 
;IF THEN
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 14] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 14] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, FVAR(141)

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2115 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 15] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 15] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, FVAR(141)

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
jmp Lexit2115 
;IF ELSE
Lelse2115:
mov rax, const_tbl+4
Lexit2115: 
jmp Lexit2114 
;IF ELSE
Lelse2114:
mov rax, const_tbl+4
Lexit2114: 
jmp Lexit2113 
;IF ELSE
Lelse2113:
mov rax, const_tbl+4
Lexit2113: 
cmp rax, SOB_FALSE 
jne Lexit2110 
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 10] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2116 
;IF THEN
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 10] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2117 
;IF THEN
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 16] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 16] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 1] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
jmp Lexit2117 
;IF ELSE
Lelse2117:
mov rax, const_tbl+4
Lexit2117: 
jmp Lexit2116 
;IF ELSE
Lelse2116:
mov rax, const_tbl+4
Lexit2116: 
cmp rax, SOB_FALSE 
jne Lexit2110 
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 11] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2118 
;IF THEN
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 11] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2119 
;IF THEN
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 3] 
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 4] 
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 4
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
jmp Lexit2119 
;IF ELSE
Lelse2119:
mov rax, const_tbl+4
Lexit2119: 
jmp Lexit2118 
;IF ELSE
Lelse2118:
mov rax, const_tbl+4
Lexit2118: 
cmp rax, SOB_FALSE 
jne Lexit2110 
;IF TEST
mov rax, qword[rbp+8*(4+0)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 12] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2120 
;IF THEN
;IF TEST
mov rax, qword[rbp+8*(4+1)]
push rax
push 1
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 12] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
cmp rax, SOB_FALSE 
je Lelse2121 
;IF THEN
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 6] 
push rax
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 5] 
push rax
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 4
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 0] 
mov rax, qword [rax + 8 * 0] 

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
jmp Lexit2121 
;IF ELSE
Lelse2121:
mov rax, const_tbl+4
Lexit2121: 
jmp Lexit2120 
;IF ELSE
Lelse2120:
mov rax, const_tbl+4
Lexit2120: 
cmp rax, SOB_FALSE 
jne Lexit2110 
mov rax, qword[rbp+8*(4+1)]
push rax
mov rax, qword[rbp+8*(4+0)]
push rax
push 2
mov rax, qword [rbp + 8 * 2] 
mov rax, qword [rax + 8 * 1] 
mov rax, qword [rax + 8 * 13] 

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(5)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
Lexit2110: 
leave
ret

Lcont219:
leave
ret

Lcont218:

CLOSURE_ENV rcx ,rax
push rcx
push qword[rbp+8]
mov r15,qword[rbp]
SHIFT_FRAME(4)
mov rbp,r15
CLOSURE_CODE rcx ,rax
jmp rcx
leave
ret

Lcont211:

CLOSURE_ENV rcx ,rax
push rcx
CLOSURE_CODE rcx ,rax
call rcx
add rsp , 8*1
pop rbx
shl rbx , 3
add rsp , rbx
mov FVARLABEL(141), rax 
mov rax, SOB_VOID 

    call write_sob_if_not_void

mov rax, const_tbl+118

    call write_sob_if_not_void

mov rax, const_tbl+127

    call write_sob_if_not_void

mov rax, const_tbl+2

    call write_sob_if_not_void

mov rax, const_tbl+4

    call write_sob_if_not_void

mov rax, const_tbl+136

    call write_sob_if_not_void

mov rax, const_tbl+138

    call write_sob_if_not_void

mov rax, const_tbl+179

    call write_sob_if_not_void

mov rax, const_tbl+188

    call write_sob_if_not_void

mov rax, const_tbl+214

    call write_sob_if_not_void

mov rax, const_tbl+248

    call write_sob_if_not_void

mov rax, const_tbl+308

    call write_sob_if_not_void

mov rax, const_tbl+1

    call write_sob_if_not_void

mov rax, const_tbl+357

    call write_sob_if_not_void

mov rax, const_tbl+391

    call write_sob_if_not_void

mov rax, const_tbl+425

    call write_sob_if_not_void

mov rax, const_tbl+488

    call write_sob_if_not_void

mov rax, const_tbl+532

    call write_sob_if_not_void

mov rax, const_tbl+674

    call write_sob_if_not_void
ret
is_boolean:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_BOOL
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

is_float:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_FLOAT
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

is_integer:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_INTEGER
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

is_pair:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_PAIR
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

is_null:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_NIL
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

is_char:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_CHAR
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

is_vector:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_VECTOR
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

is_string:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_STRING
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

is_procedure:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_CLOSURE
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

is_symbol:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    mov sil, byte [rsi]

    cmp sil, T_SYMBOL
    jne .wrong_type
    mov rax, SOB_TRUE
    jmp .return

.wrong_type:
    mov rax, SOB_FALSE
.return:
    leave
    ret

string_length:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    STRING_LENGTH rsi, rsi
    MAKE_INT(rax, rsi)

    leave
    ret

string_ref:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0) 
    STRING_ELEMENTS rsi, rsi
    mov rdi, PVAR(1)
    INT_VAL rdi, rdi
    shl rdi, 0
    add rsi, rdi

    mov sil, byte [rsi]
    MAKE_CHAR(rax, sil)

    leave
    ret

string_set:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0) 
    STRING_ELEMENTS rsi, rsi
    mov rdi, PVAR(1)
    INT_VAL rdi, rdi
    shl rdi, 0
    add rsi, rdi

    mov rax, PVAR(2)
    CHAR_VAL rax, rax
    mov byte [rsi], al
    mov rax, SOB_VOID

    leave
    ret

make_string:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    mov rdi, PVAR(1)
    CHAR_VAL rdi, rdi
    and rdi, 255

    MAKE_STRING rax, rsi, dil

    leave
    ret

vector_length:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0)
    VECTOR_LENGTH rsi, rsi
    MAKE_INT(rax, rsi)

    leave
    ret

vector_ref:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0) 
    VECTOR_ELEMENTS rsi, rsi
    mov rdi, PVAR(1)
    INT_VAL rdi, rdi
    shl rdi, 3
    add rsi, rdi

    mov rax, [rsi]

    leave
    ret

vector_set:
    push rbp
    mov rbp, rsp

    mov rsi, PVAR(0) 
    VECTOR_ELEMENTS rsi, rsi
    mov rdi, PVAR(1)
    INT_VAL rdi, rdi
    shl rdi, 3
    add rsi, rdi

    mov rdi, PVAR(2)
    mov [rsi], rdi
    mov rax, SOB_VOID

    leave
    ret

make_vector:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    mov rdi, PVAR(1)
    

    MAKE_VECTOR rax, rsi, rdi

    leave
    ret

symbol_to_string:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    SYMBOL_VAL rsi, rsi
    
    STRING_LENGTH rcx, rsi
    STRING_ELEMENTS rdi, rsi

    push rcx
    push rdi

    mov dil, byte [rdi]
    MAKE_CHAR(rax, dil)
    push rax
    MAKE_INT(rax, rcx)
    push rax
    push 2
    push SOB_NIL
    call make_string
    add rsp, 4*8

    STRING_ELEMENTS rsi, rax

    pop rdi
    pop rcx

.loop:
    cmp rcx, 0
    je .end
    lea r8, [rdi+rcx]
    lea r9, [rsi+rcx]

    mov bl, byte [r8]
    mov byte [r9], bl
    
    dec rcx
.end:

    leave
    ret

char_to_integer:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    CHAR_VAL rsi, rsi
    and rsi, 255
    MAKE_INT(rax, rsi)

    leave
    ret

integer_to_char:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    and rsi, 255
    MAKE_CHAR(rax, sil)

    leave
    ret

is_eq:
    push rbp
    mov rbp, rsp

    
    mov rsi, PVAR(0)
    mov rdi, PVAR(1)
    cmp rsi, rdi
    je .true
    mov rax, SOB_FALSE
    jmp .return

.true:
    mov rax, SOB_TRUE

.return:
    leave
    ret

bin_add:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    addsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    leave
    ret

bin_mul:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    mulsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    leave
    ret

bin_sub:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    subsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    leave
    ret

bin_div:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    divsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    leave
    ret

bin_lt:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    cmpltsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    INT_VAL rsi, rax
    cmp rsi, 0
    je .return_false
    mov rax, SOB_TRUE
    jmp .final_return

.return_false:
    mov rax, SOB_FALSE

.final_return:


    leave
    ret

bin_equ:
    push rbp
    mov rbp, rsp

    mov r8, 0

    mov rsi, PVAR(0)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .test_next
    or r8, 1

.test_next:

    mov rsi, PVAR(1)
    push rsi
    push 1
    push SOB_NIL
    call is_float
    add rsp, 3*WORD_SIZE 


    cmp rax, SOB_TRUE
    je .load_numbers
    or r8, 2

.load_numbers:
    push r8

    shr r8, 1
    jc .first_arg_int
    mov rsi, PVAR(0)
    FLOAT_VAL rsi, rsi 
    movq xmm0, rsi
    jmp .load_next_float

.first_arg_int:
    mov rsi, PVAR(0)
    INT_VAL rsi, rsi
    cvtsi2sd xmm0, rsi

.load_next_float:
    shr r8, 1
    jc .second_arg_int
    mov rsi, PVAR(1)
    FLOAT_VAL rsi, rsi
    movq xmm1, rsi
    jmp .perform_float_op

.second_arg_int:
    mov rsi, PVAR(1)
    INT_VAL rsi, rsi
    cvtsi2sd xmm1, rsi

.perform_float_op:
    cmpeqsd xmm0, xmm1

    pop r8
    cmp r8, 3
    jne .return_float

    cvttsd2si rsi, xmm0
    MAKE_INT(rax, rsi)
    jmp .return

.return_float:
    movq rsi, xmm0
    MAKE_FLOAT(rax, rsi)

.return:

    INT_VAL rsi, rax
    cmp rsi, 0
    je .return_false
    mov rax, SOB_TRUE
    jmp .final_return

.return_false:
    mov rax, SOB_FALSE

.final_return:


    leave
    ret


car:
    push rbp
    mov rbp, rsp

    mov rax,[rbp+4*8]
    CAR rax, rax

    leave 
    ret

cdr:
    push rbp
    mov rbp, rsp

    mov rax,[rbp+4*8]
    CDR rax, rax

    leave 
    ret
set_car:

    push rbp
    mov rbp, rsp

    mov r12,qword[rbp+4*8]
    mov rbx,qword[rbp+5*8]
   
    mov qword [r12+TYPE_SIZE],rbx

    mov rax,SOB_VOID

    leave
    ret

set_cdr:

    push rbp
    mov rbp, rsp

    mov r12,qword[rbp+4*8]
    mov rbx,qword[rbp+5*8]
   
    mov qword [r12+TYPE_SIZE+WORD_SIZE],rbx

    mov rax,SOB_VOID

    leave
    ret

cons:

    push rbp
    mov rbp, rsp

    mov r12,qword[rbp+4*8]
    mov rbx,qword[rbp+5*8]
    MAKE_PAIR(rax,r12,rbx)

    leave
    ret


apply:
    push rbp
    mov rbp, rsp

    mov r12,qword[rbp+3*8] ;num of args
    mov r9,0
    add r12,3 ;add ret+frame+n
    mov r13,r12
    mov rax,8 
    mul r12 
    mov rax,qword[rbp+rax] ;list is now in rax
    
    cmp rax,SOB_NIL
    je continueapply


    push_args:
        CAR r12,rax
        CDR r11,rax
        push r12
        inc r9
        cmp r11,SOB_NIL
        je preparereverse
        CDR rax,rax
        jmp push_args

    preparereverse:
    ;PUSH NIL


    mov r14,0
    mov r12,r9
    mov rax,8
    mul r12
    MALLOC rax,rax
    
    jmp reverse

    reverse:
    cmp r12,0
    je push_args2
    
    pop qword[rax+r14*(8)]
    inc r14
    dec r12
    jmp reverse

    push_args2:
    cmp r12,r9
    je continueapply
    push qword[rax+r12*8]
    inc r12
    jmp push_args2


    continueapply:
    dec r13
    cmp r13,4
    je callproc
    push qword[rbp+r13*8]
    inc r9
    jmp continueapply
    
    callproc:
    push r9
    mov r10,qword[rbp+4*8]
    CLOSURE_ENV rax ,r10
    push rax
    push qword[rbp+8]
    mov r15,qword[rbp]
    add r9,3
    

    ;r9 r15
    ;shift frame
	push rax
	mov rax, qword [rbp+3*8]
	mov r12,rax
	add rax, 4

  	mov r13,rbp
    sub r13,8
	mov r8, r9
	override:
		dec rax
		mov r14, qword[r13]
		mov qword[rbp+rax*8], r14
        sub r13,8
		dec r8
		cmp r8,0
		jne override

	pop rax
    mov r11, rax
    inc r9
    mov rax,8
    mul r9

	add rsp, rax
    dec r9
	mov rax, r12
	add rax, 3
	sub rax,r9
	mov r12,rax
	mov rax,8
	mul r12
	mov r12,rax
	mov rax,r11
	add rsp,r12
    ;shift frame end


    mov rbp,r15
    CLOSURE_CODE rcx ,r10
    jmp rcx

    leave
    ret 
    

