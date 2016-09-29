#!/usr/bin/env bash

compare=/x86sem/src/racket/compare.rkt

echo "===[ failing ]==="

$compare "bsfl %ecx, %ebx"
$compare "bsrl %ecx, %ebx"

# weird operands
$compare "bswap %ebx" # "bswap"
$compare "andnl %edx, %ecx, %ebx"
$compare "bextrl %edx, %ecx, %ebx"
$compare "cbtw "   # "cbw"
$compare "clc "    # "clc"
$compare "cltd "   # "cdq"
$compare "cltq "   # "cdqe"
$compare "cmc "    # "cmc"
$compare "cqto "   # "cqo"
$compare "cwtd "   # "cwd"
$compare "cwtl "   # "cwde"
$compare "leaveq " # "leave"
$compare "nop "    # "nop"
$compare "rcll $0x1, %ebx"
$compare "rcrl $0x1, %ebx"
$compare "roll $0x1, %ebx"
$compare "rorl $0x1, %ebx"
$compare "sall $0x1, %ebx"
$compare "sarl $0x1, %ebx"
$compare "sbbl %ecx, %ebx"
$compare "shll $0x1, %ebx"
$compare "shrl $0x1, %ebx"
$compare "shrxl %edx, %ecx, %ebx"
$compare "stc "        # "stc"
$compare "vzeroall "   # "vzeroall"
$compare "vzeroupper " # "vzeroupper"

echo "===[ running ]==="

$compare "imull %ebx" 
$compare "imull %ecx, %ebx"
$compare "nopl %ebx" 
$compare "adcl %ecx, %ebx" 
$compare "cmpl %ecx, %ebx"
$compare "decl %ebx"
$compare "incl %ebx"
$compare "negl %ebx"
$compare "testl %ecx, %ebx"
$compare "xaddl %ecx, %ebx"
$compare "xchgl %eax, %ebx"
$compare "xchgl %ebx, %eax"
$compare "xchgl %ecx, %ebx"

echo "===[ running and investigated ]==="

# computes incorrect overflow
$compare "subl %ebx, %eax" 
$compare "subl %ebx, %eax" af pf of

# input updated before all flags are computed
$compare "addl %ebx, %eax"
$compare "addl %ebx, %eax" af pf of
$compare "addl %ebx, %eax" af pf of sf
$compare "addl %ebx, %eax" af pf of sf cf zf
$compare "mull %ebx" 
$compare "mull %ebx" rdx
$compare "mull %ebx" of cf rdx

# only parity broken
$compare "andl %ebx, %eax"
$compare "andl %ebx, %eax" pf
$compare "orl %eax, %ebx"
$compare "orl %eax, %ebx" pf
$compare "xorl %ebx, %eax"
$compare "xorl %ebx, %eax" pf

# correct
$compare "movl %ebx, %eax"
$compare "notl %ebx"

# bug in stoke?
$compare "btl %ecx, %ebx"

echo "===[ failing and investigated ]==="

# uninterpreted functions in stoke 
$compare "divl %ebx"
$compare "idivl %ebx"

# unsupported instruction in rocksalt
$compare "blsil %ecx, %ebx" 
$compare "blsmskl %ecx, %ebx" 
$compare "blsrl %ecx, %ebx" 
$compare "cmovael %ecx, %ebx" 
$compare "cmoval %ecx, %ebx" 
$compare "cmovbel %ecx, %ebx"
$compare "cmovbl %ecx, %ebx"
$compare "cmovcl %ecx, %ebx"
$compare "cmovel %ecx, %ebx"
$compare "cmovgel %ecx, %ebx"
$compare "cmovgl %ecx, %ebx"
$compare "cmovlel %ecx, %ebx"
$compare "cmovll %ecx, %ebx"
$compare "cmovnael %ecx, %ebx"
$compare "cmovnal %ecx, %ebx"
$compare "cmovnbel %ecx, %ebx"
$compare "cmovnbl %ecx, %ebx"
$compare "cmovncl %ecx, %ebx"
$compare "cmovnel %ecx, %ebx"
$compare "cmovngel %ecx, %ebx"
$compare "cmovngl %ecx, %ebx"
$compare "cmovnlel %ecx, %ebx"
$compare "cmovnll %ecx, %ebx"
$compare "cmovnol %ecx, %ebx"
$compare "cmovnpl %ecx, %ebx"
$compare "cmovnsl %ecx, %ebx"
$compare "cmovnzl %ecx, %ebx"
$compare "cmovol %ecx, %ebx"
$compare "cmovpel %ecx, %ebx"
$compare "cmovpl %ecx, %ebx"
$compare "cmovpol %ecx, %ebx"
$compare "cmovsl %ecx, %ebx"
$compare "cmovzl %ecx, %ebx"
$compare "popcntl %ecx, %ebx"
$compare "tzcntl %ecx, %ebx"

