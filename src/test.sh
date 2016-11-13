#!/usr/bin/env bash

compare=/x86sem/src/racket/compare.rkt

echo '===[ running and investigated ]==='

# bugs exhibited:
# PF = computes wrong parity flag
# UR = reads after update
# OF = computes wrong overflow flag
# CF = computes wrong carry flag
# SH = shift by wrong amount
# ND = more non-determinism than necessary (not a bug)

# of flag is not set
$compare 'shldl $0x0, %ebx, %ecx'  shld  # 'is equal modulo sf, of (2111ms)'

exit

$compare 'shldl $0x1, %ebx, %ebx'  shld  # 'is equal modulo of (2194ms)'

# cf/of flags are computed inaccurately
$compare 'imulw $0xffe0, %bx, %cx' imul  # 'is equal modulo cf, sf, of (2786.123046875ms)'

# stoke shifts by wrong amount (SH)
$compare 'rcll $0x1, %ebx' 'rcl'
$compare 'rcrl $0x1, %ebx' 'rcr'

# rocksalt updates input before all flags are computed (UR)
# rocksalt also computes the wrong carry flag (OF)
$compare 'addl %ebx, %eax' 'add'
$compare 'adcl %ecx, %ebx' 'adc'

# rocksalt updates carry, which is then used to compute the result (UR)
# rocksalt also computes wrong overflow and carry flag (OF, CR)
$compare 'sbbl %ecx, %ebx' 'sbb'

# exchanges before anything is computed, so everything is wrong (UR)
$compare 'xaddl %ecx, %ebx' 'xadd'
$compare 'xchgl %eax, %ebx' 'xchg'
$compare 'xchgl %ebx, %eax' 'xchg'
$compare 'xchgl %ecx, %ebx' 'xchg'

# rocksalt computes wrong overflow (OF)
$compare 'subl %ebx, %eax' 'sub'
$compare 'cmpl %ecx, %ebx' 'cmp'
$compare 'negl %ebx' 'neg'

# rocksalt computes wrong parity (PF)
$compare 'andl %ebx, %eax' 'and'
$compare 'orl %eax, %ebx' 'or'
$compare 'xorl %ebx, %eax' 'xor'
$compare 'testl %ecx, %ebx' 'test'
$compare 'incl %ebx' 'inc'
$compare 'decl %ebx' 'dec'

# rocksalt edx reads updated ebx (UR)
# rocksalt computes wrong carry and overflow (CF, OF)
$compare 'mull %ebx' 'mul'

# rocksalt edx reads updated ebx (UR)
# rocksalt computes wrong carry and overflow (CF, OF)
# rocksalt is too nondeterministic with the sign flag (ND)
$compare 'imull %ebx' 'imul'

# rocksalt is too nondeterministic with the sign flag (ND)
$compare 'imull %ecx, %ebx' 'imul'

# rocksalt unnecessarily sets zf, sf, pf to a nondeterministic value (ND)
$compare 'shll $0x1, %ebx' 'shl'
$compare 'shrl $0x1, %ebx' 'shr'
$compare 'sarl $0x1, %ebx' 'sar'
$compare 'roll $0x1, %ebx' 'rol'
$compare 'rorl $0x1, %ebx' 'ror'

# stoke is too nondeterministic (ND)
$compare 'btl %ecx, %ebx' 'bt'

# correct
$compare 'nopl %ebx' 'nop'
$compare 'notl %ebx' 'not'
$compare 'movl %ebx, %eax' 'mov'
$compare 'clc' 'clc' 
$compare 'cltd' 'cdq'
$compare 'cmc' 'cmc'
$compare 'cwtl' 'cwde'
$compare 'stc' 'stc'
$compare 'bswap %ebx' 'bswap'
$compare 'bsfl %ecx, %ebx' 'bsf'
$compare 'bsrl %ecx, %ebx' 'bsr'

echo '===[ failing and investigated ]==='

# stoke implements these with uninterpreted functions
$compare 'divl %ebx' 'div'
$compare 'idivl %ebx' 'idiv'

# rocksalt does not support these instructions
$compare 'blsil %ecx, %ebx' 'blsi'
$compare 'blsmskl %ecx, %ebx' 'blsmsk'
$compare 'blsrl %ecx, %ebx' 'blsr'
$compare 'cmovael %ecx, %ebx' 'cmovae'
$compare 'cmoval %ecx, %ebx' 'cmova'
$compare 'cmovbel %ecx, %ebx' 'cmovbe'
$compare 'cmovbl %ecx, %ebx' 'cmovb'
$compare 'cmovcl %ecx, %ebx' 'cmovc'
$compare 'cmovel %ecx, %ebx' 'cmove'
$compare 'cmovgel %ecx, %ebx' 'cmovge'
$compare 'cmovgl %ecx, %ebx' 'cmovg'
$compare 'cmovlel %ecx, %ebx' 'cmovle'
$compare 'cmovll %ecx, %ebx' 'cmovl'
$compare 'cmovnael %ecx, %ebx' 'cmovnae'
$compare 'cmovnal %ecx, %ebx' 'cmovna'
$compare 'cmovnbel %ecx, %ebx' 'cmovnbe'
$compare 'cmovnbl %ecx, %ebx' 'cmovnb'
$compare 'cmovncl %ecx, %ebx' 'cmovnc'
$compare 'cmovnel %ecx, %ebx' 'cmovne'
$compare 'cmovngel %ecx, %ebx' 'cmovnge'
$compare 'cmovngl %ecx, %ebx' 'cmovng'
$compare 'cmovnlel %ecx, %ebx' 'cmovnle'
$compare 'cmovnll %ecx, %ebx' 'cmovnl'
$compare 'cmovnol %ecx, %ebx' 'cmovno'
$compare 'cmovnpl %ecx, %ebx' 'cmovnp'
$compare 'cmovnsl %ecx, %ebx' 'cmovns'
$compare 'cmovnzl %ecx, %ebx' 'cmovnz'
$compare 'cmovol %ecx, %ebx' 'cmovo'
$compare 'cmovpel %ecx, %ebx' 'cmovpe'
$compare 'cmovpl %ecx, %ebx' 'cmovp'
$compare 'cmovpol %ecx, %ebx' 'cmovpo'
$compare 'cmovsl %ecx, %ebx' 'cmovs'
$compare 'cmovzl %ecx, %ebx' 'cmovz'
$compare 'popcntl %ecx, %ebx' 'popcnt'
$compare 'tzcntl %ecx, %ebx' 'tzcnt'
$compare 'nop' 'nop' 
$compare 'cbtw' 'cbw'
$compare 'cltq' 'cdqe'
$compare 'cqto' 'cqo'
$compare 'cwtd' 'cwd'
$compare 'vzeroall' 'vzeroall'
$compare 'vzeroupper' 'vzeroupper'
$compare 'shrxl %edx, %ecx, %ebx' 'shrx'
$compare 'andnl %edx, %ecx, %ebx' 'andn'
$compare 'bextrl %edx, %ecx, %ebx' 'bextr'
$compare 'sall $0x1, %ebx' 'sal'

