#!/usr/bin/env bash

compare=/x86sem/src/racket/compare.rkt

echo '===[ running ]==='

$compare 'sarl $0x1, %ebx'
$compare 'rcll $0x1, %ebx'
$compare 'rcrl $0x1, %ebx'

echo '===[ running and investigated ]==='

# possible bugs exhibited:
# PF = computes wrong parity flag
# UR = reads after update
# OF = computes wrong overflow flag
# CF = computes wrong carry flag
# XX = misc

# rocksalt sets zf, sf, pf to a nondeterministic value,
# even though the spec says to compute those appropriately (XX)
$compare 'shll $0x1, %ebx' 
$compare 'shrl $0x1, %ebx'

# rocksalt unnecessarily sets zf, sf, pf to a nondeterministic value (XX)
$compare 'roll $0x1, %ebx'
$compare 'rorl $0x1, %ebx'

# rocksalt updates input before all flags are computed (UR)
# rocksalt also computes the wrong carry flag (OF)
$compare 'addl %ebx, %eax'
$compare 'adcl %ecx, %ebx'

# rocksalt updates carry, which is then used to compute the result (UR)
$compare 'sbbl %ecx, %ebx'

# exchanges before anything is computed, so everything is wrong (UR)
$compare 'xaddl %ecx, %ebx'
$compare 'xchgl %eax, %ebx'
$compare 'xchgl %ebx, %eax'
$compare 'xchgl %ecx, %ebx'

# rocksalt computes wrong overflow (OF)
$compare 'subl %ebx, %eax' 
$compare 'cmpl %ecx, %ebx' 
$compare 'negl %ebx'

# stoke computes sf, which is supposed to be undefined (XX)
$compare 'imull %ecx, %ebx'
# rocksalt edx reads updated ebx (UR)
# rocksalt computes wrong carry and overflow (CF, OF)
$compare 'imull %ebx'
$compare 'mull %ebx' 

# rocksalt computes wrong parity (PF)
$compare 'andl %ebx, %eax'
$compare 'orl %eax, %ebx'
$compare 'xorl %ebx, %eax'
$compare 'testl %ecx, %ebx'
$compare 'incl %ebx'
$compare 'decl %ebx' 

# stoke is too nondeterministic (XX)
$compare 'btl %ecx, %ebx'

# correct
$compare 'nopl %ebx' 
$compare 'notl %ebx'
$compare 'movl %ebx, %eax'
$compare 'clc '       # 'clc'
$compare 'cltd '      # 'cdq'
$compare 'cmc '       # 'cmc'
$compare 'cwtl '      # 'cwde'
$compare 'stc '       # 'stc'
$compare 'bswap %ebx' # 'bswap'

exit

echo '===[ failing and investigated ]==='

# stoke implements these with uninterpreted functions
$compare 'divl %ebx'
$compare 'idivl %ebx'

# rocksalt does not support these instructions
$compare 'blsil %ecx, %ebx' 
$compare 'blsmskl %ecx, %ebx' 
$compare 'blsrl %ecx, %ebx' 
$compare 'cmovael %ecx, %ebx' 
$compare 'cmoval %ecx, %ebx' 
$compare 'cmovbel %ecx, %ebx'
$compare 'cmovbl %ecx, %ebx'
$compare 'cmovcl %ecx, %ebx'
$compare 'cmovel %ecx, %ebx'
$compare 'cmovgel %ecx, %ebx'
$compare 'cmovgl %ecx, %ebx'
$compare 'cmovlel %ecx, %ebx'
$compare 'cmovll %ecx, %ebx'
$compare 'cmovnael %ecx, %ebx'
$compare 'cmovnal %ecx, %ebx'
$compare 'cmovnbel %ecx, %ebx'
$compare 'cmovnbl %ecx, %ebx'
$compare 'cmovncl %ecx, %ebx'
$compare 'cmovnel %ecx, %ebx'
$compare 'cmovngel %ecx, %ebx'
$compare 'cmovngl %ecx, %ebx'
$compare 'cmovnlel %ecx, %ebx'
$compare 'cmovnll %ecx, %ebx'
$compare 'cmovnol %ecx, %ebx'
$compare 'cmovnpl %ecx, %ebx'
$compare 'cmovnsl %ecx, %ebx'
$compare 'cmovnzl %ecx, %ebx'
$compare 'cmovol %ecx, %ebx'
$compare 'cmovpel %ecx, %ebx'
$compare 'cmovpl %ecx, %ebx'
$compare 'cmovpol %ecx, %ebx'
$compare 'cmovsl %ecx, %ebx'
$compare 'cmovzl %ecx, %ebx'
$compare 'popcntl %ecx, %ebx'
$compare 'tzcntl %ecx, %ebx'
$compare 'nop '    # 'nop'
$compare 'cbtw '   # 'cbw'
$compare 'cltq '   # 'cdqe'
$compare 'cqto '   # 'cqo'
$compare 'cwtd '   # 'cwd'
$compare 'vzeroall '   # 'vzeroall'
$compare 'vzeroupper ' # 'vzeroupper'
$compare 'shrxl %edx, %ecx, %ebx'
$compare 'andnl %edx, %ecx, %ebx'
$compare 'bextrl %edx, %ecx, %ebx'
$compare 'sall $0x1, %ebx'


echo '===[ failing ]==='

# rosette can't execute this efficiently (even for fixed inputs)
$compare 'bsfl %ecx, %ebx'
$compare 'bsrl %ecx, %ebx'
