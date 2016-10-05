#lang s-exp rosette

(provide rocksalt-instr)

(define (operand type op)
  (case type
    ((immediate) `(Imm_op ,(bv op 32)))
    ((register)  `(Reg_op ,op))))

(define (reg-or-immed type op)
  (case type
    ((immediate) `(Imm_ri ,(bv op 8)))
    ((register)  `(Reg_ri ,op))))

(define (register type op)
  (case type
    ((register) op)))

(define ((immediate bits) type op)
  (case type
    ((immediate) (bv op bits))))

(define unsupportedOpcode '(
  "blsil"
  "blsmskl"
  "blsrl"
  "cmovael" 
  "cmoval" 
  "cmovbel"
  "cmovbl"
  "cmovcl"
  "cmovel"
  "cmovgel"
  "cmovgl"
  "cmovlel"
  "cmovll"
  "cmovnael"
  "cmovnal"
  "cmovnbel"
  "cmovnbl"
  "cmovncl"
  "cmovnel"
  "cmovngel"
  "cmovngl"
  "cmovnlel"
  "cmovnll"
  "cmovnol"
  "cmovnpl"
  "cmovnsl"
  "cmovnzl"
  "cmovol"
  "cmovpel"
  "cmovpl"
  "cmovpol"
  "cmovsl"
  "cmovzl"
  "popcntl"
  "tzcntl"
  "nop"    ; "nop"
  "cbtw"   ; "cbw"
  "cltq"   ; "cdqe"
  "cqto"   ; "cqo"
  "cwtd"   ; "cwd"
  "vzeroall"   ; "vzeroall"
  "vzeroupper" ; "vzeroupper"
  "shrxl"
  "andnl"
  "bextrl"
  "sall"
))

(define specialOpcode 
  (make-immutable-hash `(
    ; at&t-name     intel-name  w-flag  operand-format (intel order)
    ("rcll"       . ("rcl"        #t  (,reg-or-immed ,operand)))
    ("rcrl"       . ("rcr"        #t  (,reg-or-immed ,operand)))
    ("roll"       . ("rol"        #t  (,reg-or-immed ,operand)))
    ("rorl"       . ("ror"        #t  (,reg-or-immed ,operand)))
    ("sarl"       . ("sar"        #t  (,reg-or-immed ,operand)))
    ("shll"       . ("shl"        #t  (,reg-or-immed ,operand)))
    ("shrl"       . ("shr"        #t  (,reg-or-immed ,operand)))
    ("bsfl"       . ("bsf"        #f  (,operand ,operand)))
    ("bsrl"       . ("bsr"        #f  (,operand ,operand)))
    ("btl"        . ("bt"         #f  (,operand ,operand)))
    ("nopl"       . ("nop"        #f  (,operand)))
    ("cltd"       . ("cdq"        #f  ()))
    ("cwtl"       . ("cwde"       #f  ()))
    ("leaveq"     . ("leave"      #f  ()))
    ("cmc"        . ("cmc"        #f  ()))
    ("stc"        . ("stc"        #f  ()))
    ("clc"        . ("clc"        #f  ()))
    ("bswap"      . ("bswap"      #f  (,register))))))

(define (op->flags op)
  (define m (regexp-match #rx"^[a-z]+([bwl])$" op))
  (if (not m) 
    (values '(False) '(True)) ; default to 32bit
    (case (second m)
             ; override w-flag
      [("b") (values '(False) '(False))]    ;  8bit
      [("w") (values '(True)  '(True) )]    ; 16bit
      [("l") (values '(False) '(True) )]))) ; 32bit

(define (rocksalt-info op args)
  (define r (hash-ref specialOpcode op #f))
  (if r 
    (values (first r) 
            (second r)
            (third r))
    (values (second (regexp-match #rx"^([a-z]+)[bwl]$" op)) 
            #t
            (map (lambda (_) operand) args))))

(define (rocksalt-operand op wrap)
  (define m (regexp-match #rx"^\\$0x([a-f0-9]+)$" op))
  (if m 
    (wrap 'immediate (string->number (second m) 16))
    (wrap 'register (list
      ((match-lambda 
        [(regexp #rx"^%e?ax|al$") 'EAX]
        [(regexp #rx"^%e?cx|cl$") 'ECX]
        [(regexp #rx"^%e?dx|dl$") 'EDX]
        [(regexp #rx"^%e?bx|bl$") 'EBX]
        [(regexp #rx"^%e?sp$")    'ESP]
        [(regexp #rx"^%e?bp$")    'EBP]
        [(regexp #rx"^%e?si$")    'ESI]
        [(regexp #rx"^%e?di$")    'EDI]
        [(regexp #rx"^%([a-z0-9]+)$" m)
          (string->symbol (string-upcase (second m)))]) op)))))

(define (prefixed-instr op-over instr)
  (define p `(MkPrefix (None) (None) ,op-over (False)))
  `(Pair ,p ,instr))

(define (generic-rocksalt-instr op args)
  (define-values (op* wflag? formats) (rocksalt-info op args))
  (define-values (op-over wflag) (op->flags op))
  (define id (string->symbol (string-upcase op*)))
  (prefixed-instr op-over (append 
    (if wflag? `(,id ,wflag) `(,id))
    (reverse (map rocksalt-operand args formats)))))

(define (imul op args)
  (define-values (op-over wflag) (op->flags op))
  (prefixed-instr op-over (append `(IMUL ,wflag)
    (case (length args)
      [(1) `(,(rocksalt-operand (first args) operand) (None) (None))]
      [(2) `(,(rocksalt-operand (second args) operand)
             (Some ,(rocksalt-operand (first args) operand)) (None))]
      [(3) `(,(rocksalt-operand (third args) operand)
             (Some ,(rocksalt-operand (second args) operand))
             (Some ,(rocksalt-operand (first args) (immediate 32))))]))))

(define (rocksalt-instr instr)
  (define is (regexp-split #rx"[ ,]+" instr))
  (define op (car is))
  (define args (cdr is))
  (if (member op unsupportedOpcode) #f
    (if (string-prefix? op "imul")
      (imul op args)
      (generic-rocksalt-instr op args))))

