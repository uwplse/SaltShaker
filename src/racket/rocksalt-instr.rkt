#lang s-exp rosette

(provide rocksalt-instr)

(define (operand type op)
  (case type
    ((immediate) `(Imm_op ,op))
    ((register)  `(Reg_op ,op))))

(define (reg-or-immed type op)
  (case type
    ((immediate) `(Imm_ri ,op))
    ((register)  `(Reg_ri ,op))))

(define (register type op)
  (case type
    ((register)  op)))

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

(define (rocksalt-info op args)
  (define r (hash-ref specialOpcode op #f))
  (if r 
    (values (first r) 
            (second r)
            (third r))
    (values (second (regexp-match #rx"^([a-z]+)l$" op)) 
            #t 
            (map (lambda (_) operand) args))))

(define (rocksalt-operand op wrap)
  (define m (regexp-match #rx"^%([a-z0-9]+)$" op))
  (if m
    (wrap 'register (list (string->symbol (string-upcase (second m)))))
    (begin
      (define m (regexp-match #rx"^\\$0x([a-f0-9]+)$" op))
      (if m 
        (wrap 'immediate (bv (string->number (second m)) 8))
        (error "unsupported operand")))))

(define (generic-rocksalt-instr op args)
  (define-values (op* wflag? formats) (rocksalt-info op args))
  (define id (string->symbol (string-upcase op*)))
  (append 
    (if wflag? `(,id (True)) `(,id))
    (reverse (map rocksalt-operand args formats))))

(define (imull args)
  (if (= 1 (length args))
    `(IMUL (True) ,(rocksalt-operand (first args) operand) (None) (None))
    `(IMUL (True) ,(rocksalt-operand (second args) operand) (Some ,(rocksalt-operand (first args) operand)) (None))))

(define (rocksalt-instr instr)
  (define is (regexp-split #rx"[ ,]+" instr))
  (define op (car is))
  (define args (cdr is))
  (when (member op unsupportedOpcode) (error "unsupported opcode"))
  (if (equal? op "imull") (imull args)
                          (generic-rocksalt-instr op args)))

