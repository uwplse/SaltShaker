#lang s-exp rosette

(provide rocksalt-instr)

(define ((operand bits) type op)
  (case type
    ((immediate) `(Imm_op ,(bv op bits)))
    ((register)  `(Reg_op ,op))))

(define ((reg-or-immed bits) type op)
  (case type
    ((immediate) `(Imm_ri ,(bv op bits)))
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
    ("rcll"       . ("rcl"        #t  (,(reg-or-immed 8) ,(operand 32))))
    ("rcrl"       . ("rcr"        #t  (,(reg-or-immed 8) ,(operand 32))))
    ("roll"       . ("rol"        #t  (,(reg-or-immed 8) ,(operand 32))))
    ("rorl"       . ("ror"        #t  (,(reg-or-immed 8) ,(operand 32))))
    ("sarl"       . ("sar"        #t  (,(reg-or-immed 8) ,(operand 32))))
    ("shll"       . ("shl"        #t  (,(reg-or-immed 8) ,(operand 32))))
    ("shrl"       . ("shr"        #t  (,(reg-or-immed 8) ,(operand 32))))
    ("bsfl"       . ("bsf"        #f  (,(operand 32) ,(operand 32))))
    ("bsrl"       . ("bsr"        #f  (,(operand 32) ,(operand 32))))
    ("btl"        . ("bt"         #f  (,(operand 32) ,(operand 32))))
    ("nopl"       . ("nop"        #f  (,(operand 32))))
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
            (map (lambda (_) (operand 32)) args))))

(define (rocksalt-operand op wrap)
  (define m (regexp-match #rx"^%([a-z0-9]+)$" op))
  (if m
    (wrap 'register (list (string->symbol (string-upcase (second m)))))
    (begin
      (define m (regexp-match #rx"^\\$0x([a-f0-9]+)$" op))
      (if m 
        (wrap 'immediate (string->number (second m) 16))
        (error "unsupported operand")))))

(define (generic-rocksalt-instr op args)
  (define-values (op* wflag? formats) (rocksalt-info op args))
  (define id (string->symbol (string-upcase op*)))
  (append 
    (if wflag? `(,id (True)) `(,id))
    (reverse (map rocksalt-operand args formats))))

(define (imull args)
  (case (length args)
    [(1) `(IMUL (True) ,(rocksalt-operand (first args) (operand 32)) (None) (None))]
    [(2) `(IMUL (True) ,(rocksalt-operand (second args) (operand 32))
                       (Some ,(rocksalt-operand (first args) (operand 32))) (None))]
    [(3) `(IMUL (True) ,(rocksalt-operand (third args) (operand 32))
                       (Some ,(rocksalt-operand (second args) (operand 32)))
                       (Some ,(rocksalt-operand (first args) (immediate 32))))]))

(define (rocksalt-instr instr)
  (define is (regexp-split #rx"[ ,]+" instr))
  (define op (car is))
  (define args (cdr is))
  (if (member op unsupportedOpcode) #f
    (if (equal? op "imull") (imull args)
                            (generic-rocksalt-instr op args))))

