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

(define specialOpcode 
  (make-immutable-hash `(
    ; intel-name  w-flag  operand-format (intel order)
    ("rcl"      . (#t  (,operand ,reg-or-immed)))
    ("rcr"      . (#t  (,operand ,reg-or-immed)))
    ("rol"      . (#t  (,operand ,reg-or-immed)))
    ("ror"      . (#t  (,operand ,reg-or-immed)))
    ("sar"      . (#t  (,operand ,reg-or-immed)))
    ("shl"      . (#t  (,operand ,reg-or-immed)))
    ("shr"      . (#t  (,operand ,reg-or-immed)))
    ("shld"     . (#f  (,operand ,register ,reg-or-immed)))
    ("shrd"     . (#f  (,operand ,register ,reg-or-immed)))
    ("bsf"      . (#f  (,operand ,operand)))
    ("bsr"      . (#f  (,operand ,operand)))
    ("bt"       . (#f  (,operand ,operand)))
    ("nop"      . (#f  (,operand)))
    ("cdq"      . (#f  ()))
    ("cwde"     . (#f  ()))
    ("leave"    . (#f  ()))
    ("cmc"      . (#f  ()))
    ("stc"      . (#f  ()))
    ("clc"      . (#f  ()))
    ("bswap"    . (#f  (,register))))))

(define (arg->flags arg)
  ((match-lambda 
                                     ; override   w-flag
     [(regexp #rx"^%.[hl]$")   (values '(False) '(False))]        ;  8bit
     [(regexp #rx"^%.[xpi]$")  (values '(True)  '(True) )]        ; 16bit
     [(regexp #rx"^%e.[xpi]$") (values '(False) '(True) )]) arg)) ; 32bit

(define (generic-op->flags op)
  (define m (regexp-match #rx"^[a-z]+([bwl])$" op))
  (if (not m) 
    (values '(False) '(True)) ; default to 32bit
    (case (second m)
                   ; override   w-flag
      [("b") (values '(False) '(False))]    ;  8bit
      [("w") (values '(True)  '(True) )]    ; 16bit
      [("l") (values '(False) '(True) )]))) ; 32bit

(define (op->flags op)
  ((match-lambda 
    [(regexp #rx"^mov[sz]wl$") (values '(False) '(True) )] ; 16bit -> 32bit
    [(regexp #rx"^mov[sz]bw$") (values '(True)  '(False))] ;  8bit -> 16bit
    [(regexp #rx"^mov[sz]bl$") (values '(False) '(False))] ;  8bit -> 32bit
    [else (generic-op->flags op)]) op))

(define (rocksalt-info intel args)
  (define r (hash-ref specialOpcode intel #f))
  (if r 
    (values (first r) (second r))
    (values #t (map (lambda (_) operand) args))))

(define (rocksalt-operand op wrap)
  (define m (regexp-match #rx"^\\$0x([a-f0-9]+)$" op))
  (if m 
    (wrap 'immediate (string->number (second m) 16))
    (wrap 'register (list
      ((match-lambda 
        [(regexp #rx"^%a[xl]$")   'EAX]
        [(regexp #rx"^%c[xl]$")   'ECX]
        [(regexp #rx"^%d[xl]$")   'EDX]
        [(regexp #rx"^%b[xl]$")   'EBX]
        [(regexp #rx"^%(sp|ah)$") 'ESP]
        [(regexp #rx"^%(bp|ch)$") 'EBP]
        [(regexp #rx"^%(si|dh)$") 'ESI]
        [(regexp #rx"^%(di|bh)$") 'EDI]
        [(regexp #rx"^%([a-z0-9]+)$" m)
          (string->symbol (string-upcase (second m)))]) op)))))

(define (prefixed-instr op-over instr)
  (define p `(MkPrefix (None) (None) ,op-over (False)))
  `(Pair ,p ,instr))

(define (generic-rocksalt-instr op intel args)
  (define-values (wflag? formats) (rocksalt-info intel args))
  (define-values (op-over wflag) (op->flags op))
  (define id (string->symbol (string-upcase intel)))
  (prefixed-instr op-over (append 
    (if wflag? `(,id ,wflag) `(,id))
    (map rocksalt-operand (reverse args) formats))))

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

(define (rocksalt-instr instr intel)
  (define is (regexp-split #rx"[ ,]+" instr))
  (define op (car is))
  (define args (cdr is))
  (if (equal? intel "imul") (imul op args)
  (if (equal? op "nop") (error "nop without arguments is not supported")
    (generic-rocksalt-instr op intel args))))

