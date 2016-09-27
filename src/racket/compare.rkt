#!/usr/bin/env racket
#lang s-exp rosette

(require "state.rkt")

(define-namespace-anchor a)

(require "x86sem.rkt" "rosette.rkt" "word.rkt" "extraction.rkt")

(define (pretty-bits i j x)
  (build-string (+ (- i j) 1) (lambda (k)
    (if (bveq (bv 1 1) (extract (- i k) (- i k) x))
      #\1 #\0))))

(define (pretty-bv32 x)
  (string-append
    (pretty-bits 31 24 x) " "
    (pretty-bits 23 16 x) " "
    (pretty-bits 15 8 x) " "
    (pretty-bits 7 0 x) "   "
    (~a (bitvector->natural x) #:align 'right #:min-width 15)
    (~a (bitvector->integer (extract 31 0 x)) #:align 'right #:min-width 15)))

(define (pretty-bool b)
  (if b "1" "0"))

(define registers '(rax rcx rdx rbx rsp rbp rsi rdi cf pf af zf sf of))

(define (state->map s)
  (make-immutable-hash `(
    (rax . ,(pretty-bv32 (state-rax s)))
    (rcx . ,(pretty-bv32 (state-rcx s)))
    (rdx . ,(pretty-bv32 (state-rdx s)))
    (rbx . ,(pretty-bv32 (state-rbx s)))
    (rsp . ,(pretty-bv32 (state-rsp s)))
    (rbp . ,(pretty-bv32 (state-rbp s)))
    (rsi . ,(pretty-bv32 (state-rsi s)))
    (rdi . ,(pretty-bv32 (state-rdi s)))
    (cf . ,(pretty-bool (state-cf s)))
    (pf . ,(pretty-bool (state-pf s)))
    (af . ,(pretty-bool (state-af s)))
    (zf . ,(pretty-bool (state-zf s)))
    (sf . ,(pretty-bool (state-sf s)))
    (of . ,(pretty-bool (state-of s))))))

(define (pretty-state name s)
  (define regs (state->map s))
  (define pst (apply string-append (for/list ((r registers))
    (string-append (~a r) ": " (hash-ref regs r) "\n"))))
  (string-append name " state:\n" pst "\n"))

(define (pretty-result r)
  (match r 
    ((None) "semantics are equivalent")
    ((Some r) 
      (match r  ((Pair xy z)
      (match xy ((Pair x y)
        (match y ((None) "error occured in stoke semantics") ((Some y)
        (match z ((None) "error occured in rocksalt semantics") ((Some z)
          (string-append (pretty-state "original" x)
                         (pretty-state "stoke" y)
                         (pretty-state "rocksalt" z)))))))))))))

(define (rocksalt-operator op)
  (define name (second (regexp-match #rx"^([a-z]+)l$" op)))
  `(,(string->symbol (string-upcase name)) (True)))

(define (rocksalt-operand op)
  (define reg (second (regexp-match #rx"^%([a-z0-9]+)$" op)))
  `(Reg_op (,(string->symbol (string-upcase reg)))))

(define (rocksalt-instr instr)
  (define is (regexp-split #rx"[ ,]+" instr))
  (append (rocksalt-operator (car is)) 
          (reverse (map rocksalt-operand (cdr is)))))

(define (run-rocksalt instr)
  (@ runRocksalt no_prefix (rocksalt-instr instr)))

(define (run-stoke instr)
  (define file (make-temporary-file))
  (system* "/x86sem/src/python/instr2racket.py" instr file)
  (define ns (namespace-anchor->namespace a))
  (parameterize ([current-namespace ns])
    (load file)
    (eval 'run)))

(define instr (vector-ref (current-command-line-arguments) 0))

(displayln (string-append "Verifying instruction: " instr))
(displayln "======================================================\n")

(define stoke (run-stoke instr))
(displayln (rocksalt-instr instr))
(define rocksalt (run-rocksalt instr))

(displayln "")
(displayln "Testing Outcome")
(define t (@ testInstrEq stoke rocksalt))
(displayln (pretty-result t))
(displayln "")
(displayln "Verification Outcome:")
(define r (@ verifyInstrEq stoke rocksalt))
(displayln (pretty-result r))
(displayln "")
(displayln "Counterexample Space:")
(displayln (@ spaceInstrEq stoke rocksalt (void)))
(displayln "")
 
