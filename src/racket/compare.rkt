#!/usr/bin/env racket
#lang s-exp rosette

(require "x86sem.rkt" "state.rkt" "bvex.rkt")

(define-namespace-anchor a)

(require "rosette.rkt" "word.rkt" "extraction.rkt" "rocksalt-instr.rkt")

(define (pretty-bits i j x)
  (build-string (+ (- i j) 1) (lambda (k)
    (if (bveq (bv 1 1) (extract (- i k) (- i k) x))
      #\1 #\0))))

(define (pretty-reg x)
  (cond
    (((bitvector 32) x)
      (string-append
        (pretty-bits 31 24 x) " "
        (pretty-bits 23 16 x) " "
        (pretty-bits 15 8 x) " "
        (pretty-bits 7 0 x) "   "
        (~a (bitvector->natural x) #:align 'right #:min-width 15)
        (~a (bitvector->integer (extract 31 0 x)) #:align 'right #:min-width 15)))
    (((bitvector 1) x) (pretty-bits 0 0 x))
    (else "unsupported")))

(define registers '(rax rcx rdx rbx rsp rbp rsi rdi cf pf af zf sf of))

(define (state->map s)
  (make-immutable-hash `(
    (rax . ,(eax s))
    (rcx . ,(ecx s))
    (rdx . ,(edx s))
    (rbx . ,(ebx s))
    (rsp . ,(esp s))
    (rbp . ,(ebp s))
    (rsi . ,(esi s))
    (rdi . ,(edi s))
    (cf . ,(cf s))
    (pf . ,(pf s))
    (af . ,(af s))
    (zf . ,(zf s))
    (sf . ,(sf s))
    (of . ,(of s)))))

(define (pretty-state reg->string name s)
  (define regs (state->map s))
  (define pst (apply string-append (for/list ((r registers))
    (string-append (~a r) ": " (reg->string (hash-ref regs r)) "\n"))))
  (string-append name " state:\n" pst))

(define (pretty-result reg->string r)
  (match r 
    ((None) "semantics are equivalent")
    ((Some r) 
      (match r  ((Pair xy z)
      (match xy ((Pair x y)
        (match y ((None) "error occured in stoke semantics") ((Some y)
        (match z ((None) "error occured in rocksalt semantics") ((Some z)
          (string-append (pretty-state reg->string "original" x)
                         (pretty-state reg->string "stoke" y)
                         (pretty-state reg->string "rocksalt" z)))))))))))))

(define (diff-state s0 s1)
  (define regs0 (state->map s0))
  (define regs1 (state->map s1))
  (define res '())
  (for-each 
    (lambda (r) (unless (equal? (hash-ref regs0 r) (hash-ref regs1 r)) 
                  (set! res (cons (~a r) res))))
    registers)
  (string-join res ", " #:before-first "broken "))

(define (diff-result r)
  (match r  ((Pair xy z)
  (match xy ((Pair x y)
    (match y ((None) "stoke error") ((Some y)
    (match z ((None) "rocksalt error") ((Some z)
      (string-append (diff-state y z)))))))))))

(define (run-rocksalt instr)
  (@ runRocksalt no_prefix (rocksalt-instr instr)))

(define (run-stoke instr)
  (define file (make-temporary-file))
  (system* "/x86sem/src/python/instr2racket.py" instr file)
  (define ns (namespace-anchor->namespace a))
  (parameterize ([current-namespace ns])
    (load file)
    (eval 'run)))

(define (racketList->coqList l)
  (if (null? l) '(Nil) `(Cons ,(car l) ,(racketList->coqList (cdr l)))))

(define (shared-state-regs ignoreRegs)
  (define regs (remove* ignoreRegs (map symbol->string registers)))
  (racketList->coqList (map 
    (lambda (reg)
      (define reg* (string->symbol (regexp-replace #rx"r" reg "e")))
      (define ns (namespace-anchor->namespace a))
      (parameterize ([current-namespace ns])
        `(ExistT (O) ,(eval reg*)))) regs)))

(define instr (string-trim (vector-ref (current-command-line-arguments) 0)))
(define ignoreRegs (cdr (vector->list (current-command-line-arguments))))
(define details #f)

(printf (~a instr #:align 'left #:min-width 21))
(flush-output)

(define stoke (run-stoke instr))
(define rocksalt (run-rocksalt instr))
(define eq (shared_state_eq (shared-state-regs ignoreRegs)))

; testing the instruction, just to make sure the code runs
(define _ (@ testInstrEq eq stoke rocksalt))

(define result (@ verifyInstrEq eq stoke rocksalt))

(match result
  ((None) (if (null? ignoreRegs)
    (printf " is correct\n")
    (printf " is correct   (modulo ~a)\n"
            (string-join ignoreRegs ", "))))
  ((Some r) 
    (printf " is incorrect (~a)\n" 
            (diff-result r))))
(flush-output)

(when details
  (printf "Ignoring Registers: ~a\n" ignoreRegs)
  (printf "Rocksalt Instruction: ~a\n" (rocksalt-instr instr))
  (displayln "Verification Outcome: ")
  (displayln (pretty-result pretty-reg result))
  (displayln "")
  (displayln "Counterexample Space:")
  (displayln (@ spaceInstrEq eq stoke rocksalt (void)))
  (displayln "======================================================\n")
  (flush-output))
 
