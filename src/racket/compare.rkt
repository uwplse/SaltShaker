#!/usr/bin/env racket
#lang s-exp rosette

(require "x86sem.rkt" "rosette.rkt" "word.rkt" "extraction.rkt" "state.rkt")

(define (pretty-bv64 x)
  (build-string 64 (lambda (i) (if (bveq (bv 1 1) (extract (- 63 i) (- 63 i) x)) #\1 #\0))))

(define (pretty-bool b)
  (if b "1" "0"))

(define registers '(rax rcx rdx rbx rsp rbp rsi rdi cf pf af zf sf of))

(define (state->map s)
  (make-immutable-hash `(
    (rax . ,(pretty-bv64 (state-rax s)))
    (rcx . ,(pretty-bv64 (state-rcx s)))
    (rdx . ,(pretty-bv64 (state-rdx s)))
    (rbx . ,(pretty-bv64 (state-rbx s)))
    (rsp . ,(pretty-bv64 (state-rsp s)))
    (rbp . ,(pretty-bv64 (state-rbp s)))
    (rsi . ,(pretty-bv64 (state-rsi s)))
    (rdi . ,(pretty-bv64 (state-rdi s)))
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
        (match z
    	  ((None) "error occured in rocksalt semantics")
          ((Some z)
            (string-append (pretty-state "original" x)
        	           (pretty-state "stoke" y)
                           (pretty-state "rocksalt" z)))))))))))

(define (lookup-instr name)
  (if (equal? name "andl %ebx, %eax") andEaxEbx
  (if (equal? name "notl %eax") notEax
  (error "Invalid Instruction"))))

(define name (vector-ref (current-command-line-arguments) 0))
(define instr (lookup-instr name))

(displayln (string-append "Verifying instruction: " name))

(displayln "Counterexample Space:")
(displayln (@ instrEqSpace no_prefix andEaxEbx (void)))
(displayln "")

(displayln "Verification Outcome:")
(define r (@ verifyInstrEq no_prefix andEaxEbx))
(displayln (pretty-result r))

