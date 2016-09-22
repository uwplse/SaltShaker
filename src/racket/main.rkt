#!/usr/bin/env racket
#lang s-exp rosette

(require "x86sem.rkt" "rosette.rkt" "word.rkt" "extraction.rkt" "state.rkt")

(define (read-bits)
  (string->number (vector-ref (current-command-line-arguments) 1)))

(define (construct-positive-space) 
  (define bits (read-bits))
  (displayln (string-append "Construct positive space with " (~a bits) " bits:"))
  (displayln (@ constructPositiveSpace (number->unary (- bits 1)) (void))))

(define (trivial-positive-verification)
  (define bits (read-bits))
  (displayln (string-append "Trivial positive verification with " (~a bits) " bits:"))
  (displayln (@ trivialPositiveVerification (number->unary (- bits 1)))))

(define (find-word-proposition)
  (define bits (read-bits))
  (displayln (string-append "Find word proposition with " (~a bits) " bits:"))
  (displayln (@ findWordProposition (number->unary (- bits 1)) (bv 4 bits)))
  (displayln (@ findWordProposition (number->unary (- bits 1)) (bv -1 bits))))

(define (find-word)
  (define bits (read-bits))
  (displayln (string-append "Find word with " (~a bits) " bits:"))
  (displayln (@ findWord (number->unary (- bits 1)))))

(define (word-verification)
  (define bits (read-bits))
  (displayln (string-append "Word verification with " (~a bits) " bits:"))
  (displayln (@ wordVerification (number->unary (- bits 1)))))

(define (cast8-add-verification-proposition)
  (displayln "Cast8 add verification proposition (good):")
  (displayln (@ cast8AddVerificationProposition `(Pair ,(bv 6 32) ,(bv 4 32))))
  (displayln "Cast8 add verification proposition (bad):")
  (displayln (@ cast8AddVerificationProposition `(Pair ,(bv 510 32) ,(bv 4 32)))))

(define (init-rtl-state)
  (displayln "Init RTL state:")
  (displayln (@ initRTLState (void))))

(define (cast8-add-verification)
  (displayln "Cast8 add verification:")
  (displayln (@ cast8AddVerification (void))))

(define (not-verification-proposition)
  (displayln "Not verification proposition (good1):")
  (displayln (@ notVerificationProposition (bv 0 32)))
  (displayln "Not verification proposition (good2):")
  (displayln (@ notVerificationProposition (bv -1 32))))

(define (not-verification)
  (displayln "Not verification:")
  (displayln (@ notVerification (void))))

(define (and-verification-proposition)
  (displayln "And verification proposition (good1):")
  (displayln (@ andVerificationProposition `(Pair ,(bv 6 32) ,(bv 4 32))))
  (displayln "And verification proposition (good2):")
  (displayln (@ andVerificationProposition `(Pair ,(bv 21303 32) ,(bv 4 32)))))

(define (and-verification)
  (displayln "And verification:")
  (displayln (@ andVerification (void))))

(define (and-space)
  (displayln "And space")
  (displayln (@ andSpace (void))))

(define (pretty-bv64 x)
  (build-string 64 (lambda (i) (if (bveq (bv 1 1) (extract i i x)) #\1 #\0))))

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

(define (instr-eq-space)
  (displayln "Instr eq space")
  (displayln (@ instrEqSpace no_prefix andEaxEbx (void))))

(define (verify-instr-eq)
  (displayln "Verify instr eq")
  (define r (@ verifyInstrEq no_prefix andEaxEbx))
  (displayln r)
  (displayln (pretty-result r)))

(define command (vector-ref (current-command-line-arguments) 0))

(if (equal? command "construct-positive-space") (construct-positive-space)
(if (equal? command "trivial-positive-verification") (trivial-positive-verification)
(if (equal? command "find-word-proposition") (find-word-proposition)
(if (equal? command "find-word") (find-word)
(if (equal? command "word-verification") (word-verification)
(if (equal? command "cast8-add-verification-proposition") (cast8-add-verification-proposition)
(if (equal? command "init-rtl-state") (init-rtl-state)
(if (equal? command "cast8-add-verification") (cast8-add-verification)
(if (equal? command "not-verification-proposition") (not-verification-proposition)
(if (equal? command "not-verification") (not-verification)
(if (equal? command "and-verification-proposition") (and-verification-proposition)
(if (equal? command "and-verification") (and-verification)
(if (equal? command "and-space") (and-space)
(if (equal? command "instr-eq-space") (instr-eq-space)
(if (equal? command "verify-instr-eq") (verify-instr-eq)
(void))))))))))))))))

