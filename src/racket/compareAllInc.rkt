#!/usr/bin/env racket
#lang s-exp rosette

(current-bitwidth #f)

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

(define registers '(eax ecx edx ebx esp ebp esi edi cf pf zf sf of))

(define (state->map s)
  (make-immutable-hash `(
    (eax . ,(eax s))
    (ecx . ,(ecx s))
    (edx . ,(edx s))
    (ebx . ,(ebx s))
    (esp . ,(esp s))
    (ebp . ,(ebp s))
    (esi . ,(esi s))
    (edi . ,(edi s))
    (cf . ,(cf s))
    (pf . ,(pf s))
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
      (match r  ((Pair ixy z)
      (match ixy ((Pair ix y)
      (match ix ((Pair i x)
        (match y ((None) "error occured in stoke semantics") ((Some y)
        (match z ((None) "error occured in rocksalt semantics") ((Some z)
          (string-append (pretty-state reg->string "original" x)
                         (pretty-state reg->string "stoke" y)
                         (pretty-state reg->string "rocksalt" z)))))))))))))))

(define (diff-state s0 s1)
  (define regs0 (state->map s0))
  (define regs1 (state->map s1))
  (filter  
    (lambda (r) 
      (not (equal? (hash-ref regs0 r) (hash-ref regs1 r)))) 
    registers))

(define (diff-result r)
  (match r ((Pair ixy z)
  (match ixy ((Pair ix y)
  (match ix ((Pair i x)
    (match y ((None) "stoke error") ((Some y)
    (match z ((None) "rocksalt error") ((Some z)
      (diff-state y z))))))))))))

(define (result-instr r)
  (match r ((Pair ixy z)
  (match ixy ((Pair ix y)
  (match ix ((Pair i x) i)))))))

(define (racketList->coqList l)
  (if (null? l) '(Nil) `(Cons ,(car l) ,(racketList->coqList (cdr l)))))

(define (coqList->racketList l)
  (match l ((Nil) '()) ((Cons h t) (cons h (coqList->racketList t)))))

(define replace-unary
  (match-lambda
    [`(O) 0]
    [`(S ,n) (+ 1 (replace-unary n))]
    [(? list? l) (map replace-unary l)]
    [e e]))

; Read instructions from file
; Each line consists of 'stoke instruction : intel instruction'
(define (read-instrs filename)
  (map (lambda (line)
     (define input (map string-trim (string-split line ":")))
     (cons (first input) (second input)))
       (file->lines filename)))

(define t0 (current-inexact-milliseconds))

(define newList (string-trim (vector-ref (current-command-line-arguments) 0)))
(define oldList (string-trim (vector-ref (current-command-line-arguments) 1)))

(define newInstrs (read-instrs newList))
(define oldInstrs (read-instrs oldList))

(define result (coqList->racketList (@ verifyInstrsEqInc
                  (racketList->coqList newInstrs)
		  (racketList->coqList oldInstrs))))

(if (empty? result)
  (printf "All equal")
  (for-each (lambda (r)
    (printf "Not equal in case [~a] (differs on ~a)\n"
      (result-instr r)
      (string-join (map symbol->string (diff-result r)) ", "))) result))

  (printf " (~ams)\n" (exact-round (- (current-inexact-milliseconds) t0)))
  (flush-output)
  
