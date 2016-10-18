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
  (filter  
    (lambda (r) 
      (not (equal? (hash-ref regs0 r) (hash-ref regs1 r)))) 
    registers))

(define (diff-result r)
  (match r  ((Pair xy z)
  (match xy ((Pair x y)
    (match y ((None) "stoke error") ((Some y)
    (match z ((None) "rocksalt error") ((Some z)
      (diff-state y z))))))))))

(define (runStoke instr)
  (define file (make-temporary-file))
  (system* "/x86sem/src/python/instr2racket.py" instr file)
  (define ns (namespace-anchor->namespace a))
  (parameterize ([current-namespace ns])
    (load file)
    (eval 'run)))

(define (racketList->coqList l)
  (if (null? l) '(Nil) `(Cons ,(car l) ,(racketList->coqList (cdr l)))))

(define (coqList->racketList l)
  (match l ((Nil) '()) ((Cons h t) (cons h (coqList->racketList t)))))

(define (shared-state-regs ignoreRegs)
  (define regs (remove* ignoreRegs registers))
  (racketList->coqList (for/list ((reg regs)) 
    (define ns (namespace-anchor->namespace a))
    (parameterize ([current-namespace ns])
      `(ExistT (O) ,(eval reg))))))

(define replace-unary
  (match-lambda
    [`(O) 0]
    [`(S ,n) (+ 1 (replace-unary n))]
    [(? list? l) (map replace-unary l)]
    [e e]))

(define instr (string-trim (vector-ref (current-command-line-arguments) 0)))
(define intel (string-trim (vector-ref (current-command-line-arguments) 1)))
(define details (= 3 (vector-length (current-command-line-arguments))))
(define ignoreRegs '())  ; (map string->symbol (cdr (vector->list (current-command-line-arguments)))))

(printf "~a " (~a instr #:align 'left #:min-width 25))
(printf "~a " (~a intel #:align 'left #:min-width 8))
(flush-output)

(with-handlers ([exn:fail? (lambda (exn) 
  (if details (raise exn) (displayln exn)))])

  (define rocksaltInstr (rocksalt-instr instr intel))
  (define stoke (runStoke instr))
  (define rocksalt (runRocksalt rocksaltInstr))
  
  (when details
    (printf "Rocksalt Instruction: ~a\n" rocksaltInstr)
    (displayln "")
    (displayln "Rocksalt Semantics:")
    (for-each displayln (coqList->racketList (replace-unary (instrToRTL rocksaltInstr))))
    (displayln "")
    (flush-output))
  
  (define (verificationLoop ignoreRegs)
    (when details
      (printf "Verification Outcome (ignoring registers ~a):\n" ignoreRegs)
      (flush-output))
  
    (define eq (shared_state_eq (shared-state-regs ignoreRegs)))
    ; testing the instruction, just to make sure the code runs
    (define _ (@ testInstrEq eq stoke rocksalt))
    (define result (@ verifyInstrEq eq stoke rocksalt))
  
    (when details
      (displayln (pretty-result pretty-reg result))
      (displayln "")
      (flush-output))
  
    (match result
      ((None) ignoreRegs)
      ((Some r)
        (verificationLoop (remove-duplicates
          (append ignoreRegs (diff-result r)))))))
  
  (define ignoredRegs (verificationLoop ignoreRegs))
  
  (if (null? ignoredRegs)
    (printf "is equal\n")
    (printf "is equal modulo ~a\n"
      (string-join (map symbol->string ignoredRegs) ", ")))
  (flush-output)
  
  (when details
  ; (displayln "Counterexample Space:")
  ; (displayln (@ spaceInstrEq eq stoke rocksalt (void)))
    (displayln "======================================================\n")
    (flush-output)))
   
