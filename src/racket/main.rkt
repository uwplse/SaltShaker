#!/usr/bin/env racket
#lang s-exp rosette

(require "x86sem.rkt" "rosette.rkt" "word.rkt" "extraction.rkt")

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

(define (instruction-verification-proposition)
  (displayln "Instruction verification proposition:")
  (displayln (@ instructionVerificationProposition `(Pair ,(bv 5 32) ,(bv 8 32)))))

(define (init-rtl-state)
  (displayln "Init RTL state:")
  (displayln (@ initRTLState (void))))

(define (instruction-verification)
  (displayln "Instruction verification:")
  (displayln (@ instructionVerification (void))))

(define command (vector-ref (current-command-line-arguments) 0))

(if (equal? command "construct-positive-space") (construct-positive-space)
(if (equal? command "trivial-positive-verification") (trivial-positive-verification)
(if (equal? command "find-word-proposition") (find-word-proposition)
(if (equal? command "find-word") (find-word)
(if (equal? command "word-verification") (word-verification)
(if (equal? command "instruction-verification-proposition") (instruction-verification-proposition)
(if (equal? command "init-rtl-state") (init-rtl-state)
(if (equal? command "instruction-verification") (instruction-verification)
(void)))))))))
