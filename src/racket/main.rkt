#!/usr/bin/env racket
#lang s-exp rosette

(require "x86sem.rkt" "rosette.rkt" "word.rkt" "extraction.rkt")

(define (number->unary n)
  (if (= n 0) '(O) `(S ,(number->unary (- n 1)))))

(define bits0 (string->number (vector-ref (current-command-line-arguments) 0)))
(define bits1 (string->number (vector-ref (current-command-line-arguments) 1)))

(displayln (string-append "Construct positive space with " (~a bits0) " bits:"))
(displayln (@ constructPositiveSpace (number->unary (- bits0 1)) (void)))
(displayln "")
(displayln (string-append "Trivial positive verification with " (~a bits1) " bits:"))
(displayln (@ trivialPositiveVerification (number->unary (- bits1 1))))
(displayln "")
(displayln "Word verification:")
(displayln (@ wordVerification void))
(displayln "")
(displayln "Instruction verification:")
(displayln (@ instructionVerification void))

