#!/usr/bin/env racket
#lang s-exp rosette

(require "x86sem.rkt" "rosette.rkt")

(define (number->unary n)
  (if (= n 0) '(O) `(S ,(number->unary (- n 1)))))

(define bits (string->number (vector-ref (current-command-line-arguments) 0)))

(display "Verification for all positive numbers with ")
(display bits)
(displayln " bits.")

(displayln (number->unary bits))

(define s (((positives rosette) (number->unary bits)) (void)))

(define (symbolic->string s)
  (displayln s)
  (displayln (union? s))
  (displayln (term? s))
  (displayln (constant? s))
  (displayln (expression? s))
  (displayln "------------------")
  (if (union? s)
    (string-append
      (symbolic->string (cdr (first (union-contents s))))
      " U "
      (symbolic->string (cdr (second (union-contents s)))))
    (match s
      [(constant identifier type) (~a "const" (list identifier type))]
      [(expression op child ...) (~a "expr" (cons op child))]
      [_ (~a "{" s "}" )])))

(displayln (symbolic->string s))

(define (symbolic-binary-list len) 
  


(displayln (verification (number->unary bits)))

; (displayln proposition)

; (solve/evaluate/concretize 5)

