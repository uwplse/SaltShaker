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

; (define s (((positives rosette) (number->unary bits)) (void)))

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

; (displayln (symbolic->string s))

(define (build-list f n)
  (if (= n 0)
    '()
    (cons (f) (build-list f (- n 1)))))

; (define (build-list n f)
;   (letrec 
;     ([R (lambda (k)
;       (if (= n k)
;         '()
;         (cons (f k) (R (add1 k))))
;     )]) (R 0)))

(define (symbolic-bool)
  (define-symbolic* b boolean?)
  (if b '(True) '(False)))

(define (symbolic-list k)
  (build-list (lambda () (symbolic-bool)) k))

(define t (symbolic-list 32))

(displayln t)

; (displayln (verification (number->unary bits)))

(displayln ((proposition (number->unary bits)) (void)))

; (solve/evaluate/concretize 5)

