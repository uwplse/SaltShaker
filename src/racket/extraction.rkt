#lang s-exp rosette

(provide lambdas @ match)

(define-syntax lambdas
  (syntax-rules ()
    [(lambdas (a) es ...) (lambda (a) es ...)]
    [(lambdas (a as ...) es ...) (lambda (a) (lambdas (as ...) es ...))]))

(define-syntax @
  (syntax-rules ()
    [(@ e) e]
    [(@ f a as ...) (@ (f a) as ...)]))

(define-syntax match
  (syntax-rules ()
    [(match e) (error (string-append (~a 'non-exhaustive-match) (~a e)))]
    [(match e ((t as ...) f) cs ...)
      (if (eq? 't (car e)) 
        (apply (lambda (as ...) f) (cdr e))
        (match e cs ...))]))

; syntax-case:!
; (symbol<? a

