#lang s-exp rosette

(provide lambdas @ match)

(define-syntax lambdas
  (syntax-rules ()
    [(lambdas () es ...) (begin es ...)]
    [(lambdas (a as ...) es ...) (lambda (a) (lambdas (as ...) es ...))]))

(define-syntax @
  (syntax-rules ()
    [(@ e) e]
    [(@ f a as ...) (@ (f a) as ...)]))

(define (curried-apply f args)
  (if (null? args) f (curried-apply (f (car args)) (cdr args))))

(define-syntax match
  (syntax-rules ()
    [(match e) (error (string-append "Pattern match failed for " (~a e)))]
    [(match e ((t as ...) f) cs ...)
      (if (eq? 't (car e)) 
        (curried-apply (lambdas (as ...) f) (cdr e))
        (match e cs ...))]))

