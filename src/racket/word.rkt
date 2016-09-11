#lang s-exp rosette

(require "extraction.rkt")

; (require base/bitvector)

(provide word-zero word-mkint word-add word-eq word-free)

(define (number->unary n)
  (if (= n 0) '(O) `(S ,(number->unary (- n 1)))))

(define (unary->number n)
  (match n
    ((O) 0)
    ((S n) (add1 (unary->number n)))))

(define (positive->number n)
  (match n
    ((xH) 1)
    ((xO n) (* 2 (positive->number n)))
    ((xO n) (+ 1 (* 2 (positive->number n))))))

(define (z->number n)
  (match n
    ((Z0) 0)
    ((Zpos n) (positive->number n))
    ((Zneg n) (* -1 (positive->number n)))))

(define (word-bits->bv-bits n)
  (add1 (unary->number n)))

(define word-zero (lambdas (bits)
  (bv 0 (word-bits->bv-bits bits))))

(define word-mkint (lambdas (bits n _)
  (bv (z->number n) (word-bits->bv-bits bits))))

(define word-add (lambdas (_ n m)
  (bvadd n m)))

(define word-eq (lambdas (_ n m)
  (if (bveq n m) '(True) '(False))))

(define word-free (lambdas (bits _)
  (define-symbolic* v (bitvector (word-bits->bv-bits bits)))
  v))

