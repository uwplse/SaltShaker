#lang s-exp rosette

(require "extraction.rkt")

(provide word-zero word-mkint word-add word-eq word-free word-one word-unsigned-cast
         unary->number number->unary positive->number z->number)

(define (number->unary n)
  (if (= n 0) '(O) `(S ,(number->unary (- n 1)))))

(define (unary->number n)
  (match n
    ((O) 0)
    ((S n) (add1 (unary->number n)))))

(define (positive->number n)
  (match n
    ((XH) 1)
    ((XO n) (* 2 (positive->number n)))
    ((XI n) (+ 1 (* 2 (positive->number n))))))

(define (z->number n)
  (match n
    ((Z0) 0)
    ((Zpos n) (positive->number n))
    ((Zneg n) (* -1 (positive->number n)))))

(define (word-bits->bv-bits n)
  (add1 (unary->number n)))

(define word-zero (lambdas (bits)
  (bv 0 (word-bits->bv-bits bits))))

(define word-one (lambdas (bits)
  (bv 1 (word-bits->bv-bits bits))))

(define word-mkint (lambdas (bits z)
  (bv (z->number z) (word-bits->bv-bits bits))))

(define word-add (lambdas (_ x y)
  (bvadd x y)))

(define word-eq (lambdas (_ x y)
  (if (bveq x y) '(True) '(False))))

(define word-free (lambdas (bits _)
  (define-symbolic* x (bitvector (word-bits->bv-bits bits)))
  x))

(define word-unsigned-cast (lambdas (srcBits dstBits x)
  (define srcBits* (word-bits->bv-bits srcBits))
  (define dstBits* (word-bits->bv-bits dstBits))
  (if (>= srcBits* dstBits*)
    (extract dstBits* 0 x)
    (zero-extend x (bitvector dstBits*)))))
    
