#lang s-exp rosette

(require "extraction.rkt")

(provide word-free word-mkint word-zero word-one word-mone 
         word-eq
         word-add 
         word-unsigned-cast
         word-and word-or word-xor word-shl
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

(define word-mone (lambdas (bits)
  (bv -1 (word-bits->bv-bits bits))))

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
    (extract (sub1 dstBits*) 0 x)
    (zero-extend x (bitvector dstBits*)))))

(define word-or (lambdas (_ x y)
  (bvor x y)))

(define word-and (lambdas (_ x y)
  (bvand x y)))

(define word-xor (lambdas (bits x y)
  (bvxor x y)))

(define word-shl (lambdas (_ x y)
  (bvshl x y)))

