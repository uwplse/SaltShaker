#lang s-exp rosette

(require "extraction.rkt" "bvex.rkt")

(provide word-free word-mkint word-zero word-one word-mone 
         word-eq word-eqdec word-lt word-ltu
         word-add word-sub word-mul word-divu word-divs word-modu word-mods
         word-castu word-casts
         word-and word-or word-xor word-shl word-shr word-shru word-ror word-rol
         unary->number number->unary positive->number z->number
         word-bits->bv-bits)

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

(define word-free (lambdas (bits _)
  (define-symbolic* x (bitvector (word-bits->bv-bits bits))) x))

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

(define word-sub (lambdas (_ x y)
  (bvsub x y)))

(define word-mul (lambdas (_ x y)
  (bvmul x y)))

(define word-divu (lambdas (_ x y)
  (bvudiv x y)))

(define word-divs (lambdas (_ x y)
  (bvsdiv x y)))

(define word-modu (lambdas (_ x y)
  (bvurem x y)))

(define word-mods (lambdas (_ x y)
  (bvsmod x y)))

(define word-eq (lambdas (_ x y)
  (if (bveq x y) '(True) '(False))))

(define word-eqdec (lambdas (_ x y)
  (if (bveq x y) '(Left) '(Right))))

(define word-lt (lambdas (_ x y)
  (if (bvslt x y) '(True) '(False))))

(define word-ltu (lambdas (_ x y)
  (if (bvult x y) '(True) '(False))))

(define word-castu (lambdas (_ newBits x)
  (bvucast (word-bits->bv-bits newBits) x)))

(define word-casts (lambdas (_ newBits x)
  (bvscast (word-bits->bv-bits newBits) x)))

(define word-or (lambdas (_ x y)
  (bvor x y)))

(define word-and (lambdas (_ x y)
  (bvand x y)))

(define word-xor (lambdas (_ x y)
  (bvxor x y)))

(define word-shl (lambdas (_ x y)
  (bvshl x y)))

(define word-shr (lambdas (_ x y)
  (bvashr x y)))

(define word-shru (lambdas (_ x y)
  (bvlshr x y)))

(define word-rol (lambdas (_ x y)
  (bvrol x y)))

(define word-ror (lambdas (_ x y)
  (bvror x y)))

