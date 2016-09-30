#lang s-exp rosette

(provide bvsize extract* bvrol bvror bvucast bvscast)

(define (bvsize x)
  (bitvector-size (type-of x)))

; like extract, but the upper bound i is excluded
; i = j is an error
(define (extract* i j x)
  (extract (- i 1) j x))

(define (bvrol x y)
  (define s (bvsize x))
  (define i (modulo (bitvector->integer y) s))
  (if (= i 0) x
    (concat (extract* (- s i) 0 x) (extract* s (- s i) x))))

(define (bvror x y)
  (define s (bvsize x))
  (define i (modulo (bitvector->integer y) s))
  (if (= i 0) x
    (concat (extract* i 0 x) (extract* s i x))))

(define (bvucast newSize x)
  (if (>= (bvsize x) newSize)
    (extract* newSize 0 x)
    (zero-extend x (bitvector newSize))))

(define (bvscast newSize x)
  (if (>= (bvsize x) newSize)
    (extract* newSize 0 x)
    (sign-extend x (bitvector newSize))))

