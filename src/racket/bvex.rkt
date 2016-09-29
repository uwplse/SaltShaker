#lang s-exp rosette

(provide bvror bvrol bvumod)

(define (bvumod x y)
  (bvurem x y))

; TODO replace shift with rotation
(define (bvrol x y)
  (bvshl x y))

(define (bvror x y)
  (bvlshr x y))

