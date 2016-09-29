#lang s-exp rosette

(provide bvror bvrol bvumod)

; TODO make sure mod for signed is equal to unsigned
(define (bvumod x y)
  (bvsmod x y))

; TODO replace shift with rotation
(define (bvrol x y)
  (bvshl x y))

(define (bvror x y)
  (bvlshr x y))

