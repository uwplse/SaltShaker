#lang s-exp rosette

(provide stoke)

(require "state.rkt" "bvex.rkt" "word.rkt" "extraction.rkt")
(define-namespace-anchor a)

(define (stoke instr-intel)
  (define instr (car instr-intel))
  (define file (make-temporary-file))
  (system* "/x86sem/src/python/instr2racket.py" instr file)
  (define ns (namespace-anchor->namespace a))
  (define-values (ub r) (parameterize ([current-namespace ns])
    (load file)
    (eval '(values uninterpreted-bits run))))
  `(ExistT ,(number->unary ub) ,(lambdas (a b) (r a b))))

