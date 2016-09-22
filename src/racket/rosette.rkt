#lang s-exp rosette

(provide solve/evaluate/concretize)

(define (concretize-solution sol consts)
  (sat (for/hash ([c consts])
         (match (sol c)
           [(and (? constant?) (? integer?)) 
            (values c 0)]
           [(and (? constant?) (? boolean?))
            (values c #f)]
           [(and (? constant?) (? (bitvector 32)))
            (values c (bv 0 32))]
           [(and (? constant?) (? (bitvector 1)))
            (values c (bv 0 1))]
           [val 
            (values c val)]))))

(define-syntax-rule (solve/evaluate/concretize expr)
  (let* ([out (void)]
         [sol (solve (set! out (expr (void))))])
    (if (unsat? sol) '(None)
      `(Some ,(evaluate out (concretize-solution sol (symbolics out)))))))

