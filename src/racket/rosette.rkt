#lang s-exp rosette

(provide solve/evaluate/concretize)

(define (concretize-solution m consts)
  (sat (for/hash ([c consts])
         (match (m c)
           [(constant _ (== integer?))
            (values c 0)]
           [(constant _ (== boolean?))
            (values c #f)]
       ;   [(constant _ (? enum? t))
       ;    (values c (enum-first t))]
           [val (values c val)]))))

(define-syntax-rule (solve/evaluate/concretize expr)
  (solve (expr void)))
; (let ([v (solve (expr void))])
;   (if (unsat? v) '(None)
;     `(Some ,(void)))))

;   (let ([v (solve/evaluate (expr void))])
;     `(Some ,(evaluate v (concretize-solution (current-solution) (symbolics v)))))


