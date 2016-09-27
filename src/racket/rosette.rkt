#lang s-exp rosette

(require
  racket/hash
  (only-in rosette term-cache constant? model sat)
  (only-in rosette/base/core/type solvable-default get-type))

(provide solve/evaluate/concretize)

(define concretize
  (case-lambda
    [(sol)
     (concretize sol (filter constant? (hash-values (term-cache))))]
    [(sol consts)
     (match sol
       [(model bindings)
        (sat
         (hash-union
          bindings
          (for/hash ([c consts] #:unless (dict-has-key? bindings c))
            (values c (solvable-default (get-type c))))))]
       [_ (error 'complete "expected a sat? solution, given ~a" sol)])]))

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
  (let* ([out (void)]
         [sol (solve (set! out (expr (void))))])
    (if (unsat? sol) '(Nil)
      `(Cons ,(evaluate out (concretize sol)) (Nil)))))

; (let ([v (solve (expr void))])
;   (if (unsat? v) '(None)
;     `(Some ,(void)))))

;   (let ([v (solve/evaluate (expr void))])
;     `(Some ,(evaluate v (concretize-solution (current-solution) (symbolics v)))))


