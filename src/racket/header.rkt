#lang s-exp rosette

(require rosette/solver/smt/z3)
(require racket/format)

(current-bitwidth 10)
(current-solver (new z3%))

(require "extraction.rkt")
(require "rosette.rkt")

(provide (all-defined-out))
