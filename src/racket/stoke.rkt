#!/usr/bin/env racket
#lang s-exp rosette

(require "word.rkt" "extraction.rkt")
(require (prefix-in not-eax- "stoke/not-eax.rkt"))

(provide run-stoke)

(define run-stoke (lambdas (p i s)
  (not-eax-run s)))

