#!/usr/bin/env racket
#lang s-exp rosette

(require "word.rkt" "extraction.rkt")
(require (prefix-in not-eax- "stoke/not-eax.rkt"))
(require (prefix-in and-eax-ebx- "stoke/and-eax-ebx.rkt"))

(provide run-stoke)

(define run-stoke (lambdas (p i s)
  (and-eax-ebx-run s)))

