#lang s-exp rosette

(provide (all-defined-out))

(define (bit->bool bit)
  (bveq bit (bv 1 1)))

(define (bool->bit bool)
  (if bool (bv 1 1) (bv 0 1)))

(define (state 
  rax rcx rdx rbx rsp rbp rsi rdi 
  r8 r9 r10 r11 r12 r13 r14 r15 
  ymm0 ymm1 ymm2 ymm3 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 
  ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 
  cf pf af zf sf of)
  `(Build_SharedState ,rax ,rcx ,rdx ,rbx ,rsp ,rbp ,rsi ,rdi 
                      ,(bool->bit cf) ,(bool->bit pf) ,(bool->bit af) 
                      ,(bool->bit zf) ,(bool->bit sf) ,(bool->bit of)))

(define (state-rax s) (list-ref s 1))
(define (state-rcx s) (list-ref s 2))
(define (state-rdx s) (list-ref s 3))
(define (state-rbx s) (list-ref s 4))
(define (state-rsp s) (list-ref s 5))
(define (state-rbp s) (list-ref s 6))
(define (state-rsi s) (list-ref s 7))
(define (state-rdi s) (list-ref s 8))
(define (state-r8 s) (bv 0 64))
(define (state-r9 s) (bv 0 64))
(define (state-r10 s) (bv 0 64))
(define (state-r11 s) (bv 0 64))
(define (state-r12 s) (bv 0 64))
(define (state-r13 s) (bv 0 64))
(define (state-r14 s) (bv 0 64))
(define (state-r15 s) (bv 0 64))
(define (state-ymm0 s) (bv 0 256)) 
(define (state-ymm1 s) (bv 0 256))
(define (state-ymm2 s) (bv 0 256))
(define (state-ymm3 s) (bv 0 256))
(define (state-ymm4 s) (bv 0 256))
(define (state-ymm5 s) (bv 0 256))
(define (state-ymm6 s) (bv 0 256))
(define (state-ymm7 s) (bv 0 256))
(define (state-ymm8 s) (bv 0 256))
(define (state-ymm9 s) (bv 0 256))
(define (state-ymm10 s) (bv 0 256))
(define (state-ymm11 s) (bv 0 256))
(define (state-ymm12 s) (bv 0 256))
(define (state-ymm13 s) (bv 0 256))
(define (state-ymm14 s) (bv 0 256))
(define (state-ymm15 s) (bv 0 256))
(define (state-cf s) (bit->bool (list-ref s 9)))
(define (state-pf s) (bit->bool (list-ref s 10)))
(define (state-af s) (bit->bool (list-ref s 11)))
(define (state-zf s) (bit->bool (list-ref s 12)))
(define (state-sf s) (bit->bool (list-ref s 13)))
(define (state-of s) (bit->bool (list-ref s 14)))

