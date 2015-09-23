#lang s-exp rosette

(require rosette/solver/smt/z3)
(require racket/format)

(current-bitwidth 10)
(current-solver (new z3%))

(require "extraction.rkt")
(require "rosette.rkt")

(provide verification)

(define __ (void))

(define xorb (lambdas (b1 b2)
  (match b1
     ((True)
       (match b2
          ((True) `(False))
          ((False) `(True))))
     ((False)
       (match b2
          ((True) `(True))
          ((False) `(False)))))))

(define negb (lambda (b)
  (match b
     ((True) `(False))
     ((False) `(True)))))

(define fst (lambda (p)
  (match p
     ((Pair x y) x))))

(define snd (lambda (p)
  (match p
     ((Pair x y) y))))

(define app (lambdas (l m)
  (match l
     ((Nil) m)
     ((Cons a l1) `(Cons ,a ,(@ app l1 m))))))
  
(define compOpp (lambda (r)
  (match r
     ((Eq) `(Eq))
     ((Lt) `(Gt))
     ((Gt) `(Lt)))))

(define compareSpec2Type (lambda (c)
  (match c
     ((Eq) `(CompEqT))
     ((Lt) `(CompLtT))
     ((Gt) `(CompGtT)))))

(define compSpec2Type (lambdas (x y c) (compareSpec2Type c)))

(define id (lambda (x) x))

(define plus (lambdas (n m)
  (match n
     ((O) m)
     ((S p) `(S ,(@ plus p m))))))
  
(define minus (lambdas (n m)
  (match n
     ((O) n)
     ((S k)
       (match m
          ((O) n)
          ((S l) (@ minus k l)))))))
  
(define nat_iter (lambdas (n f x)
  (match n
     ((O) x)
     ((S n~) (f (@ nat_iter n~ f x))))))
  
(define bool_dec (lambdas (b1 b2)
  (match b1
     ((True)
       (match b2
          ((True) `(Left))
          ((False) `(Right))))
     ((False)
       (match b2
          ((True) `(Right))
          ((False) `(Left)))))))

(define eqb (lambdas (b1 b2)
  (match b1
     ((True)
       (match b2
          ((True) `(True))
          ((False) `(False))))
     ((False)
       (match b2
          ((True) `(False))
          ((False) `(True)))))))

(define iff_reflect (lambda (b)
  (match b
     ((True) `(ReflectT))
     ((False) `(ReflectF)))))

(define rev (lambda (l)
  (match l
     ((Nil) `(Nil))
     ((Cons x l~) (@ app (rev l~) `(Cons ,x ,`(Nil)))))))
  
(define map (lambdas (f l)
  (match l
     ((Nil) `(Nil))
     ((Cons a t) `(Cons ,(f a) ,(@ map f t))))))
  
(define succ (lambda (x)
  (match x
     ((XI p) `(XO ,(succ p)))
     ((XO p) `(XI ,p))
     ((XH) `(XO ,`(XH))))))
  
(define add (lambdas (x y)
  (match x
     ((XI p)
       (match y
          ((XI q) `(XO ,(@ add_carry p q)))
          ((XO q) `(XI ,(@ add p q)))
          ((XH) `(XO ,(succ p)))))
     ((XO p)
       (match y
          ((XI q) `(XI ,(@ add p q)))
          ((XO q) `(XO ,(@ add p q)))
          ((XH) `(XI ,p))))
     ((XH)
       (match y
          ((XI q) `(XO ,(succ q)))
          ((XO q) `(XI ,q))
          ((XH) `(XO ,`(XH))))))))
  
(define add_carry (lambdas (x y)
  (match x
     ((XI p)
       (match y
          ((XI q) `(XI ,(@ add_carry p q)))
          ((XO q) `(XO ,(@ add_carry p q)))
          ((XH) `(XI ,(succ p)))))
     ((XO p)
       (match y
          ((XI q) `(XO ,(@ add_carry p q)))
          ((XO q) `(XI ,(@ add p q)))
          ((XH) `(XO ,(succ p)))))
     ((XH)
       (match y
          ((XI q) `(XI ,(succ q)))
          ((XO q) `(XO ,(succ q)))
          ((XH) `(XI ,`(XH))))))))
  
(define pred_double (lambda (x)
  (match x
     ((XI p) `(XI ,`(XO ,p)))
     ((XO p) `(XI ,(pred_double p)))
     ((XH) `(XH)))))
  
(define pred (lambda (x)
  (match x
     ((XI p) `(XO ,p))
     ((XO p) (pred_double p))
     ((XH) `(XH)))))

(define pred_N (lambda (x)
  (match x
     ((XI p) `(Npos ,`(XO ,p)))
     ((XO p) `(Npos ,(pred_double p)))
     ((XH) `(N0)))))

(define mask_rect (lambdas (f f0 f1 m)
  (match m
     ((IsNul) f)
     ((IsPos x) (f0 x))
     ((IsNeg) f1))))

(define mask_rec (lambdas (f f0 f1 m)
  (match m
     ((IsNul) f)
     ((IsPos x) (f0 x))
     ((IsNeg) f1))))

(define succ_double_mask (lambda (x)
  (match x
     ((IsNul) `(IsPos ,`(XH)))
     ((IsPos p) `(IsPos ,`(XI ,p)))
     ((IsNeg) `(IsNeg)))))

(define double_mask (lambda (x)
  (match x
     ((IsNul) `(IsNul))
     ((IsPos p) `(IsPos ,`(XO ,p)))
     ((IsNeg) `(IsNeg)))))

(define double_pred_mask (lambda (x)
  (match x
     ((XI p) `(IsPos ,`(XO ,`(XO ,p))))
     ((XO p) `(IsPos ,`(XO ,(pred_double p))))
     ((XH) `(IsNul)))))

(define pred_mask (lambda (p)
  (match p
     ((IsNul) `(IsNeg))
     ((IsPos q)
       (match q
          ((XI p0) `(IsPos ,(pred q)))
          ((XO p0) `(IsPos ,(pred q)))
          ((XH) `(IsNul))))
     ((IsNeg) `(IsNeg)))))

(define sub_mask (lambdas (x y)
  (match x
     ((XI p)
       (match y
          ((XI q) (double_mask (@ sub_mask p q)))
          ((XO q) (succ_double_mask (@ sub_mask p q)))
          ((XH) `(IsPos ,`(XO ,p)))))
     ((XO p)
       (match y
          ((XI q) (succ_double_mask (@ sub_mask_carry p q)))
          ((XO q) (double_mask (@ sub_mask p q)))
          ((XH) `(IsPos ,(pred_double p)))))
     ((XH)
       (match y
          ((XI p) `(IsNeg))
          ((XO p) `(IsNeg))
          ((XH) `(IsNul)))))))
  
(define sub_mask_carry (lambdas (x y)
  (match x
     ((XI p)
       (match y
          ((XI q) (succ_double_mask (@ sub_mask_carry p q)))
          ((XO q) (double_mask (@ sub_mask p q)))
          ((XH) `(IsPos ,(pred_double p)))))
     ((XO p)
       (match y
          ((XI q) (double_mask (@ sub_mask_carry p q)))
          ((XO q) (succ_double_mask (@ sub_mask_carry p q)))
          ((XH) (double_pred_mask p))))
     ((XH) `(IsNeg)))))
  
(define sub (lambdas (x y)
  (match (@ sub_mask x y)
     ((IsNul) `(XH))
     ((IsPos z) z)
     ((IsNeg) `(XH)))))

(define mul (lambdas (x y)
  (match x
     ((XI p) (@ add y `(XO ,(@ mul p y))))
     ((XO p) `(XO ,(@ mul p y)))
     ((XH) y))))
  
(define iter (lambdas (n f x)
  (match n
     ((XI n~) (f (@ iter n~ f (@ iter n~ f x))))
     ((XO n~) (@ iter n~ f (@ iter n~ f x)))
     ((XH) (f x)))))
  
(define pow (lambdas (x y) (@ iter y (mul x) `(XH))))

(define square (lambda (p)
  (match p
     ((XI p0) `(XI ,`(XO ,(@ add (square p0) p0))))
     ((XO p0) `(XO ,`(XO ,(square p0))))
     ((XH) `(XH)))))
  
(define div2 (lambda (p)
  (match p
     ((XI p0) p0)
     ((XO p0) p0)
     ((XH) `(XH)))))

(define div2_up (lambda (p)
  (match p
     ((XI p0) (succ p0))
     ((XO p0) p0)
     ((XH) `(XH)))))

(define size_nat (lambda (p)
  (match p
     ((XI p0) `(S ,(size_nat p0)))
     ((XO p0) `(S ,(size_nat p0)))
     ((XH) `(S ,`(O))))))
  
(define size (lambda (p)
  (match p
     ((XI p0) (succ (size p0)))
     ((XO p0) (succ (size p0)))
     ((XH) `(XH)))))
  
(define compare_cont (lambdas (x y r)
  (match x
     ((XI p)
       (match y
          ((XI q) (@ compare_cont p q r))
          ((XO q) (@ compare_cont p q `(Gt)))
          ((XH) `(Gt))))
     ((XO p)
       (match y
          ((XI q) (@ compare_cont p q `(Lt)))
          ((XO q) (@ compare_cont p q r))
          ((XH) `(Gt))))
     ((XH)
       (match y
          ((XI q) `(Lt))
          ((XO q) `(Lt))
          ((XH) r))))))
  
(define compare (lambdas (x y) (@ compare_cont x y `(Eq))))

(define min (lambdas (p p~)
  (match (@ compare p p~)
     ((Eq) p)
     ((Lt) p)
     ((Gt) p~))))

(define max (lambdas (p p~)
  (match (@ compare p p~)
     ((Eq) p~)
     ((Lt) p~)
     ((Gt) p))))

(define eqb0 (lambdas (p q)
  (match p
     ((XI p0)
       (match q
          ((XI q0) (@ eqb0 p0 q0))
          ((XO p1) `(False))
          ((XH) `(False))))
     ((XO p0)
       (match q
          ((XI p1) `(False))
          ((XO q0) (@ eqb0 p0 q0))
          ((XH) `(False))))
     ((XH)
       (match q
          ((XI p0) `(False))
          ((XO p0) `(False))
          ((XH) `(True)))))))
  
(define leb (lambdas (x y)
  (match (@ compare x y)
     ((Eq) `(True))
     ((Lt) `(True))
     ((Gt) `(False)))))

(define ltb (lambdas (x y)
  (match (@ compare x y)
     ((Eq) `(False))
     ((Lt) `(True))
     ((Gt) `(False)))))

(define sqrtrem_step (lambdas (f g p)
  (match p
     ((Pair s y)
       (match y
          ((IsNul) `(Pair ,`(XO ,s)
            ,(@ sub_mask (g (f `(XH))) `(XO ,`(XO ,`(XH))))))
          ((IsPos r)
            (let ((s~ `(XI ,`(XO ,s))))
              (let ((r~ (g (f r))))
                (match (@ leb s~ r~)
                   ((True) `(Pair ,`(XI ,s) ,(@ sub_mask r~ s~)))
                   ((False) `(Pair ,`(XO ,s) ,`(IsPos ,r~)))))))
          ((IsNeg) `(Pair ,`(XO ,s)
            ,(@ sub_mask (g (f `(XH))) `(XO ,`(XO ,`(XH)))))))))))

(define sqrtrem (lambda (p)
  (match p
     ((XI p0)
       (match p0
          ((XI p1)
            (@ sqrtrem_step (lambda (x) `(XI ,x)) (lambda (x) `(XI ,x))
              (sqrtrem p1)))
          ((XO p1)
            (@ sqrtrem_step (lambda (x) `(XO ,x)) (lambda (x) `(XI ,x))
              (sqrtrem p1)))
          ((XH) `(Pair ,`(XH) ,`(IsPos ,`(XO ,`(XH)))))))
     ((XO p0)
       (match p0
          ((XI p1)
            (@ sqrtrem_step (lambda (x) `(XI ,x)) (lambda (x) `(XO ,x))
              (sqrtrem p1)))
          ((XO p1)
            (@ sqrtrem_step (lambda (x) `(XO ,x)) (lambda (x) `(XO ,x))
              (sqrtrem p1)))
          ((XH) `(Pair ,`(XH) ,`(IsPos ,`(XH))))))
     ((XH) `(Pair ,`(XH) ,`(IsNul))))))
  
(define sqrt (lambda (p) (fst (sqrtrem p))))

(define gcdn (lambdas (n a b)
  (match n
     ((O) `(XH))
     ((S n0)
       (match a
          ((XI a~)
            (match b
               ((XI b~)
                 (match (@ compare a~ b~)
                    ((Eq) a)
                    ((Lt) (@ gcdn n0 (@ sub b~ a~) a))
                    ((Gt) (@ gcdn n0 (@ sub a~ b~) b))))
               ((XO b0) (@ gcdn n0 a b0))
               ((XH) `(XH))))
          ((XO a0)
            (match b
               ((XI p) (@ gcdn n0 a0 b))
               ((XO b0) `(XO ,(@ gcdn n0 a0 b0)))
               ((XH) `(XH))))
          ((XH) `(XH)))))))
  
(define gcd (lambdas (a b) (@ gcdn (@ plus (size_nat a) (size_nat b)) a b)))

(define ggcdn (lambdas (n a b)
  (match n
     ((O) `(Pair ,`(XH) ,`(Pair ,a ,b)))
     ((S n0)
       (match a
          ((XI a~)
            (match b
               ((XI b~)
                 (match (@ compare a~ b~)
                    ((Eq) `(Pair ,a ,`(Pair ,`(XH) ,`(XH))))
                    ((Lt)
                      (match (@ ggcdn n0 (@ sub b~ a~) a)
                         ((Pair g p)
                           (match p
                              ((Pair ba aa) `(Pair ,g ,`(Pair ,aa
                                ,(@ add aa `(XO ,ba)))))))))
                    ((Gt)
                      (match (@ ggcdn n0 (@ sub a~ b~) b)
                         ((Pair g p)
                           (match p
                              ((Pair ab bb) `(Pair ,g ,`(Pair
                                ,(@ add bb `(XO ,ab)) ,bb)))))))))
               ((XO b0)
                 (match (@ ggcdn n0 a b0)
                    ((Pair g p)
                      (match p
                         ((Pair aa bb) `(Pair ,g ,`(Pair ,aa ,`(XO ,bb))))))))
               ((XH) `(Pair ,`(XH) ,`(Pair ,a ,`(XH))))))
          ((XO a0)
            (match b
               ((XI p)
                 (match (@ ggcdn n0 a0 b)
                    ((Pair g p0)
                      (match p0
                         ((Pair aa bb) `(Pair ,g ,`(Pair ,`(XO ,aa) ,bb)))))))
               ((XO b0)
                 (match (@ ggcdn n0 a0 b0)
                    ((Pair g p) `(Pair ,`(XO ,g) ,p))))
               ((XH) `(Pair ,`(XH) ,`(Pair ,a ,`(XH))))))
          ((XH) `(Pair ,`(XH) ,`(Pair ,`(XH) ,b))))))))
  
(define ggcd (lambdas (a b)
  (@ ggcdn (@ plus (size_nat a) (size_nat b)) a b)))

(define nsucc_double (lambda (x)
  (match x
     ((N0) `(Npos ,`(XH)))
     ((Npos p) `(Npos ,`(XI ,p))))))

(define ndouble (lambda (n)
  (match n
     ((N0) `(N0))
     ((Npos p) `(Npos ,`(XO ,p))))))

(define lor (lambdas (p q)
  (match p
     ((XI p0)
       (match q
          ((XI q0) `(XI ,(@ lor p0 q0)))
          ((XO q0) `(XI ,(@ lor p0 q0)))
          ((XH) p)))
     ((XO p0)
       (match q
          ((XI q0) `(XI ,(@ lor p0 q0)))
          ((XO q0) `(XO ,(@ lor p0 q0)))
          ((XH) `(XI ,p0))))
     ((XH)
       (match q
          ((XI p0) q)
          ((XO q0) `(XI ,q0))
          ((XH) q))))))
  
(define land (lambdas (p q)
  (match p
     ((XI p0)
       (match q
          ((XI q0) (nsucc_double (@ land p0 q0)))
          ((XO q0) (ndouble (@ land p0 q0)))
          ((XH) `(Npos ,`(XH)))))
     ((XO p0)
       (match q
          ((XI q0) (ndouble (@ land p0 q0)))
          ((XO q0) (ndouble (@ land p0 q0)))
          ((XH) `(N0))))
     ((XH)
       (match q
          ((XI p0) `(Npos ,`(XH)))
          ((XO q0) `(N0))
          ((XH) `(Npos ,`(XH))))))))
  
(define ldiff (lambdas (p q)
  (match p
     ((XI p0)
       (match q
          ((XI q0) (ndouble (@ ldiff p0 q0)))
          ((XO q0) (nsucc_double (@ ldiff p0 q0)))
          ((XH) `(Npos ,`(XO ,p0)))))
     ((XO p0)
       (match q
          ((XI q0) (ndouble (@ ldiff p0 q0)))
          ((XO q0) (ndouble (@ ldiff p0 q0)))
          ((XH) `(Npos ,p))))
     ((XH)
       (match q
          ((XI p0) `(N0))
          ((XO q0) `(Npos ,`(XH)))
          ((XH) `(N0)))))))
  
(define lxor (lambdas (p q)
  (match p
     ((XI p0)
       (match q
          ((XI q0) (ndouble (@ lxor p0 q0)))
          ((XO q0) (nsucc_double (@ lxor p0 q0)))
          ((XH) `(Npos ,`(XO ,p0)))))
     ((XO p0)
       (match q
          ((XI q0) (nsucc_double (@ lxor p0 q0)))
          ((XO q0) (ndouble (@ lxor p0 q0)))
          ((XH) `(Npos ,`(XI ,p0)))))
     ((XH)
       (match q
          ((XI q0) `(Npos ,`(XO ,q0)))
          ((XO q0) `(Npos ,`(XI ,q0)))
          ((XH) `(N0)))))))
  
(define shiftl_nat (lambdas (p n) (@ nat_iter n (lambda (x) `(XO ,x)) p)))

(define shiftr_nat (lambdas (p n) (@ nat_iter n div2 p)))

(define shiftl (lambdas (p n)
  (match n
     ((N0) p)
     ((Npos n0) (@ iter n0 (lambda (x) `(XO ,x)) p)))))

(define shiftr (lambdas (p n)
  (match n
     ((N0) p)
     ((Npos n0) (@ iter n0 div2 p)))))

(define testbit_nat (lambdas (p n)
  (match p
     ((XI p0)
       (match n
          ((O) `(True))
          ((S n~) (@ testbit_nat p0 n~))))
     ((XO p0)
       (match n
          ((O) `(False))
          ((S n~) (@ testbit_nat p0 n~))))
     ((XH)
       (match n
          ((O) `(True))
          ((S n0) `(False)))))))
  
(define testbit (lambdas (p n)
  (match p
     ((XI p0)
       (match n
          ((N0) `(True))
          ((Npos n0) (@ testbit p0 (pred_N n0)))))
     ((XO p0)
       (match n
          ((N0) `(False))
          ((Npos n0) (@ testbit p0 (pred_N n0)))))
     ((XH)
       (match n
          ((N0) `(True))
          ((Npos p0) `(False)))))))
  
(define iter_op (lambdas (op p a)
  (match p
     ((XI p0) (@ op a (@ iter_op op p0 (@ op a a))))
     ((XO p0) (@ iter_op op p0 (@ op a a)))
     ((XH) a))))
  
(define to_nat (lambda (x) (@ iter_op plus x `(S ,`(O)))))

(define of_nat (lambda (n)
  (match n
     ((O) `(XH))
     ((S x)
       (match x
          ((O) `(XH))
          ((S n0) (succ (of_nat x))))))))
  
(define of_succ_nat (lambda (n)
  (match n
     ((O) `(XH))
     ((S x) (succ (of_succ_nat x))))))
  
(define eq_dec (lambdas (p y0)
  (match p
     ((XI p0)
       (match y0
          ((XI p1)
            (match (@ eq_dec p0 p1)
               ((Left) `(Left))
               ((Right) `(Right))))
          ((XO p1) `(Right))
          ((XH) `(Right))))
     ((XO p0)
       (match y0
          ((XI p1) `(Right))
          ((XO p1)
            (match (@ eq_dec p0 p1)
               ((Left) `(Left))
               ((Right) `(Right))))
          ((XH) `(Right))))
     ((XH)
       (match y0
          ((XI p0) `(Right))
          ((XO p0) `(Right))
          ((XH) `(Left)))))))
  
(define peano_rect (lambdas (a f p)
  (let ((f2
    (@ peano_rect (@ f `(XH) a) (lambdas (p0 x)
      (@ f (succ `(XO ,p0)) (@ f `(XO ,p0) x))))))
    (match p
       ((XI q) (@ f `(XO ,q) (f2 q)))
       ((XO q) (f2 q))
       ((XH) a)))))
  
(define peano_rec peano_rect)

(define peanoView_rect (lambdas (f f0 p p0)
  (match p0
     ((PeanoOne) f)
     ((PeanoSucc p1 p2) (@ f0 p1 p2 (@ peanoView_rect f f0 p1 p2))))))
  
(define peanoView_rec (lambdas (f f0 p p0)
  (match p0
     ((PeanoOne) f)
     ((PeanoSucc p1 p2) (@ f0 p1 p2 (@ peanoView_rec f f0 p1 p2))))))
  
(define peanoView_xO (lambdas (p q)
  (match q
     ((PeanoOne) `(PeanoSucc ,`(XH) ,`(PeanoOne)))
     ((PeanoSucc p0 q0) `(PeanoSucc ,(succ `(XO ,p0)) ,`(PeanoSucc ,`(XO ,p0)
       ,(@ peanoView_xO p0 q0)))))))
  
(define peanoView_xI (lambdas (p q)
  (match q
     ((PeanoOne) `(PeanoSucc ,(succ `(XH)) ,`(PeanoSucc ,`(XH)
       ,`(PeanoOne))))
     ((PeanoSucc p0 q0) `(PeanoSucc ,(succ `(XI ,p0)) ,`(PeanoSucc ,`(XI ,p0)
       ,(@ peanoView_xI p0 q0)))))))
  
(define peanoView (lambda (p)
  (match p
     ((XI p0) (@ peanoView_xI p0 (peanoView p0)))
     ((XO p0) (@ peanoView_xO p0 (peanoView p0)))
     ((XH) `(PeanoOne)))))
  
(define peanoView_iter (lambdas (a f p q)
  (match q
     ((PeanoOne) a)
     ((PeanoSucc p0 q0) (@ f p0 (@ peanoView_iter a f p0 q0))))))
  
(define eqb_spec (lambdas (x y) (iff_reflect (@ eqb0 x y))))

(define switch_Eq (lambdas (c c~)
  (match c~
     ((Eq) c)
     ((Lt) `(Lt))
     ((Gt) `(Gt)))))

(define mask2cmp (lambda (p)
  (match p
     ((IsNul) `(Eq))
     ((IsPos p0) `(Gt))
     ((IsNeg) `(Lt)))))

(define leb_spec0 (lambdas (x y) (iff_reflect (@ leb x y))))

(define ltb_spec0 (lambdas (x y) (iff_reflect (@ ltb x y))))

(define max_case_strong (lambdas (n m compat hl hr)
  (let ((c (@ compSpec2Type n m (@ compare n m))))
    (match c
       ((CompEqT) (@ compat m (@ max n m) __ (hr __)))
       ((CompLtT) (@ compat m (@ max n m) __ (hr __)))
       ((CompGtT) (@ compat n (@ max n m) __ (hl __)))))))

(define max_case (lambdas (n m x x0 x1)
  (@ max_case_strong n m x (lambda (_) x0) (lambda (_) x1))))

(define max_dec (lambdas (n m)
  (@ max_case n m (lambdas (x y _ h0)
    (match h0
       ((Left) `(Left))
       ((Right) `(Right)))) `(Left) `(Right))))

(define min_case_strong (lambdas (n m compat hl hr)
  (let ((c (@ compSpec2Type n m (@ compare n m))))
    (match c
       ((CompEqT) (@ compat n (@ min n m) __ (hl __)))
       ((CompLtT) (@ compat n (@ min n m) __ (hl __)))
       ((CompGtT) (@ compat m (@ min n m) __ (hr __)))))))

(define min_case (lambdas (n m x x0 x1)
  (@ min_case_strong n m x (lambda (_) x0) (lambda (_) x1))))

(define min_dec (lambdas (n m)
  (@ min_case n m (lambdas (x y _ h0)
    (match h0
       ((Left) `(Left))
       ((Right) `(Right)))) `(Left) `(Right))))

(define max_case_strong0 (lambdas (n m x x0)
  (@ max_case_strong n m (lambdas (x1 y _ x2) x2) x x0)))

(define max_case0 (lambdas (n m x x0)
  (@ max_case_strong0 n m (lambda (_) x) (lambda (_) x0))))

(define max_dec0 max_dec)

(define min_case_strong0 (lambdas (n m x x0)
  (@ min_case_strong n m (lambdas (x1 y _ x2) x2) x x0)))

(define min_case0 (lambdas (n m x x0)
  (@ min_case_strong0 n m (lambda (_) x) (lambda (_) x0))))

(define min_dec0 min_dec)

(define zero `(N0))

(define one `(Npos ,`(XH)))

(define two `(Npos ,`(XO ,`(XH))))

(define succ_double (lambda (x)
  (match x
     ((N0) `(Npos ,`(XH)))
     ((Npos p) `(Npos ,`(XI ,p))))))

(define double (lambda (n)
  (match n
     ((N0) `(N0))
     ((Npos p) `(Npos ,`(XO ,p))))))

(define succ0 (lambda (n)
  (match n
     ((N0) `(Npos ,`(XH)))
     ((Npos p) `(Npos ,(succ p))))))

(define pred0 (lambda (n)
  (match n
     ((N0) `(N0))
     ((Npos p) (pred_N p)))))

(define succ_pos (lambda (n)
  (match n
     ((N0) `(XH))
     ((Npos p) (succ p)))))

(define add0 (lambdas (n m)
  (match n
     ((N0) m)
     ((Npos p)
       (match m
          ((N0) n)
          ((Npos q) `(Npos ,(@ add p q))))))))

(define sub0 (lambdas (n m)
  (match n
     ((N0) `(N0))
     ((Npos n~)
       (match m
          ((N0) n)
          ((Npos m~)
            (match (@ sub_mask n~ m~)
               ((IsNul) `(N0))
               ((IsPos p) `(Npos ,p))
               ((IsNeg) `(N0)))))))))

(define mul0 (lambdas (n m)
  (match n
     ((N0) `(N0))
     ((Npos p)
       (match m
          ((N0) `(N0))
          ((Npos q) `(Npos ,(@ mul p q))))))))

(define compare0 (lambdas (n m)
  (match n
     ((N0)
       (match m
          ((N0) `(Eq))
          ((Npos m~) `(Lt))))
     ((Npos n~)
       (match m
          ((N0) `(Gt))
          ((Npos m~) (@ compare n~ m~)))))))

(define eqb1 (lambdas (n m)
  (match n
     ((N0)
       (match m
          ((N0) `(True))
          ((Npos p) `(False))))
     ((Npos p)
       (match m
          ((N0) `(False))
          ((Npos q) (@ eqb0 p q)))))))
  
(define leb0 (lambdas (x y)
  (match (@ compare0 x y)
     ((Eq) `(True))
     ((Lt) `(True))
     ((Gt) `(False)))))

(define ltb0 (lambdas (x y)
  (match (@ compare0 x y)
     ((Eq) `(False))
     ((Lt) `(True))
     ((Gt) `(False)))))

(define min0 (lambdas (n n~)
  (match (@ compare0 n n~)
     ((Eq) n)
     ((Lt) n)
     ((Gt) n~))))

(define max0 (lambdas (n n~)
  (match (@ compare0 n n~)
     ((Eq) n~)
     ((Lt) n~)
     ((Gt) n))))

(define div0 (lambda (n)
  (match n
     ((N0) `(N0))
     ((Npos p0)
       (match p0
          ((XI p) `(Npos ,p))
          ((XO p) `(Npos ,p))
          ((XH) `(N0)))))))

(define even (lambda (n)
  (match n
     ((N0) `(True))
     ((Npos p)
       (match p
          ((XI p0) `(False))
          ((XO p0) `(True))
          ((XH) `(False)))))))

(define odd (lambda (n) (negb (even n))))

(define pow0 (lambdas (n p)
  (match p
     ((N0) `(Npos ,`(XH)))
     ((Npos p0)
       (match n
          ((N0) `(N0))
          ((Npos q) `(Npos ,(@ pow q p0))))))))

(define square0 (lambda (n)
  (match n
     ((N0) `(N0))
     ((Npos p) `(Npos ,(square p))))))

(define log2 (lambda (n)
  (match n
     ((N0) `(N0))
     ((Npos p0)
       (match p0
          ((XI p) `(Npos ,(size p)))
          ((XO p) `(Npos ,(size p)))
          ((XH) `(N0)))))))

(define size0 (lambda (n)
  (match n
     ((N0) `(N0))
     ((Npos p) `(Npos ,(size p))))))

(define size_nat0 (lambda (n)
  (match n
     ((N0) `(O))
     ((Npos p) (size_nat p)))))

(define pos_div_eucl (lambdas (a b)
  (match a
     ((XI a~)
       (match (@ pos_div_eucl a~ b)
          ((Pair q r)
            (let ((r~ (succ_double r)))
              (match (@ leb0 b r~)
                 ((True) `(Pair ,(succ_double q) ,(@ sub0 r~ b)))
                 ((False) `(Pair ,(double q) ,r~)))))))
     ((XO a~)
       (match (@ pos_div_eucl a~ b)
          ((Pair q r)
            (let ((r~ (double r)))
              (match (@ leb0 b r~)
                 ((True) `(Pair ,(succ_double q) ,(@ sub0 r~ b)))
                 ((False) `(Pair ,(double q) ,r~)))))))
     ((XH)
       (match b
          ((N0) `(Pair ,`(N0) ,`(Npos ,`(XH))))
          ((Npos p)
            (match p
               ((XI p0) `(Pair ,`(N0) ,`(Npos ,`(XH))))
               ((XO p0) `(Pair ,`(N0) ,`(Npos ,`(XH))))
               ((XH) `(Pair ,`(Npos ,`(XH)) ,`(N0))))))))))
  
(define div_eucl (lambdas (a b)
  (match a
     ((N0) `(Pair ,`(N0) ,`(N0)))
     ((Npos na)
       (match b
          ((N0) `(Pair ,`(N0) ,a))
          ((Npos p) (@ pos_div_eucl na b)))))))

(define div (lambdas (a b) (fst (@ div_eucl a b))))

(define modulo (lambdas (a b) (snd (@ div_eucl a b))))

(define gcd0 (lambdas (a b)
  (match a
     ((N0) b)
     ((Npos p)
       (match b
          ((N0) a)
          ((Npos q) `(Npos ,(@ gcd p q))))))))

(define ggcd0 (lambdas (a b)
  (match a
     ((N0) `(Pair ,b ,`(Pair ,`(N0) ,`(Npos ,`(XH)))))
     ((Npos p)
       (match b
          ((N0) `(Pair ,a ,`(Pair ,`(Npos ,`(XH)) ,`(N0))))
          ((Npos q)
            (match (@ ggcd p q)
               ((Pair g p0)
                 (match p0
                    ((Pair aa bb) `(Pair ,`(Npos ,g) ,`(Pair ,`(Npos ,aa)
                      ,`(Npos ,bb)))))))))))))

(define sqrtrem0 (lambda (n)
  (match n
     ((N0) `(Pair ,`(N0) ,`(N0)))
     ((Npos p)
       (match (sqrtrem p)
          ((Pair s m)
            (match m
               ((IsNul) `(Pair ,`(Npos ,s) ,`(N0)))
               ((IsPos r) `(Pair ,`(Npos ,s) ,`(Npos ,r)))
               ((IsNeg) `(Pair ,`(Npos ,s) ,`(N0))))))))))

(define sqrt0 (lambda (n)
  (match n
     ((N0) `(N0))
     ((Npos p) `(Npos ,(sqrt p))))))

(define lor0 (lambdas (n m)
  (match n
     ((N0) m)
     ((Npos p)
       (match m
          ((N0) n)
          ((Npos q) `(Npos ,(@ lor p q))))))))

(define land0 (lambdas (n m)
  (match n
     ((N0) `(N0))
     ((Npos p)
       (match m
          ((N0) `(N0))
          ((Npos q) (@ land p q)))))))

(define ldiff0 (lambdas (n m)
  (match n
     ((N0) `(N0))
     ((Npos p)
       (match m
          ((N0) n)
          ((Npos q) (@ ldiff p q)))))))
  
(define lxor0 (lambdas (n m)
  (match n
     ((N0) m)
     ((Npos p)
       (match m
          ((N0) n)
          ((Npos q) (@ lxor p q)))))))

(define shiftl_nat0 (lambdas (a n) (@ nat_iter n double a)))

(define shiftr_nat0 (lambdas (a n) (@ nat_iter n div0 a)))

(define shiftl0 (lambdas (a n)
  (match a
     ((N0) `(N0))
     ((Npos a0) `(Npos ,(@ shiftl a0 n))))))

(define shiftr0 (lambdas (a n)
  (match n
     ((N0) a)
     ((Npos p) (@ iter p div0 a)))))

(define testbit_nat0 (lambda (a)
  (match a
     ((N0) (lambda (x) `(False)))
     ((Npos p) (testbit_nat p)))))

(define testbit0 (lambdas (a n)
  (match a
     ((N0) `(False))
     ((Npos p) (@ testbit p n)))))

(define to_nat0 (lambda (a)
  (match a
     ((N0) `(O))
     ((Npos p) (to_nat p)))))

(define of_nat0 (lambda (n)
  (match n
     ((O) `(N0))
     ((S n~) `(Npos ,(of_succ_nat n~))))))

(define iter0 (lambdas (n f x)
  (match n
     ((N0) x)
     ((Npos p) (@ iter p f x)))))

(define eq_dec0 (lambdas (n m)
  (match n
     ((N0)
       (match m
          ((N0) `(Left))
          ((Npos p) `(Right))))
     ((Npos x)
       (match m
          ((N0) `(Right))
          ((Npos p0)
            (match (@ eq_dec x p0)
               ((Left) `(Left))
               ((Right) `(Right)))))))))

(define discr (lambda (n)
  (match n
     ((N0) `(Inright))
     ((Npos p) `(Inleft ,p)))))

(define binary_rect (lambdas (f0 f2 fS2 n)
  (let ((f2~ (lambda (p) (f2 `(Npos ,p)))))
    (let ((fS2~ (lambda (p) (fS2 `(Npos ,p)))))
      (match n
         ((N0) f0)
         ((Npos p)
           (letrec ((f
                   (lambda (p0)
                   (match p0
                      ((XI p1) (@ fS2~ p1 (f p1)))
                      ((XO p1) (@ f2~ p1 (f p1)))
                      ((XH) (@ fS2 `(N0) f0))))))
                   (f p))))))))

(define binary_rec binary_rect)

(define peano_rect0 (lambdas (f0 f n)
  (let ((f~ (lambda (p) (f `(Npos ,p)))))
    (match n
       ((N0) f0)
       ((Npos p) (@ peano_rect (@ f `(N0) f0) f~ p))))))

(define peano_rec0 peano_rect0)

(define leb_spec1 (lambdas (x y) (iff_reflect (@ leb0 x y))))

(define ltb_spec1 (lambdas (x y) (iff_reflect (@ ltb0 x y))))

(define recursion peano_rect0)

(define sqrt_up (lambda (a)
  (match (@ compare0 `(N0) a)
     ((Eq) `(N0))
     ((Lt) (succ0 (sqrt0 (pred0 a))))
     ((Gt) `(N0)))))

(define log2_up (lambda (a)
  (match (@ compare0 `(Npos ,`(XH)) a)
     ((Eq) `(N0))
     ((Lt) (succ0 (log2 (pred0 a))))
     ((Gt) `(N0)))))

(define lcm (lambdas (a b) (@ mul0 a (@ div b (@ gcd0 a b)))))

(define eqb_spec0 (lambdas (x y) (iff_reflect (@ eqb1 x y))))

(define b2n (lambda (b)
  (match b
     ((True) `(Npos ,`(XH)))
     ((False) `(N0)))))

(define setbit (lambdas (a n) (@ lor0 a (@ shiftl0 `(Npos ,`(XH)) n))))

(define clearbit (lambdas (a n) (@ ldiff0 a (@ shiftl0 `(Npos ,`(XH)) n))))

(define ones (lambda (n) (pred0 (@ shiftl0 `(Npos ,`(XH)) n))))

(define lnot (lambdas (a n) (@ lxor0 a (ones n))))

(define max_case_strong1 (lambdas (n m compat hl hr)
  (let ((c (@ compSpec2Type n m (@ compare0 n m))))
    (match c
       ((CompEqT) (@ compat m (@ max0 n m) __ (hr __)))
       ((CompLtT) (@ compat m (@ max0 n m) __ (hr __)))
       ((CompGtT) (@ compat n (@ max0 n m) __ (hl __)))))))

(define max_case1 (lambdas (n m x x0 x1)
  (@ max_case_strong1 n m x (lambda (_) x0) (lambda (_) x1))))

(define max_dec1 (lambdas (n m)
  (@ max_case1 n m (lambdas (x y _ h0)
    (match h0
       ((Left) `(Left))
       ((Right) `(Right)))) `(Left) `(Right))))

(define min_case_strong1 (lambdas (n m compat hl hr)
  (let ((c (@ compSpec2Type n m (@ compare0 n m))))
    (match c
       ((CompEqT) (@ compat n (@ min0 n m) __ (hl __)))
       ((CompLtT) (@ compat n (@ min0 n m) __ (hl __)))
       ((CompGtT) (@ compat m (@ min0 n m) __ (hr __)))))))

(define min_case1 (lambdas (n m x x0 x1)
  (@ min_case_strong1 n m x (lambda (_) x0) (lambda (_) x1))))

(define min_dec1 (lambdas (n m)
  (@ min_case1 n m (lambdas (x y _ h0)
    (match h0
       ((Left) `(Left))
       ((Right) `(Right)))) `(Left) `(Right))))

(define max_case_strong2 (lambdas (n m x x0)
  (@ max_case_strong1 n m (lambdas (x1 y _ x2) x2) x x0)))

(define max_case2 (lambdas (n m x x0)
  (@ max_case_strong2 n m (lambda (_) x) (lambda (_) x0))))

(define max_dec2 max_dec1)

(define min_case_strong2 (lambdas (n m x x0)
  (@ min_case_strong1 n m (lambdas (x1 y _ x2) x2) x x0)))

(define min_case2 (lambdas (n m x x0)
  (@ min_case_strong2 n m (lambda (_) x) (lambda (_) x0))))

(define min_dec2 min_dec1)

(define zero0 `(Z0))

(define one0 `(Zpos ,`(XH)))

(define two0 `(Zpos ,`(XO ,`(XH))))

(define double0 (lambda (x)
  (match x
     ((Z0) `(Z0))
     ((Zpos p) `(Zpos ,`(XO ,p)))
     ((Zneg p) `(Zneg ,`(XO ,p))))))

(define succ_double0 (lambda (x)
  (match x
     ((Z0) `(Zpos ,`(XH)))
     ((Zpos p) `(Zpos ,`(XI ,p)))
     ((Zneg p) `(Zneg ,(pred_double p))))))

(define pred_double0 (lambda (x)
  (match x
     ((Z0) `(Zneg ,`(XH)))
     ((Zpos p) `(Zpos ,(pred_double p)))
     ((Zneg p) `(Zneg ,`(XI ,p))))))

(define pos_sub (lambdas (x y)
  (match x
     ((XI p)
       (match y
          ((XI q) (double0 (@ pos_sub p q)))
          ((XO q) (succ_double0 (@ pos_sub p q)))
          ((XH) `(Zpos ,`(XO ,p)))))
     ((XO p)
       (match y
          ((XI q) (pred_double0 (@ pos_sub p q)))
          ((XO q) (double0 (@ pos_sub p q)))
          ((XH) `(Zpos ,(pred_double p)))))
     ((XH)
       (match y
          ((XI q) `(Zneg ,`(XO ,q)))
          ((XO q) `(Zneg ,(pred_double q)))
          ((XH) `(Z0)))))))
  
(define add1 (lambdas (x y)
  (match x
     ((Z0) y)
     ((Zpos x~)
       (match y
          ((Z0) x)
          ((Zpos y~) `(Zpos ,(@ add x~ y~)))
          ((Zneg y~) (@ pos_sub x~ y~))))
     ((Zneg x~)
       (match y
          ((Z0) x)
          ((Zpos y~) (@ pos_sub y~ x~))
          ((Zneg y~) `(Zneg ,(@ add x~ y~))))))))

(define opp (lambda (x)
  (match x
     ((Z0) `(Z0))
     ((Zpos x0) `(Zneg ,x0))
     ((Zneg x0) `(Zpos ,x0)))))

(define succ1 (lambda (x) (@ add1 x `(Zpos ,`(XH)))))

(define pred1 (lambda (x) (@ add1 x `(Zneg ,`(XH)))))

(define sub1 (lambdas (m n) (@ add1 m (opp n))))

(define mul1 (lambdas (x y)
  (match x
     ((Z0) `(Z0))
     ((Zpos x~)
       (match y
          ((Z0) `(Z0))
          ((Zpos y~) `(Zpos ,(@ mul x~ y~)))
          ((Zneg y~) `(Zneg ,(@ mul x~ y~)))))
     ((Zneg x~)
       (match y
          ((Z0) `(Z0))
          ((Zpos y~) `(Zneg ,(@ mul x~ y~)))
          ((Zneg y~) `(Zpos ,(@ mul x~ y~))))))))

(define pow_pos (lambdas (z n) (@ iter n (mul1 z) `(Zpos ,`(XH)))))

(define pow1 (lambdas (x y)
  (match y
     ((Z0) `(Zpos ,`(XH)))
     ((Zpos p) (@ pow_pos x p))
     ((Zneg p) `(Z0)))))

(define square1 (lambda (x)
  (match x
     ((Z0) `(Z0))
     ((Zpos p) `(Zpos ,(square p)))
     ((Zneg p) `(Zpos ,(square p))))))

(define compare1 (lambdas (x y)
  (match x
     ((Z0)
       (match y
          ((Z0) `(Eq))
          ((Zpos y~) `(Lt))
          ((Zneg y~) `(Gt))))
     ((Zpos x~)
       (match y
          ((Z0) `(Gt))
          ((Zpos y~) (@ compare x~ y~))
          ((Zneg y~) `(Gt))))
     ((Zneg x~)
       (match y
          ((Z0) `(Lt))
          ((Zpos y~) `(Lt))
          ((Zneg y~) (compOpp (@ compare x~ y~))))))))

(define sgn (lambda (z)
  (match z
     ((Z0) `(Z0))
     ((Zpos p) `(Zpos ,`(XH)))
     ((Zneg p) `(Zneg ,`(XH))))))

(define leb1 (lambdas (x y)
  (match (@ compare1 x y)
     ((Eq) `(True))
     ((Lt) `(True))
     ((Gt) `(False)))))

(define ltb1 (lambdas (x y)
  (match (@ compare1 x y)
     ((Eq) `(False))
     ((Lt) `(True))
     ((Gt) `(False)))))

(define geb (lambdas (x y)
  (match (@ compare1 x y)
     ((Eq) `(True))
     ((Lt) `(False))
     ((Gt) `(True)))))

(define gtb (lambdas (x y)
  (match (@ compare1 x y)
     ((Eq) `(False))
     ((Lt) `(False))
     ((Gt) `(True)))))

(define eqb2 (lambdas (x y)
  (match x
     ((Z0)
       (match y
          ((Z0) `(True))
          ((Zpos p) `(False))
          ((Zneg p) `(False))))
     ((Zpos p)
       (match y
          ((Z0) `(False))
          ((Zpos q) (@ eqb0 p q))
          ((Zneg p0) `(False))))
     ((Zneg p)
       (match y
          ((Z0) `(False))
          ((Zpos p0) `(False))
          ((Zneg q) (@ eqb0 p q)))))))
  
(define max1 (lambdas (n m)
  (match (@ compare1 n m)
     ((Eq) n)
     ((Lt) m)
     ((Gt) n))))

(define min1 (lambdas (n m)
  (match (@ compare1 n m)
     ((Eq) n)
     ((Lt) n)
     ((Gt) m))))

(define abs (lambda (z)
  (match z
     ((Z0) `(Z0))
     ((Zpos p) `(Zpos ,p))
     ((Zneg p) `(Zpos ,p)))))

(define abs_nat (lambda (z)
  (match z
     ((Z0) `(O))
     ((Zpos p) (to_nat p))
     ((Zneg p) (to_nat p)))))

(define abs_N (lambda (z)
  (match z
     ((Z0) `(N0))
     ((Zpos p) `(Npos ,p))
     ((Zneg p) `(Npos ,p)))))

(define to_nat1 (lambda (z)
  (match z
     ((Z0) `(O))
     ((Zpos p) (to_nat p))
     ((Zneg p) `(O)))))

(define to_N (lambda (z)
  (match z
     ((Z0) `(N0))
     ((Zpos p) `(Npos ,p))
     ((Zneg p) `(N0)))))

(define of_nat1 (lambda (n)
  (match n
     ((O) `(Z0))
     ((S n0) `(Zpos ,(of_succ_nat n0))))))

(define of_N (lambda (n)
  (match n
     ((N0) `(Z0))
     ((Npos p) `(Zpos ,p)))))

(define to_pos (lambda (z)
  (match z
     ((Z0) `(XH))
     ((Zpos p) p)
     ((Zneg p) `(XH)))))

(define iter1 (lambdas (n f x)
  (match n
     ((Z0) x)
     ((Zpos p) (@ iter p f x))
     ((Zneg p) x))))

(define pos_div_eucl0 (lambdas (a b)
  (match a
     ((XI a~)
       (match (@ pos_div_eucl0 a~ b)
          ((Pair q r)
            (let ((r~
              (@ add1 (@ mul1 `(Zpos ,`(XO ,`(XH))) r) `(Zpos ,`(XH)))))
              (match (@ ltb1 r~ b)
                 ((True) `(Pair ,(@ mul1 `(Zpos ,`(XO ,`(XH))) q) ,r~))
                 ((False) `(Pair
                   ,(@ add1 (@ mul1 `(Zpos ,`(XO ,`(XH))) q) `(Zpos ,`(XH)))
                   ,(@ sub1 r~ b))))))))
     ((XO a~)
       (match (@ pos_div_eucl0 a~ b)
          ((Pair q r)
            (let ((r~ (@ mul1 `(Zpos ,`(XO ,`(XH))) r)))
              (match (@ ltb1 r~ b)
                 ((True) `(Pair ,(@ mul1 `(Zpos ,`(XO ,`(XH))) q) ,r~))
                 ((False) `(Pair
                   ,(@ add1 (@ mul1 `(Zpos ,`(XO ,`(XH))) q) `(Zpos ,`(XH)))
                   ,(@ sub1 r~ b))))))))
     ((XH)
       (match (@ leb1 `(Zpos ,`(XO ,`(XH))) b)
          ((True) `(Pair ,`(Z0) ,`(Zpos ,`(XH))))
          ((False) `(Pair ,`(Zpos ,`(XH)) ,`(Z0))))))))
  
(define div_eucl0 (lambdas (a b)
  (match a
     ((Z0) `(Pair ,`(Z0) ,`(Z0)))
     ((Zpos a~)
       (match b
          ((Z0) `(Pair ,`(Z0) ,`(Z0)))
          ((Zpos p) (@ pos_div_eucl0 a~ b))
          ((Zneg b~)
            (match (@ pos_div_eucl0 a~ `(Zpos ,b~))
               ((Pair q r)
                 (match r
                    ((Z0) `(Pair ,(opp q) ,`(Z0)))
                    ((Zpos p) `(Pair ,(opp (@ add1 q `(Zpos ,`(XH))))
                      ,(@ add1 b r)))
                    ((Zneg p) `(Pair ,(opp (@ add1 q `(Zpos ,`(XH))))
                      ,(@ add1 b r)))))))))
     ((Zneg a~)
       (match b
          ((Z0) `(Pair ,`(Z0) ,`(Z0)))
          ((Zpos p)
            (match (@ pos_div_eucl0 a~ b)
               ((Pair q r)
                 (match r
                    ((Z0) `(Pair ,(opp q) ,`(Z0)))
                    ((Zpos p0) `(Pair ,(opp (@ add1 q `(Zpos ,`(XH))))
                      ,(@ sub1 b r)))
                    ((Zneg p0) `(Pair ,(opp (@ add1 q `(Zpos ,`(XH))))
                      ,(@ sub1 b r)))))))
          ((Zneg b~)
            (match (@ pos_div_eucl0 a~ `(Zpos ,b~))
               ((Pair q r) `(Pair ,q ,(opp r))))))))))

(define div1 (lambdas (a b)
  (match (@ div_eucl0 a b)
     ((Pair q x) q))))

(define modulo0 (lambdas (a b)
  (match (@ div_eucl0 a b)
     ((Pair x r) r))))

(define quotrem (lambdas (a b)
  (match a
     ((Z0) `(Pair ,`(Z0) ,`(Z0)))
     ((Zpos a0)
       (match b
          ((Z0) `(Pair ,`(Z0) ,a))
          ((Zpos b0)
            (match (@ pos_div_eucl a0 `(Npos ,b0))
               ((Pair q r) `(Pair ,(of_N q) ,(of_N r)))))
          ((Zneg b0)
            (match (@ pos_div_eucl a0 `(Npos ,b0))
               ((Pair q r) `(Pair ,(opp (of_N q)) ,(of_N r)))))))
     ((Zneg a0)
       (match b
          ((Z0) `(Pair ,`(Z0) ,a))
          ((Zpos b0)
            (match (@ pos_div_eucl a0 `(Npos ,b0))
               ((Pair q r) `(Pair ,(opp (of_N q)) ,(opp (of_N r))))))
          ((Zneg b0)
            (match (@ pos_div_eucl a0 `(Npos ,b0))
               ((Pair q r) `(Pair ,(of_N q) ,(opp (of_N r)))))))))))

(define quot (lambdas (a b) (fst (@ quotrem a b))))

(define rem (lambdas (a b) (snd (@ quotrem a b))))

(define even0 (lambda (z)
  (match z
     ((Z0) `(True))
     ((Zpos p)
       (match p
          ((XI p0) `(False))
          ((XO p0) `(True))
          ((XH) `(False))))
     ((Zneg p)
       (match p
          ((XI p0) `(False))
          ((XO p0) `(True))
          ((XH) `(False)))))))

(define odd0 (lambda (z)
  (match z
     ((Z0) `(False))
     ((Zpos p)
       (match p
          ((XI p0) `(True))
          ((XO p0) `(False))
          ((XH) `(True))))
     ((Zneg p)
       (match p
          ((XI p0) `(True))
          ((XO p0) `(False))
          ((XH) `(True)))))))

(define div3 (lambda (z)
  (match z
     ((Z0) `(Z0))
     ((Zpos p)
       (match p
          ((XI p0) `(Zpos ,(div2 p)))
          ((XO p0) `(Zpos ,(div2 p)))
          ((XH) `(Z0))))
     ((Zneg p) `(Zneg ,(div2_up p))))))

(define quot2 (lambda (z)
  (match z
     ((Z0) `(Z0))
     ((Zpos p)
       (match p
          ((XI p0) `(Zpos ,(div2 p)))
          ((XO p0) `(Zpos ,(div2 p)))
          ((XH) `(Z0))))
     ((Zneg p)
       (match p
          ((XI p0) `(Zneg ,(div2 p)))
          ((XO p0) `(Zneg ,(div2 p)))
          ((XH) `(Z0)))))))

(define log0 (lambda (z)
  (match z
     ((Z0) `(Z0))
     ((Zpos p0)
       (match p0
          ((XI p) `(Zpos ,(size p)))
          ((XO p) `(Zpos ,(size p)))
          ((XH) `(Z0))))
     ((Zneg p) `(Z0)))))

(define sqrtrem1 (lambda (n)
  (match n
     ((Z0) `(Pair ,`(Z0) ,`(Z0)))
     ((Zpos p)
       (match (sqrtrem p)
          ((Pair s m)
            (match m
               ((IsNul) `(Pair ,`(Zpos ,s) ,`(Z0)))
               ((IsPos r) `(Pair ,`(Zpos ,s) ,`(Zpos ,r)))
               ((IsNeg) `(Pair ,`(Zpos ,s) ,`(Z0)))))))
     ((Zneg p) `(Pair ,`(Z0) ,`(Z0))))))

(define sqrt1 (lambda (n)
  (match n
     ((Z0) `(Z0))
     ((Zpos p) `(Zpos ,(sqrt p)))
     ((Zneg p) `(Z0)))))

(define gcd1 (lambdas (a b)
  (match a
     ((Z0) (abs b))
     ((Zpos a0)
       (match b
          ((Z0) (abs a))
          ((Zpos b0) `(Zpos ,(@ gcd a0 b0)))
          ((Zneg b0) `(Zpos ,(@ gcd a0 b0)))))
     ((Zneg a0)
       (match b
          ((Z0) (abs a))
          ((Zpos b0) `(Zpos ,(@ gcd a0 b0)))
          ((Zneg b0) `(Zpos ,(@ gcd a0 b0))))))))

(define ggcd1 (lambdas (a b)
  (match a
     ((Z0) `(Pair ,(abs b) ,`(Pair ,`(Z0) ,(sgn b))))
     ((Zpos a0)
       (match b
          ((Z0) `(Pair ,(abs a) ,`(Pair ,(sgn a) ,`(Z0))))
          ((Zpos b0)
            (match (@ ggcd a0 b0)
               ((Pair g p)
                 (match p
                    ((Pair aa bb) `(Pair ,`(Zpos ,g) ,`(Pair ,`(Zpos ,aa)
                      ,`(Zpos ,bb))))))))
          ((Zneg b0)
            (match (@ ggcd a0 b0)
               ((Pair g p)
                 (match p
                    ((Pair aa bb) `(Pair ,`(Zpos ,g) ,`(Pair ,`(Zpos ,aa)
                      ,`(Zneg ,bb))))))))))
     ((Zneg a0)
       (match b
          ((Z0) `(Pair ,(abs a) ,`(Pair ,(sgn a) ,`(Z0))))
          ((Zpos b0)
            (match (@ ggcd a0 b0)
               ((Pair g p)
                 (match p
                    ((Pair aa bb) `(Pair ,`(Zpos ,g) ,`(Pair ,`(Zneg ,aa)
                      ,`(Zpos ,bb))))))))
          ((Zneg b0)
            (match (@ ggcd a0 b0)
               ((Pair g p)
                 (match p
                    ((Pair aa bb) `(Pair ,`(Zpos ,g) ,`(Pair ,`(Zneg ,aa)
                      ,`(Zneg ,bb)))))))))))))

(define testbit1 (lambdas (a n)
  (match n
     ((Z0) (odd0 a))
     ((Zpos p)
       (match a
          ((Z0) `(False))
          ((Zpos a0) (@ testbit a0 `(Npos ,p)))
          ((Zneg a0) (negb (@ testbit0 (pred_N a0) `(Npos ,p))))))
     ((Zneg p) `(False)))))

(define shiftl1 (lambdas (a n)
  (match n
     ((Z0) a)
     ((Zpos p) (@ iter p (mul1 `(Zpos ,`(XO ,`(XH)))) a))
     ((Zneg p) (@ iter p div3 a)))))

(define shiftr1 (lambdas (a n) (@ shiftl1 a (opp n))))

(define lor1 (lambdas (a b)
  (match a
     ((Z0) b)
     ((Zpos a0)
       (match b
          ((Z0) a)
          ((Zpos b0) `(Zpos ,(@ lor a0 b0)))
          ((Zneg b0) `(Zneg ,(succ_pos (@ ldiff0 (pred_N b0) `(Npos ,a0)))))))
     ((Zneg a0)
       (match b
          ((Z0) a)
          ((Zpos b0) `(Zneg ,(succ_pos (@ ldiff0 (pred_N a0) `(Npos ,b0)))))
          ((Zneg b0) `(Zneg ,(succ_pos (@ land0 (pred_N a0) (pred_N b0))))))))))

(define land1 (lambdas (a b)
  (match a
     ((Z0) `(Z0))
     ((Zpos a0)
       (match b
          ((Z0) `(Z0))
          ((Zpos b0) (of_N (@ land a0 b0)))
          ((Zneg b0) (of_N (@ ldiff0 `(Npos ,a0) (pred_N b0))))))
     ((Zneg a0)
       (match b
          ((Z0) `(Z0))
          ((Zpos b0) (of_N (@ ldiff0 `(Npos ,b0) (pred_N a0))))
          ((Zneg b0) `(Zneg ,(succ_pos (@ lor0 (pred_N a0) (pred_N b0))))))))))

(define ldiff1 (lambdas (a b)
  (match a
     ((Z0) `(Z0))
     ((Zpos a0)
       (match b
          ((Z0) a)
          ((Zpos b0) (of_N (@ ldiff a0 b0)))
          ((Zneg b0) (of_N (@ land0 `(Npos ,a0) (pred_N b0))))))
     ((Zneg a0)
       (match b
          ((Z0) a)
          ((Zpos b0) `(Zneg ,(succ_pos (@ lor0 (pred_N a0) `(Npos ,b0)))))
          ((Zneg b0) (of_N (@ ldiff0 (pred_N b0) (pred_N a0)))))))))

(define lxor1 (lambdas (a b)
  (match a
     ((Z0) b)
     ((Zpos a0)
       (match b
          ((Z0) a)
          ((Zpos b0) (of_N (@ lxor a0 b0)))
          ((Zneg b0) `(Zneg ,(succ_pos (@ lxor0 `(Npos ,a0) (pred_N b0)))))))
     ((Zneg a0)
       (match b
          ((Z0) a)
          ((Zpos b0) `(Zneg ,(succ_pos (@ lxor0 (pred_N a0) `(Npos ,b0)))))
          ((Zneg b0) (of_N (@ lxor0 (pred_N a0) (pred_N b0)))))))))

(define eq_dec1 (lambdas (x y)
  (match x
     ((Z0)
       (match y
          ((Z0) `(Left))
          ((Zpos p) `(Right))
          ((Zneg p) `(Right))))
     ((Zpos x0)
       (match y
          ((Z0) `(Right))
          ((Zpos p0)
            (match (@ eq_dec x0 p0)
               ((Left) `(Left))
               ((Right) `(Right))))
          ((Zneg p0) `(Right))))
     ((Zneg x0)
       (match y
          ((Z0) `(Right))
          ((Zpos p0) `(Right))
          ((Zneg p0)
            (match (@ eq_dec x0 p0)
               ((Left) `(Left))
               ((Right) `(Right)))))))))

(define leb_spec2 (lambdas (x y) (iff_reflect (@ leb1 x y))))

(define ltb_spec2 (lambdas (x y) (iff_reflect (@ ltb1 x y))))

(define sqrt_up0 (lambda (a)
  (match (@ compare1 `(Z0) a)
     ((Eq) `(Z0))
     ((Lt) (succ1 (sqrt1 (pred1 a))))
     ((Gt) `(Z0)))))

(define log2_up0 (lambda (a)
  (match (@ compare1 `(Zpos ,`(XH)) a)
     ((Eq) `(Z0))
     ((Lt) (succ1 (log0 (pred1 a))))
     ((Gt) `(Z0)))))

(define div4 quot)

(define modulo1 rem)

(define lcm0 (lambdas (a b) (abs (@ mul1 a (@ div1 b (@ gcd1 a b))))))

(define eqb_spec1 (lambdas (x y) (iff_reflect (@ eqb2 x y))))

(define b2z (lambda (b)
  (match b
     ((True) `(Zpos ,`(XH)))
     ((False) `(Z0)))))

(define setbit0 (lambdas (a n) (@ lor1 a (@ shiftl1 `(Zpos ,`(XH)) n))))

(define clearbit0 (lambdas (a n) (@ ldiff1 a (@ shiftl1 `(Zpos ,`(XH)) n))))

(define lnot0 (lambda (a) (pred1 (opp a))))

(define ones0 (lambda (n) (pred1 (@ shiftl1 `(Zpos ,`(XH)) n))))

(define max_case_strong3 (lambdas (n m compat hl hr)
  (let ((c (@ compSpec2Type n m (@ compare1 n m))))
    (match c
       ((CompEqT) (@ compat m (@ max1 n m) __ (hr __)))
       ((CompLtT) (@ compat m (@ max1 n m) __ (hr __)))
       ((CompGtT) (@ compat n (@ max1 n m) __ (hl __)))))))

(define max_case3 (lambdas (n m x x0 x1)
  (@ max_case_strong3 n m x (lambda (_) x0) (lambda (_) x1))))

(define max_dec3 (lambdas (n m)
  (@ max_case3 n m (lambdas (x y _ h0)
    (match h0
       ((Left) `(Left))
       ((Right) `(Right)))) `(Left) `(Right))))

(define min_case_strong3 (lambdas (n m compat hl hr)
  (let ((c (@ compSpec2Type n m (@ compare1 n m))))
    (match c
       ((CompEqT) (@ compat n (@ min1 n m) __ (hl __)))
       ((CompLtT) (@ compat n (@ min1 n m) __ (hl __)))
       ((CompGtT) (@ compat m (@ min1 n m) __ (hr __)))))))

(define min_case3 (lambdas (n m x x0 x1)
  (@ min_case_strong3 n m x (lambda (_) x0) (lambda (_) x1))))

(define min_dec3 (lambdas (n m)
  (@ min_case3 n m (lambdas (x y _ h0)
    (match h0
       ((Left) `(Left))
       ((Right) `(Right)))) `(Left) `(Right))))

(define max_case_strong4 (lambdas (n m x x0)
  (@ max_case_strong3 n m (lambdas (x1 y _ x2) x2) x x0)))

(define max_case4 (lambdas (n m x x0)
  (@ max_case_strong4 n m (lambda (_) x) (lambda (_) x0))))

(define max_dec4 max_dec3)

(define min_case_strong4 (lambdas (n m x x0)
  (@ min_case_strong3 n m (lambdas (x1 y _ x2) x2) x x0)))

(define min_case4 (lambdas (n m x x0)
  (@ min_case_strong4 n m (lambda (_) x) (lambda (_) x0))))

(define min_dec4 min_dec3)

(define z_lt_dec (lambdas (x y)
  (match (@ compare1 x y)
     ((Eq) `(Right))
     ((Lt) `(Left))
     ((Gt) `(Right)))))

(define z_le_dec (lambdas (x y)
  (match (@ compare1 x y)
     ((Eq) `(Left))
     ((Lt) `(Left))
     ((Gt) `(Right)))))

(define z_lt_ge_dec (lambdas (x y) (@ z_lt_dec x y)))

(define z_le_gt_dec (lambdas (x y)
  (match (@ z_le_dec x y)
     ((Left) `(Left))
     ((Right) `(Right)))))

(define zeq_bool (lambdas (x y)
  (match (@ compare1 x y)
     ((Eq) `(True))
     ((Lt) `(False))
     ((Gt) `(False)))))

(define shift_nat (lambdas (n z) (@ nat_iter n (lambda (x) `(XO ,x)) z)))

(define shift_pos (lambdas (n z) (@ iter n (lambda (x) `(XO ,x)) z)))

(define two_power_nat (lambda (n) `(Zpos ,(@ shift_nat n `(XH)))))

(define two_power_pos (lambda (x) `(Zpos ,(@ shift_pos x `(XH)))))

(define two_p (lambda (x)
  (match x
     ((Z0) `(Zpos ,`(XH)))
     ((Zpos y) (two_power_pos y))
     ((Zneg y) `(Z0)))))

(define peq (lambdas (x y)
  (match (@ compare_cont x y `(Eq))
     ((Eq) `(Left))
     ((Lt) `(Right))
     ((Gt) `(Right)))))

(define zeq eq_dec1)

(define zlt z_lt_ge_dec)

(define zle z_le_gt_dec)

(define option_map (lambdas (f x)
  (match x
     ((Some y) `(Some ,(f y)))
     ((None) `(None)))))

(define proj_sumbool (lambda (a)
  (match a
     ((Left) `(True))
     ((Right) `(False)))))

(define ascii_dec (lambdas (a b)
  (match a
     ((Ascii x x0 x1 x2 x3 x4 x5 x6)
       (match b
          ((Ascii b8 b9 b10 b11 b12 b13 b14 b15)
            (match (@ bool_dec x b8)
               ((Left)
                 (match (@ bool_dec x0 b9)
                    ((Left)
                      (match (@ bool_dec x1 b10)
                         ((Left)
                           (match (@ bool_dec x2 b11)
                              ((Left)
                                (match (@ bool_dec x3 b12)
                                   ((Left)
                                     (match (@ bool_dec x4 b13)
                                        ((Left)
                                          (match (@ bool_dec x5 b14)
                                             ((Left)
                                               (match (@ bool_dec x6 b15)
                                                  ((Left) `(Left))
                                                  ((Right) `(Right))))
                                             ((Right) `(Right))))
                                        ((Right) `(Right))))
                                   ((Right) `(Right))))
                              ((Right) `(Right))))
                         ((Right) `(Right))))
                    ((Right) `(Right))))
               ((Right) `(Right)))))))))

(define wordsize (lambda (wordsize_minus_one) `(S ,wordsize_minus_one)))

(define modulus (lambda (wordsize_minus_one)
  (two_power_nat (wordsize wordsize_minus_one))))

(define half_modulus (lambda (wordsize_minus_one)
  (@ div1 (modulus wordsize_minus_one) `(Zpos ,`(XO ,`(XH))))))

(define comparison_rect (lambdas (f f0 f1 f2 f3 f4 c)
  (match c
     ((Ceq) f)
     ((Cne) f0)
     ((Clt) f1)
     ((Cle) f2)
     ((Cgt) f3)
     ((Cge) f4))))

(define comparison_rec (lambdas (f f0 f1 f2 f3 f4 c)
  (match c
     ((Ceq) f)
     ((Cne) f0)
     ((Clt) f1)
     ((Cle) f2)
     ((Cgt) f3)
     ((Cge) f4))))

(define negate_comparison (lambda (c)
  (match c
     ((Ceq) `(Cne))
     ((Cne) `(Ceq))
     ((Clt) `(Cge))
     ((Cle) `(Cgt))
     ((Cgt) `(Cle))
     ((Cge) `(Clt)))))

(define swap_comparison (lambda (c)
  (match c
     ((Ceq) `(Ceq))
     ((Cne) `(Cne))
     ((Clt) `(Cgt))
     ((Cle) `(Cge))
     ((Cgt) `(Clt))
     ((Cge) `(Cle)))))

(define int_rect (lambdas (wordsize_minus_one f i) (@ f i __)))

(define int_rec (lambdas (wordsize_minus_one f i) (@ f i __)))

(define intval (lambdas (wordsize_minus_one i) i))

(define max_unsigned (lambda (wordsize_minus_one)
  (@ sub1 (modulus wordsize_minus_one) `(Zpos ,`(XH)))))

(define max_signed (lambda (wordsize_minus_one)
  (@ sub1 (half_modulus wordsize_minus_one) `(Zpos ,`(XH)))))

(define min_signed (lambda (wordsize_minus_one)
  (opp (half_modulus wordsize_minus_one))))

(define unsigned (lambdas (wordsize_minus_one n)
  (@ intval wordsize_minus_one n)))

(define signed (lambdas (wordsize_minus_one n)
  (match (@ zlt (@ unsigned wordsize_minus_one n)
           (half_modulus wordsize_minus_one))
     ((Left) (@ unsigned wordsize_minus_one n))
     ((Right)
       (@ sub1 (@ unsigned wordsize_minus_one n)
         (modulus wordsize_minus_one))))))

(define repr (lambdas (wordsize_minus_one x)
  (@ modulo0 x (modulus wordsize_minus_one))))

(define zero1 (lambda (wordsize_minus_one)
  (@ repr wordsize_minus_one `(Z0))))

(define one1 (lambda (wordsize_minus_one)
  (@ repr wordsize_minus_one `(Zpos ,`(XH)))))

(define mone (lambda (wordsize_minus_one)
  (@ repr wordsize_minus_one `(Zneg ,`(XH)))))

(define eq_dec2 (lambdas (wordsize_minus_one x y)
  (match (@ zeq x y)
     ((Left) `(Left))
     ((Right) `(Right)))))

(define eq (lambdas (wordsize_minus_one x y)
  (match (@ zeq (@ unsigned wordsize_minus_one x)
           (@ unsigned wordsize_minus_one y))
     ((Left) `(True))
     ((Right) `(False)))))

(define lt (lambdas (wordsize_minus_one x y)
  (match (@ zlt (@ signed wordsize_minus_one x)
           (@ signed wordsize_minus_one y))
     ((Left) `(True))
     ((Right) `(False)))))

(define ltu (lambdas (wordsize_minus_one x y)
  (match (@ zlt (@ unsigned wordsize_minus_one x)
           (@ unsigned wordsize_minus_one y))
     ((Left) `(True))
     ((Right) `(False)))))

(define lequ (lambdas (wordsize_minus_one x y)
  (match (@ ltu wordsize_minus_one x y)
     ((True) `(True))
     ((False) (@ eq wordsize_minus_one x y)))))

(define neg (lambdas (wordsize_minus_one x)
  (@ repr wordsize_minus_one (opp (@ unsigned wordsize_minus_one x)))))

(define zero_ext (lambdas (wordsize_minus_one n x)
  (@ repr wordsize_minus_one
    (@ modulo0 (@ unsigned wordsize_minus_one x) (two_p n)))))

(define sign_ext (lambdas (wordsize_minus_one n x)
  (@ repr wordsize_minus_one
    (let ((p (two_p n)))
      (let ((y (@ modulo0 (@ unsigned wordsize_minus_one x) p)))
        (match (@ zlt y (two_p (@ sub1 n `(Zpos ,`(XH)))))
           ((Left) y)
           ((Right) (@ sub1 y p))))))))

(define add2 (lambdas (wordsize_minus_one x y)
  (@ repr wordsize_minus_one
    (@ add1 (@ unsigned wordsize_minus_one x)
      (@ unsigned wordsize_minus_one y)))))

(define sub2 (lambdas (wordsize_minus_one x y)
  (@ repr wordsize_minus_one
    (@ sub1 (@ unsigned wordsize_minus_one x)
      (@ unsigned wordsize_minus_one y)))))

(define mul2 (lambdas (wordsize_minus_one x y)
  (@ repr wordsize_minus_one
    (@ mul1 (@ unsigned wordsize_minus_one x)
      (@ unsigned wordsize_minus_one y)))))

(define zdiv_round (lambdas (x y)
  (match (@ zlt x `(Z0))
     ((Left)
       (match (@ zlt y `(Z0))
          ((Left) (@ div1 (opp x) (opp y)))
          ((Right) (opp (@ div1 (opp x) y)))))
     ((Right)
       (match (@ zlt y `(Z0))
          ((Left) (opp (@ div1 x (opp y))))
          ((Right) (@ div1 x y)))))))

(define zmod_round (lambdas (x y) (@ sub1 x (@ mul1 (@ zdiv_round x y) y))))

(define divs (lambdas (wordsize_minus_one x y)
  (@ repr wordsize_minus_one
    (@ zdiv_round (@ signed wordsize_minus_one x)
      (@ signed wordsize_minus_one y)))))

(define mods (lambdas (wordsize_minus_one x y)
  (@ repr wordsize_minus_one
    (@ zmod_round (@ signed wordsize_minus_one x)
      (@ signed wordsize_minus_one y)))))

(define divu (lambdas (wordsize_minus_one x y)
  (@ repr wordsize_minus_one
    (@ div1 (@ unsigned wordsize_minus_one x)
      (@ unsigned wordsize_minus_one y)))))

(define modu (lambdas (wordsize_minus_one x y)
  (@ repr wordsize_minus_one
    (@ modulo0 (@ unsigned wordsize_minus_one x)
      (@ unsigned wordsize_minus_one y)))))

(define bool_to_int (lambdas (wordsize_minus_one b)
  (match b
     ((True) (one1 wordsize_minus_one))
     ((False) (zero1 wordsize_minus_one)))))

(define unsigned_overflow (lambdas (wordsize_minus_one o1 o2)
  (let ((res (@ add1 o1 o2)))
    (match (@ zlt res (modulus wordsize_minus_one))
       ((Left) `(False))
       ((Right) `(True))))))

(define unsigned_overflow_with_carry (lambdas (wordsize_minus_one o1 o2
  carry)
  (let ((c (@ bool_to_int wordsize_minus_one carry)))
    (let ((res (@ add1 (@ add1 o1 o2) (@ unsigned wordsize_minus_one c))))
      (match (@ zle res (max_unsigned wordsize_minus_one))
         ((Left) `(False))
         ((Right) `(True)))))))

(define signed_overflow (lambdas (wordsize_minus_one o1 o2)
  (let ((res (@ add1 o1 o2)))
    (match (match (proj_sumbool (@ zle res (max_signed wordsize_minus_one)))
              ((True)
                (proj_sumbool (@ zle (min_signed wordsize_minus_one) res)))
              ((False) `(False)))
       ((True) `(False))
       ((False) `(True))))))

(define signed_overflow_with_carry (lambdas (wordsize_minus_one o1 o2 carry)
  (let ((c (@ bool_to_int wordsize_minus_one carry)))
    (let ((res (@ add1 (@ add1 o1 o2) (@ signed wordsize_minus_one c))))
      (match (match (proj_sumbool
                      (@ zle res (max_signed wordsize_minus_one)))
                ((True)
                  (proj_sumbool (@ zle (min_signed wordsize_minus_one) res)))
                ((False) `(False)))
         ((True) `(False))
         ((False) `(True)))))))

(define signed_overflow_with_borrow (lambdas (wordsize_minus_one o1 o2
  borrow)
  (let ((b (@ bool_to_int wordsize_minus_one borrow)))
    (let ((res (@ sub1 (@ add1 o1 o2) (@ signed wordsize_minus_one b))))
      (match (match (proj_sumbool
                      (@ zle res (max_signed wordsize_minus_one)))
                ((True)
                  (proj_sumbool (@ zle (min_signed wordsize_minus_one) res)))
                ((False) `(False)))
         ((True) `(False))
         ((False) `(True)))))))

(define is_zero (lambdas (wordsize_minus_one i)
  (@ eq wordsize_minus_one i (zero1 wordsize_minus_one))))

(define is_signed (lambdas (wordsize_minus_one i)
  (@ lt wordsize_minus_one i (zero1 wordsize_minus_one))))

(define z_shift_add (lambdas (b x)
  (match b
     ((True) (@ add1 (@ mul1 `(Zpos ,`(XO ,`(XH))) x) `(Zpos ,`(XH))))
     ((False) (@ mul1 `(Zpos ,`(XO ,`(XH))) x)))))

(define z_bin_decomp (lambda (x)
  (match x
     ((Z0) `(Pair ,`(False) ,`(Z0)))
     ((Zpos p)
       (match p
          ((XI q) `(Pair ,`(True) ,`(Zpos ,q)))
          ((XO q) `(Pair ,`(False) ,`(Zpos ,q)))
          ((XH) `(Pair ,`(True) ,`(Z0)))))
     ((Zneg p)
       (match p
          ((XI q) `(Pair ,`(True) ,(@ sub1 `(Zneg ,q) `(Zpos ,`(XH)))))
          ((XO q) `(Pair ,`(False) ,`(Zneg ,q)))
          ((XH) `(Pair ,`(True) ,`(Zneg ,`(XH)))))))))

(define bits_of_Z (lambdas (n x)
  (match n
     ((O) (lambda (i) `(False)))
     ((S m)
       (match (z_bin_decomp x)
          ((Pair b y)
            (let ((f (@ bits_of_Z m y)))
              (lambda (i)
              (match (@ zeq i `(Z0))
                 ((Left) b)
                 ((Right) (f (@ sub1 i `(Zpos ,`(XH))))))))))))))
  
(define z_of_bits (lambdas (n f)
  (match n
     ((O) `(Z0))
     ((S m)
       (@ z_shift_add (f `(Z0))
         (@ z_of_bits m (lambda (i) (f (@ add1 i `(Zpos ,`(XH)))))))))))
  
(define bitwise_binop (lambdas (wordsize_minus_one f x y)
  (let ((fx
    (@ bits_of_Z (wordsize wordsize_minus_one)
      (@ unsigned wordsize_minus_one x))))
    (let ((fy
      (@ bits_of_Z (wordsize wordsize_minus_one)
        (@ unsigned wordsize_minus_one y))))
      (@ repr wordsize_minus_one
        (@ z_of_bits (wordsize wordsize_minus_one) (lambda (i)
          (@ f (fx i) (fy i)))))))))

(define and (lambdas (wordsize_minus_one x y)
  (@ bitwise_binop wordsize_minus_one (lambdas (b1 b2)
    (match b1
       ((True) b2)
       ((False) `(False)))) x y)))

(define or (lambdas (wordsize_minus_one x y)
  (@ bitwise_binop wordsize_minus_one (lambdas (b1 b2)
    (match b1
       ((True) `(True))
       ((False) b2))) x y)))

(define xor (lambdas (wordsize_minus_one x y)
  (@ bitwise_binop wordsize_minus_one xorb x y)))

(define not (lambdas (wordsize_minus_one x)
  (@ xor wordsize_minus_one x (mone wordsize_minus_one))))

(define shl (lambdas (wordsize_minus_one x y)
  (let ((fx
    (@ bits_of_Z (wordsize wordsize_minus_one)
      (@ unsigned wordsize_minus_one x))))
    (let ((vy (@ unsigned wordsize_minus_one y)))
      (@ repr wordsize_minus_one
        (@ z_of_bits (wordsize wordsize_minus_one) (lambda (i)
          (fx (@ sub1 i vy)))))))))

(define shru (lambdas (wordsize_minus_one x y)
  (let ((fx
    (@ bits_of_Z (wordsize wordsize_minus_one)
      (@ unsigned wordsize_minus_one x))))
    (let ((vy (@ unsigned wordsize_minus_one y)))
      (@ repr wordsize_minus_one
        (@ z_of_bits (wordsize wordsize_minus_one) (lambda (i)
          (fx (@ add1 i vy)))))))))

(define shr (lambdas (wordsize_minus_one x y)
  (@ repr wordsize_minus_one
    (@ div1 (@ signed wordsize_minus_one x)
      (two_p (@ unsigned wordsize_minus_one y))))))

(define shrx (lambdas (wordsize_minus_one x y)
  (@ divs wordsize_minus_one x
    (@ shl wordsize_minus_one (one1 wordsize_minus_one) y))))

(define shr_carry (lambdas (wordsize_minus_one x y)
  (@ sub2 wordsize_minus_one (@ shrx wordsize_minus_one x y)
    (@ shr wordsize_minus_one x y))))

(define rol (lambdas (wordsize_minus_one x y)
  (let ((fx
    (@ bits_of_Z (wordsize wordsize_minus_one)
      (@ unsigned wordsize_minus_one x))))
    (let ((vy (@ unsigned wordsize_minus_one y)))
      (@ repr wordsize_minus_one
        (@ z_of_bits (wordsize wordsize_minus_one) (lambda (i)
          (fx
            (@ modulo0 (@ sub1 i vy) (of_nat1 (wordsize wordsize_minus_one)))))))))))

(define ror (lambdas (wordsize_minus_one x y)
  (let ((fx
    (@ bits_of_Z (wordsize wordsize_minus_one)
      (@ unsigned wordsize_minus_one x))))
    (let ((vy (@ unsigned wordsize_minus_one y)))
      (@ repr wordsize_minus_one
        (@ z_of_bits (wordsize wordsize_minus_one) (lambda (i)
          (fx
            (@ modulo0 (@ add1 i vy) (of_nat1 (wordsize wordsize_minus_one)))))))))))

(define rolm (lambdas (wordsize_minus_one x a m)
  (@ and wordsize_minus_one (@ rol wordsize_minus_one x a) m)))

(define z_one_bits (lambdas (n x i)
  (match n
     ((O) `(Nil))
     ((S m)
       (match (z_bin_decomp x)
          ((Pair b y)
            (match b
               ((True) `(Cons ,i
                 ,(@ z_one_bits m y (@ add1 i `(Zpos ,`(XH))))))
               ((False) (@ z_one_bits m y (@ add1 i `(Zpos ,`(XH))))))))))))
  
(define one_bits (lambdas (wordsize_minus_one x)
  (@ map (repr wordsize_minus_one)
    (@ z_one_bits (wordsize wordsize_minus_one)
      (@ unsigned wordsize_minus_one x) `(Z0)))))

(define is_power2 (lambdas (wordsize_minus_one x)
  (match (@ z_one_bits (wordsize wordsize_minus_one)
           (@ unsigned wordsize_minus_one x) `(Z0))
     ((Nil) `(None))
     ((Cons i l)
       (match l
          ((Nil) `(Some ,(@ repr wordsize_minus_one i)))
          ((Cons z l0) `(None)))))))

(define rlw_state_rect (lambdas (f f0 f1 f2 f3 f4 f5 f6 r)
  (match r
     ((RLW_S0) f)
     ((RLW_S1) f0)
     ((RLW_S2) f1)
     ((RLW_S3) f2)
     ((RLW_S4) f3)
     ((RLW_S5) f4)
     ((RLW_S6) f5)
     ((RLW_Sbad) f6))))

(define rlw_state_rec (lambdas (f f0 f1 f2 f3 f4 f5 f6 r)
  (match r
     ((RLW_S0) f)
     ((RLW_S1) f0)
     ((RLW_S2) f1)
     ((RLW_S3) f2)
     ((RLW_S4) f3)
     ((RLW_S5) f4)
     ((RLW_S6) f5)
     ((RLW_Sbad) f6))))

(define rlw_transition (lambdas (s b)
  (match s
     ((RLW_S0)
       (match b
          ((True) `(RLW_S4))
          ((False) `(RLW_S1))))
     ((RLW_S1)
       (match b
          ((True) `(RLW_S2))
          ((False) `(RLW_S1))))
     ((RLW_S2)
       (match b
          ((True) `(RLW_S2))
          ((False) `(RLW_S3))))
     ((RLW_S3)
       (match b
          ((True) `(RLW_Sbad))
          ((False) `(RLW_S3))))
     ((RLW_S4)
       (match b
          ((True) `(RLW_S4))
          ((False) `(RLW_S5))))
     ((RLW_S5)
       (match b
          ((True) `(RLW_S6))
          ((False) `(RLW_S5))))
     ((RLW_S6)
       (match b
          ((True) `(RLW_S6))
          ((False) `(RLW_Sbad))))
     ((RLW_Sbad) `(RLW_Sbad)))))

(define rlw_accepting (lambda (s)
  (match s
     ((RLW_S0) `(False))
     ((RLW_S1) `(False))
     ((RLW_S2) `(True))
     ((RLW_S3) `(True))
     ((RLW_S4) `(True))
     ((RLW_S5) `(True))
     ((RLW_S6) `(True))
     ((RLW_Sbad) `(False)))))

(define is_rlw_mask_rec (lambdas (n s x)
  (match n
     ((O) (rlw_accepting s))
     ((S m)
       (match (z_bin_decomp x)
          ((Pair b y) (@ is_rlw_mask_rec m (@ rlw_transition s b) y)))))))
  
(define is_rlw_mask (lambdas (wordsize_minus_one x)
  (@ is_rlw_mask_rec (wordsize wordsize_minus_one) `(RLW_S0)
    (@ unsigned wordsize_minus_one x))))

(define cmp (lambdas (wordsize_minus_one c x y)
  (match c
     ((Ceq) (@ eq wordsize_minus_one x y))
     ((Cne) (negb (@ eq wordsize_minus_one x y)))
     ((Clt) (@ lt wordsize_minus_one x y))
     ((Cle) (negb (@ lt wordsize_minus_one y x)))
     ((Cgt) (@ lt wordsize_minus_one y x))
     ((Cge) (negb (@ lt wordsize_minus_one x y))))))

(define cmpu (lambdas (wordsize_minus_one c x y)
  (match c
     ((Ceq) (@ eq wordsize_minus_one x y))
     ((Cne) (negb (@ eq wordsize_minus_one x y)))
     ((Clt) (@ ltu wordsize_minus_one x y))
     ((Cle) (negb (@ ltu wordsize_minus_one y x)))
     ((Cgt) (@ ltu wordsize_minus_one y x))
     ((Cge) (negb (@ ltu wordsize_minus_one x y))))))

(define notbool (lambdas (wordsize_minus_one x)
  (match (@ eq wordsize_minus_one x (zero1 wordsize_minus_one))
     ((True) (one1 wordsize_minus_one))
     ((False) (zero1 wordsize_minus_one)))))

(define check_equal_on_range (lambdas (wordsize_minus_one f g n)
  (match n
     ((O) `(True))
     ((S n0)
       (match (@ eq wordsize_minus_one
                (f (@ repr wordsize_minus_one (of_nat1 n0)))
                (g (@ repr wordsize_minus_one (of_nat1 n0))))
          ((True) (@ check_equal_on_range wordsize_minus_one f g n0))
          ((False) `(False)))))))
  
(define powerserie (lambda (l)
  (match l
     ((Nil) `(Z0))
     ((Cons x xs) (@ add1 (two_p x) (powerserie xs))))))
  
(define int_of_one_bits (lambdas (wordsize_minus_one l)
  (match l
     ((Nil) (zero1 wordsize_minus_one))
     ((Cons a b)
       (@ add2 wordsize_minus_one
         (@ shl wordsize_minus_one (one1 wordsize_minus_one) a)
         (@ int_of_one_bits wordsize_minus_one b))))))
  
(define string_to_bool_list (lambda (s)
  (match s
     ((EmptyString) `(Nil))
     ((String a s0) `(Cons
       ,(match (@ ascii_dec a `(Ascii ,`(False) ,`(False) ,`(False) ,`(False)
                 ,`(True) ,`(True) ,`(False) ,`(False)))
           ((Left) `(False))
           ((Right) `(True))) ,(string_to_bool_list s0))))))
  
(define string_to_Z_bool (lambda (s)
  (let ((lb (string_to_bool_list s)))
    (letrec ((to_Z_bool
            (lambdas (l
            i)
            (match l
               ((Nil) `(False))
               ((Cons b l~)
                 (match (@ zeq i `(Z0))
                    ((Left) b)
                    ((Right) (@ to_Z_bool l~ (@ sub1 i `(Zpos ,`(XH)))))))))))
            (to_Z_bool (rev lb))))))
  
(define string_to_int (lambdas (n s)
  (let ((zb (string_to_Z_bool s))) (@ repr n (@ z_of_bits n zb)))))

(define register_eq_dec (lambdas (x y)
  (match x
     ((EAX)
       (match y
          ((EAX) `(Left))
          ((ECX) `(Right))
          ((EDX) `(Right))
          ((EBX) `(Right))
          ((ESP) `(Right))
          ((EBP) `(Right))
          ((ESI) `(Right))
          ((EDI) `(Right))))
     ((ECX)
       (match y
          ((EAX) `(Right))
          ((ECX) `(Left))
          ((EDX) `(Right))
          ((EBX) `(Right))
          ((ESP) `(Right))
          ((EBP) `(Right))
          ((ESI) `(Right))
          ((EDI) `(Right))))
     ((EDX)
       (match y
          ((EAX) `(Right))
          ((ECX) `(Right))
          ((EDX) `(Left))
          ((EBX) `(Right))
          ((ESP) `(Right))
          ((EBP) `(Right))
          ((ESI) `(Right))
          ((EDI) `(Right))))
     ((EBX)
       (match y
          ((EAX) `(Right))
          ((ECX) `(Right))
          ((EDX) `(Right))
          ((EBX) `(Left))
          ((ESP) `(Right))
          ((EBP) `(Right))
          ((ESI) `(Right))
          ((EDI) `(Right))))
     ((ESP)
       (match y
          ((EAX) `(Right))
          ((ECX) `(Right))
          ((EDX) `(Right))
          ((EBX) `(Right))
          ((ESP) `(Left))
          ((EBP) `(Right))
          ((ESI) `(Right))
          ((EDI) `(Right))))
     ((EBP)
       (match y
          ((EAX) `(Right))
          ((ECX) `(Right))
          ((EDX) `(Right))
          ((EBX) `(Right))
          ((ESP) `(Right))
          ((EBP) `(Left))
          ((ESI) `(Right))
          ((EDI) `(Right))))
     ((ESI)
       (match y
          ((EAX) `(Right))
          ((ECX) `(Right))
          ((EDX) `(Right))
          ((EBX) `(Right))
          ((ESP) `(Right))
          ((EBP) `(Right))
          ((ESI) `(Left))
          ((EDI) `(Right))))
     ((EDI)
       (match y
          ((EAX) `(Right))
          ((ECX) `(Right))
          ((EDX) `(Right))
          ((EBX) `(Right))
          ((ESP) `(Right))
          ((EBP) `(Right))
          ((ESI) `(Right))
          ((EDI) `(Left)))))))

(define segment_register_eq_dec (lambdas (x y)
  (match x
     ((ES)
       (match y
          ((ES) `(Left))
          ((CS) `(Right))
          ((SS) `(Right))
          ((DS) `(Right))
          ((FS) `(Right))
          ((GS) `(Right))))
     ((CS)
       (match y
          ((ES) `(Right))
          ((CS) `(Left))
          ((SS) `(Right))
          ((DS) `(Right))
          ((FS) `(Right))
          ((GS) `(Right))))
     ((SS)
       (match y
          ((ES) `(Right))
          ((CS) `(Right))
          ((SS) `(Left))
          ((DS) `(Right))
          ((FS) `(Right))
          ((GS) `(Right))))
     ((DS)
       (match y
          ((ES) `(Right))
          ((CS) `(Right))
          ((SS) `(Right))
          ((DS) `(Left))
          ((FS) `(Right))
          ((GS) `(Right))))
     ((FS)
       (match y
          ((ES) `(Right))
          ((CS) `(Right))
          ((SS) `(Right))
          ((DS) `(Right))
          ((FS) `(Left))
          ((GS) `(Right))))
     ((GS)
       (match y
          ((ES) `(Right))
          ((CS) `(Right))
          ((SS) `(Right))
          ((DS) `(Right))
          ((FS) `(Right))
          ((GS) `(Left)))))))

(define control_register_eq_dec (lambdas (x y)
  (match x
     ((CR0)
       (match y
          ((CR0) `(Left))
          ((CR2) `(Right))
          ((CR3) `(Right))
          ((CR4) `(Right))))
     ((CR2)
       (match y
          ((CR0) `(Right))
          ((CR2) `(Left))
          ((CR3) `(Right))
          ((CR4) `(Right))))
     ((CR3)
       (match y
          ((CR0) `(Right))
          ((CR2) `(Right))
          ((CR3) `(Left))
          ((CR4) `(Right))))
     ((CR4)
       (match y
          ((CR0) `(Right))
          ((CR2) `(Right))
          ((CR3) `(Right))
          ((CR4) `(Left)))))))

(define debug_register_eq_dec (lambdas (x y)
  (match x
     ((DR0)
       (match y
          ((DR0) `(Left))
          ((DR1) `(Right))
          ((DR2) `(Right))
          ((DR3) `(Right))
          ((DR6) `(Right))
          ((DR7) `(Right))))
     ((DR1)
       (match y
          ((DR0) `(Right))
          ((DR1) `(Left))
          ((DR2) `(Right))
          ((DR3) `(Right))
          ((DR6) `(Right))
          ((DR7) `(Right))))
     ((DR2)
       (match y
          ((DR0) `(Right))
          ((DR1) `(Right))
          ((DR2) `(Left))
          ((DR3) `(Right))
          ((DR6) `(Right))
          ((DR7) `(Right))))
     ((DR3)
       (match y
          ((DR0) `(Right))
          ((DR1) `(Right))
          ((DR2) `(Right))
          ((DR3) `(Left))
          ((DR6) `(Right))
          ((DR7) `(Right))))
     ((DR6)
       (match y
          ((DR0) `(Right))
          ((DR1) `(Right))
          ((DR2) `(Right))
          ((DR3) `(Right))
          ((DR6) `(Left))
          ((DR7) `(Right))))
     ((DR7)
       (match y
          ((DR0) `(Right))
          ((DR1) `(Right))
          ((DR2) `(Right))
          ((DR3) `(Right))
          ((DR6) `(Right))
          ((DR7) `(Left)))))))

(define elt_eq peq)

(define tree_rect (lambdas (f f0 t)
  (match t
     ((Leaf) f)
     ((Node t0 o t1)
       (@ f0 t0 (@ tree_rect f f0 t0) o t1 (@ tree_rect f f0 t1))))))
  
(define tree_rec (lambdas (f f0 t)
  (match t
     ((Leaf) f)
     ((Node t0 o t1)
       (@ f0 t0 (@ tree_rec f f0 t0) o t1 (@ tree_rec f f0 t1))))))
  
(define eq0 (lambdas (eqA a b)
  (match a
     ((Leaf)
       (match b
          ((Leaf) `(Left))
          ((Node t0 o t1) `(Right))))
     ((Node t o t0)
       (match b
          ((Leaf) `(Right))
          ((Node t2 o0 t3)
            (match (@ eq0 eqA t t2)
               ((Left)
                 (match o
                    ((Some x)
                      (match o0
                         ((Some a1)
                           (match (@ eqA x a1)
                              ((Left)
                                (match (@ eq0 eqA t0 t3)
                                   ((Left) `(Left))
                                   ((Right) `(Right))))
                              ((Right) `(Right))))
                         ((None) `(Right))))
                    ((None)
                      (match o0
                         ((Some a0) `(Right))
                         ((None)
                           (match (@ eq0 eqA t0 t3)
                              ((Left) `(Left))
                              ((Right) `(Right))))))))
               ((Right) `(Right)))))))))
  
(define empty `(Leaf))

(define get (lambdas (i m)
  (match m
     ((Leaf) `(None))
     ((Node l o r)
       (match i
          ((XI ii) (@ get ii r))
          ((XO ii) (@ get ii l))
          ((XH) o))))))
  
(define set (lambdas (i v m)
  (match m
     ((Leaf)
       (match i
          ((XI ii) `(Node ,`(Leaf) ,`(None) ,(@ set ii v `(Leaf))))
          ((XO ii) `(Node ,(@ set ii v `(Leaf)) ,`(None) ,`(Leaf)))
          ((XH) `(Node ,`(Leaf) ,`(Some ,v) ,`(Leaf)))))
     ((Node l o r)
       (match i
          ((XI ii) `(Node ,l ,o ,(@ set ii v r)))
          ((XO ii) `(Node ,(@ set ii v l) ,o ,r))
          ((XH) `(Node ,l ,`(Some ,v) ,r)))))))
  
(define remove (lambdas (i m)
  (match i
     ((XI ii)
       (match m
          ((Leaf) `(Leaf))
          ((Node l o r)
            (match l
               ((Leaf)
                 (match o
                    ((Some a) `(Node ,l ,o ,(@ remove ii r)))
                    ((None)
                      (match (@ remove ii r)
                         ((Leaf) `(Leaf))
                         ((Node t o0 t0) `(Node ,`(Leaf) ,`(None) ,`(Node ,t
                           ,o0 ,t0)))))))
               ((Node t o0 t0) `(Node ,l ,o ,(@ remove ii r)))))))
     ((XO ii)
       (match m
          ((Leaf) `(Leaf))
          ((Node l o r)
            (match o
               ((Some a) `(Node ,(@ remove ii l) ,o ,r))
               ((None)
                 (match r
                    ((Leaf)
                      (match (@ remove ii l)
                         ((Leaf) `(Leaf))
                         ((Node t o0 t0) `(Node ,`(Node ,t ,o0 ,t0) ,`(None)
                           ,`(Leaf)))))
                    ((Node t o0 t0) `(Node ,(@ remove ii l) ,o ,r))))))))
     ((XH)
       (match m
          ((Leaf) `(Leaf))
          ((Node l o r)
            (match l
               ((Leaf)
                 (match r
                    ((Leaf) `(Leaf))
                    ((Node t o0 t0) `(Node ,l ,`(None) ,r))))
               ((Node t o0 t0) `(Node ,l ,`(None) ,r)))))))))
  
(define bempty (lambda (m)
  (match m
     ((Leaf) `(True))
     ((Node l o r)
       (match o
          ((Some a) `(False))
          ((None)
            (match (bempty l)
               ((True) (bempty r))
               ((False) `(False)))))))))
  
(define beq (lambdas (beqA m1 m2)
  (match m1
     ((Leaf) (bempty m2))
     ((Node l1 o1 r1)
       (match m2
          ((Leaf) (bempty m1))
          ((Node l2 o2 r2)
            (match (match (match o1
                             ((Some y1)
                               (match o2
                                  ((Some y2) (@ beqA y1 y2))
                                  ((None) `(False))))
                             ((None)
                               (match o2
                                  ((Some a) `(False))
                                  ((None) `(True)))))
                      ((True) (@ beq beqA l1 l2))
                      ((False) `(False)))
               ((True) (@ beq beqA r1 r2))
               ((False) `(False)))))))))
  
(define append (lambdas (i j)
  (match i
     ((XI ii) `(XI ,(@ append ii j)))
     ((XO ii) `(XO ,(@ append ii j)))
     ((XH) j))))
  
(define xmap (lambdas (f m i)
  (match m
     ((Leaf) `(Leaf))
     ((Node l o r) `(Node ,(@ xmap f l (@ append i `(XO ,`(XH))))
       ,(@ option_map (f i) o) ,(@ xmap f r (@ append i `(XI ,`(XH)))))))))
  
(define map0 (lambdas (f m) (@ xmap f m `(XH))))

(define node~ (lambdas (l x r)
  (match l
     ((Leaf)
       (match x
          ((Some a) `(Node ,l ,x ,r))
          ((None)
            (match r
               ((Leaf) `(Leaf))
               ((Node t o t0) `(Node ,l ,x ,r))))))
     ((Node t o t0) `(Node ,l ,x ,r)))))

(define xcombine_l (lambdas (f m)
  (match m
     ((Leaf) `(Leaf))
     ((Node l o r)
       (@ node~ (@ xcombine_l f l) (@ f o `(None)) (@ xcombine_l f r))))))
  
(define xcombine_r (lambdas (f m)
  (match m
     ((Leaf) `(Leaf))
     ((Node l o r)
       (@ node~ (@ xcombine_r f l) (@ f `(None) o) (@ xcombine_r f r))))))
  
(define combine (lambdas (f m1 m2)
  (match m1
     ((Leaf) (@ xcombine_r f m2))
     ((Node l1 o1 r1)
       (match m2
          ((Leaf) (@ xcombine_l f m1))
          ((Node l2 o2 r2)
            (@ node~ (@ combine f l1 l2) (@ f o1 o2) (@ combine f r1 r2))))))))
  
(define xelements (lambdas (m i)
  (match m
     ((Leaf) `(Nil))
     ((Node l o r)
       (match o
          ((Some x)
            (@ app (@ xelements l (@ append i `(XO ,`(XH)))) `(Cons ,`(Pair
              ,i ,x) ,(@ xelements r (@ append i `(XI ,`(XH)))))))
          ((None)
            (@ app (@ xelements l (@ append i `(XO ,`(XH))))
              (@ xelements r (@ append i `(XI ,`(XH)))))))))))
  
(define elements (lambda (m) (@ xelements m `(XH))))

(define xget (lambdas (i j m)
  (match i
     ((XI ii)
       (match j
          ((XI jj) (@ xget ii jj m))
          ((XO p) `(None))
          ((XH) (@ get i m))))
     ((XO ii)
       (match j
          ((XI p) `(None))
          ((XO jj) (@ xget ii jj m))
          ((XH) (@ get i m))))
     ((XH)
       (match j
          ((XI p) `(None))
          ((XO p) `(None))
          ((XH) (@ get i m)))))))
  
(define xkeys (lambdas (m i) (@ map fst (@ xelements m i))))

(define xfold (lambdas (f i m v)
  (match m
     ((Leaf) v)
     ((Node l o r)
       (match o
          ((Some x)
            (let ((v1 (@ xfold f (@ append i `(XO ,`(XH))) l v)))
              (let ((v2 (@ f v1 i x)))
                (@ xfold f (@ append i `(XI ,`(XH))) r v2))))
          ((None)
            (let ((v1 (@ xfold f (@ append i `(XO ,`(XH))) l v)))
              (@ xfold f (@ append i `(XI ,`(XH))) r v1))))))))
  
(define fold (lambdas (f m v) (@ xfold f `(XH) m v)))

(define elt_eq0 peq)

(define eq1 (lambdas (x a b)
  (let ((x0 (eq0 x)))
    (match a
       ((Pair x1 x2)
         (match b
            ((Pair a1 t0)
              (match (@ x x1 a1)
                 ((Left)
                   (match (@ x0 x2 t0)
                      ((Left) `(Left))
                      ((Right) `(Right))))
                 ((Right) `(Right))))))))))

(define init (lambda (x) `(Pair ,x ,empty)))

(define get0 (lambdas (i m)
  (match (@ get i (snd m))
     ((Some x) x)
     ((None) (fst m)))))

(define set0 (lambdas (i x m) `(Pair ,(fst m) ,(@ set i x (snd m)))))

(define map1 (lambdas (f m) `(Pair ,(f (fst m))
  ,(@ map0 (lambda (x) f) (snd m)))))

(define index (lambda (z)
  (match z
     ((Z0) `(XH))
     ((Zpos p) `(XO ,p))
     ((Zneg p) `(XI ,p)))))

(define eq2 zeq)

(define return (lambdas (monad x)
  (match monad
     ((Build_Monad return0 bind1) (@ return0 __ x)))))

(define bind (lambdas (monad x x0)
  (match monad
     ((Build_Monad return0 bind1) (@ bind1 __ __ x x0)))))

(define zeven (lambda (n)
  (match n
     ((Z0) `(True))
     ((Zpos p)
       (match p
          ((XI p0) `(False))
          ((XO p0) `(True))
          ((XH) `(False))))
     ((Zneg p)
       (match p
          ((XI p0) `(False))
          ((XO p0) `(True))
          ((XH) `(False)))))))

(define cond_Zopp (lambdas (b m)
  (match b
     ((True) (opp m))
     ((False) m))))

(define fLT_exp (lambdas (emin prec e) (@ max1 (@ sub1 e prec) emin)))

(define digits2_Pnat (lambda (n)
  (match n
     ((XI p) `(S ,(digits2_Pnat p)))
     ((XO p) `(S ,(digits2_Pnat p)))
     ((XH) `(O)))))
  
(define new_location_even (lambdas (nb_steps k l)
  (match (@ zeq_bool k `(Z0))
     ((True)
       (match l
          ((Loc_Exact) l)
          ((Loc_Inexact c) `(Loc_Inexact ,`(Lt)))))
     ((False) `(Loc_Inexact
       ,(match (@ compare1 (@ mul1 `(Zpos ,`(XO ,`(XH))) k) nb_steps)
           ((Eq)
             (match l
                ((Loc_Exact) `(Eq))
                ((Loc_Inexact c) `(Gt))))
           ((Lt) `(Lt))
           ((Gt) `(Gt))))))))

(define new_location_odd (lambdas (nb_steps k l)
  (match (@ zeq_bool k `(Z0))
     ((True)
       (match l
          ((Loc_Exact) l)
          ((Loc_Inexact c) `(Loc_Inexact ,`(Lt)))))
     ((False) `(Loc_Inexact
       ,(match (@ compare1
                 (@ add1 (@ mul1 `(Zpos ,`(XO ,`(XH))) k) `(Zpos ,`(XH)))
                 nb_steps)
           ((Eq)
             (match l
                ((Loc_Exact) `(Lt))
                ((Loc_Inexact l0) l0)))
           ((Lt) `(Lt))
           ((Gt) `(Gt))))))))

(define new_location (lambda (nb_steps)
  (match (zeven nb_steps)
     ((True) (new_location_even nb_steps))
     ((False) (new_location_odd nb_steps)))))

(define cond_incr (lambdas (b m)
  (match b
     ((True) (@ add1 m `(Zpos ,`(XH))))
     ((False) m))))

(define round_sign_DN (lambdas (s l)
  (match l
     ((Loc_Exact) `(False))
     ((Loc_Inexact c) s))))

(define round_sign_UP (lambdas (s l)
  (match l
     ((Loc_Exact) `(False))
     ((Loc_Inexact c) (negb s)))))

(define round_N (lambdas (p l)
  (match l
     ((Loc_Exact) `(False))
     ((Loc_Inexact c)
       (match c
          ((Eq) p)
          ((Lt) `(False))
          ((Gt) `(True)))))))

(define fF2B (lambdas (prec emax x)
  (match x
     ((F754_zero s) `(B754_zero ,s))
     ((F754_infinity s) `(B754_infinity ,s))
     ((F754_nan) `(B754_nan))
     ((F754_finite s m e) `(B754_finite ,s ,m ,e)))))

(define bopp (lambdas (prec emax x)
  (match x
     ((B754_zero sx) `(B754_zero ,(negb sx)))
     ((B754_infinity sx) `(B754_infinity ,(negb sx)))
     ((B754_nan) x)
     ((B754_finite sx mx ex) `(B754_finite ,(negb sx) ,mx ,ex)))))

(define shr_m (lambda (s)
  (match s
     ((Build_shr_record shr_m0 shr_r shr_s) shr_m0))))

(define shr_1 (lambda (mrs)
  (match mrs
     ((Build_shr_record m r s)
       (let ((s0
         (match r
            ((True) `(True))
            ((False) s))))
         (match m
            ((Z0) `(Build_shr_record ,`(Z0) ,`(False) ,s0))
            ((Zpos p0)
              (match p0
                 ((XI p) `(Build_shr_record ,`(Zpos ,p) ,`(True) ,s0))
                 ((XO p) `(Build_shr_record ,`(Zpos ,p) ,`(False) ,s0))
                 ((XH) `(Build_shr_record ,`(Z0) ,`(True) ,s0))))
            ((Zneg p0)
              (match p0
                 ((XI p) `(Build_shr_record ,`(Zneg ,p) ,`(True) ,s0))
                 ((XO p) `(Build_shr_record ,`(Zneg ,p) ,`(False) ,s0))
                 ((XH) `(Build_shr_record ,`(Z0) ,`(True) ,s0))))))))))

(define loc_of_shr_record (lambda (mrs)
  (match mrs
     ((Build_shr_record shr_m0 shr_r shr_s)
       (match shr_r
          ((True)
            (match shr_s
               ((True) `(Loc_Inexact ,`(Gt)))
               ((False) `(Loc_Inexact ,`(Eq)))))
          ((False)
            (match shr_s
               ((True) `(Loc_Inexact ,`(Lt)))
               ((False) `(Loc_Exact)))))))))

(define shr_record_of_loc (lambdas (m l)
  (match l
     ((Loc_Exact) `(Build_shr_record ,m ,`(False) ,`(False)))
     ((Loc_Inexact c)
       (match c
          ((Eq) `(Build_shr_record ,m ,`(True) ,`(False)))
          ((Lt) `(Build_shr_record ,m ,`(False) ,`(True)))
          ((Gt) `(Build_shr_record ,m ,`(True) ,`(True))))))))

(define shr0 (lambdas (mrs e n)
  (match n
     ((Z0) `(Pair ,mrs ,e))
     ((Zpos p) `(Pair ,(@ iter p shr_1 mrs) ,(@ add1 e n)))
     ((Zneg p) `(Pair ,mrs ,e)))))

(define zdigits2 (lambda (m)
  (match m
     ((Z0) m)
     ((Zpos p) (of_nat1 `(S ,(digits2_Pnat p))))
     ((Zneg p) (of_nat1 `(S ,(digits2_Pnat p)))))))

(define shr_fexp (lambdas (prec emax)
  (let ((emin (@ sub1 (@ sub1 `(Zpos ,`(XI ,`(XH))) emax) prec)))
    (let ((fexp (@ fLT_exp emin prec)))
      (lambdas (m e l)
      (@ shr0 (@ shr_record_of_loc m l) e
        (@ sub1 (fexp (@ add1 (zdigits2 m) e)) e)))))))

(define choice_mode (lambdas (m sx mx lx)
  (match m
     ((Mode_NE) (@ cond_incr (@ round_N (negb (zeven mx)) lx) mx))
     ((Mode_ZR) mx)
     ((Mode_DN) (@ cond_incr (@ round_sign_DN sx lx) mx))
     ((Mode_UP) (@ cond_incr (@ round_sign_UP sx lx) mx))
     ((Mode_NA) (@ cond_incr (@ round_N `(True) lx) mx)))))

(define overflow_to_inf (lambdas (m s)
  (match m
     ((Mode_NE) `(True))
     ((Mode_ZR) `(False))
     ((Mode_DN) s)
     ((Mode_UP) (negb s))
     ((Mode_NA) `(True)))))

(define binary_overflow (lambdas (prec emax m s)
  (match (@ overflow_to_inf m s)
     ((True) `(F754_infinity ,s))
     ((False) `(F754_finite ,s
       ,(match (@ sub1 (@ pow1 `(Zpos ,`(XO ,`(XH))) prec) `(Zpos ,`(XH)))
           ((Z0) `(XH))
           ((Zpos p) p)
           ((Zneg p) `(XH))) ,(@ sub1 emax prec))))))

(define binary_round_aux (lambdas (prec emax mode sx mx ex lx)
  (match (@ shr_fexp prec emax `(Zpos ,mx) ex lx)
     ((Pair mrs~ e~)
       (match (@ shr_fexp prec emax
                (@ choice_mode mode sx (shr_m mrs~) (loc_of_shr_record mrs~))
                e~ `(Loc_Exact))
          ((Pair mrs~~ e~~)
            (match (shr_m mrs~~)
               ((Z0) `(F754_zero ,sx))
               ((Zpos m)
                 (match (@ leb1 e~~ (@ sub1 emax prec))
                    ((True) `(F754_finite ,sx ,m ,e~~))
                    ((False) (@ binary_overflow prec emax mode sx))))
               ((Zneg p) `(F754_nan)))))))))

(define bmult (lambdas (prec emax m x y)
  (match x
     ((B754_zero sx)
       (match y
          ((B754_zero sy) `(B754_zero ,(@ xorb sx sy)))
          ((B754_infinity b) `(B754_nan))
          ((B754_nan) y)
          ((B754_finite sy m0 e) `(B754_zero ,(@ xorb sx sy)))))
     ((B754_infinity sx)
       (match y
          ((B754_zero b) `(B754_nan))
          ((B754_infinity sy) `(B754_infinity ,(@ xorb sx sy)))
          ((B754_nan) y)
          ((B754_finite sy m0 e) `(B754_infinity ,(@ xorb sx sy)))))
     ((B754_nan) x)
     ((B754_finite sx mx ex)
       (match y
          ((B754_zero sy) `(B754_zero ,(@ xorb sx sy)))
          ((B754_infinity sy) `(B754_infinity ,(@ xorb sx sy)))
          ((B754_nan) y)
          ((B754_finite sy my ey)
            (@ fF2B prec emax
              (@ binary_round_aux prec emax m (@ xorb sx sy) (@ mul mx my)
                (@ add1 ex ey) `(Loc_Exact)))))))))

(define shl_align (lambdas (mx ex ex~)
  (match (@ sub1 ex~ ex)
     ((Z0) `(Pair ,mx ,ex))
     ((Zpos p) `(Pair ,mx ,ex))
     ((Zneg d) `(Pair ,(@ shift_pos d mx) ,ex~)))))

(define shl_align_fexp (lambdas (prec emax)
  (let ((emin (@ sub1 (@ sub1 `(Zpos ,`(XI ,`(XH))) emax) prec)))
    (let ((fexp (@ fLT_exp emin prec)))
      (lambdas (mx ex)
      (@ shl_align mx ex
        (fexp (@ add1 (of_nat1 `(S ,(digits2_Pnat mx))) ex))))))))

(define binary_round (lambdas (prec emax m sx mx ex)
  (match (@ shl_align_fexp prec emax mx ex)
     ((Pair mz ez) (@ binary_round_aux prec emax m sx mz ez `(Loc_Exact))))))

(define binary_normalize (lambdas (prec emax mode m e szero)
  (match m
     ((Z0) `(B754_zero ,szero))
     ((Zpos m0)
       (@ fF2B prec emax (@ binary_round prec emax mode `(False) m0 e)))
     ((Zneg m0)
       (@ fF2B prec emax (@ binary_round prec emax mode `(True) m0 e))))))

(define bplus (lambdas (prec emax m x y)
  (match x
     ((B754_zero sx)
       (match y
          ((B754_zero sy)
            (match (@ eqb sx sy)
               ((True) x)
               ((False)
                 (match m
                    ((Mode_NE) `(B754_zero ,`(False)))
                    ((Mode_ZR) `(B754_zero ,`(False)))
                    ((Mode_DN) `(B754_zero ,`(True)))
                    ((Mode_UP) `(B754_zero ,`(False)))
                    ((Mode_NA) `(B754_zero ,`(False)))))))
          ((B754_infinity b) y)
          ((B754_nan) y)
          ((B754_finite b m0 e) y)))
     ((B754_infinity sx)
       (match y
          ((B754_zero b) x)
          ((B754_infinity sy)
            (match (@ eqb sx sy)
               ((True) x)
               ((False) `(B754_nan))))
          ((B754_nan) y)
          ((B754_finite b m0 e) x)))
     ((B754_nan) x)
     ((B754_finite sx mx ex)
       (match y
          ((B754_zero b) x)
          ((B754_infinity b) y)
          ((B754_nan) y)
          ((B754_finite sy my ey)
            (let ((ez (@ min1 ex ey)))
              (@ binary_normalize prec emax m
                (@ add1
                  (@ cond_Zopp sx `(Zpos ,(fst (@ shl_align mx ex ez))))
                  (@ cond_Zopp sy `(Zpos ,(fst (@ shl_align my ey ez))))) ez
                (match m
                   ((Mode_NE) `(False))
                   ((Mode_ZR) `(False))
                   ((Mode_DN) `(True))
                   ((Mode_UP) `(False))
                   ((Mode_NA) `(False)))))))))))

(define bminus (lambdas (prec emax m x y)
  (@ bplus prec emax m x (@ bopp prec emax y))))

(define fdiv_core_binary (lambdas (prec m1 e1 m2 e2)
  (let ((d1 (zdigits2 m1)))
    (let ((d2 (zdigits2 m2)))
      (let ((e (@ sub1 e1 e2)))
        (match (@ sub1 (@ add1 d2 prec) d1)
           ((Z0)
             (match (@ div_eucl0 m1 m2)
                ((Pair q r) `(Pair ,`(Pair ,q ,e)
                  ,(@ new_location m2 r `(Loc_Exact))))))
           ((Zpos p)
             (let ((m (@ mul1 m1 (@ pow_pos `(Zpos ,`(XO ,`(XH))) p))))
               (let ((e~ (@ add1 e `(Zneg ,p))))
                 (match (@ div_eucl0 m m2)
                    ((Pair q r) `(Pair ,`(Pair ,q ,e~)
                      ,(@ new_location m2 r `(Loc_Exact))))))))
           ((Zneg p)
             (match (@ div_eucl0 m1 m2)
                ((Pair q r) `(Pair ,`(Pair ,q ,e)
                  ,(@ new_location m2 r `(Loc_Exact))))))))))))

(define bdiv (lambdas (prec emax m x y)
  (match x
     ((B754_zero sx)
       (match y
          ((B754_zero sy) `(B754_nan))
          ((B754_infinity sy) `(B754_zero ,(@ xorb sx sy)))
          ((B754_nan) y)
          ((B754_finite sy m0 e) `(B754_zero ,(@ xorb sx sy)))))
     ((B754_infinity sx)
       (match y
          ((B754_zero sy) `(B754_infinity ,(@ xorb sx sy)))
          ((B754_infinity sy) `(B754_nan))
          ((B754_nan) y)
          ((B754_finite sy m0 e) `(B754_infinity ,(@ xorb sx sy)))))
     ((B754_nan) x)
     ((B754_finite sx mx ex)
       (match y
          ((B754_zero sy) `(B754_infinity ,(@ xorb sx sy)))
          ((B754_infinity sy) `(B754_infinity ,(@ xorb sx sy)))
          ((B754_nan) y)
          ((B754_finite sy my ey)
            (@ fF2B prec emax
              (match (@ fdiv_core_binary prec `(Zpos ,mx) ex `(Zpos ,my) ey)
                 ((Pair p lz)
                   (match p
                      ((Pair mz ez)
                        (match mz
                           ((Z0) `(F754_nan))
                           ((Zpos mz0)
                             (@ binary_round_aux prec emax m (@ xorb sx sy)
                               mz0 ez lz))
                           ((Zneg p0) `(F754_nan))))))))))))))

(define join_bits (lambdas (mw ew s m e)
  (@ add1
    (@ mul1
      (@ add1
        (match s
           ((True) (@ pow1 `(Zpos ,`(XO ,`(XH))) ew))
           ((False) `(Z0))) e) (@ pow1 `(Zpos ,`(XO ,`(XH))) mw)) m)))

(define split_bits (lambdas (mw ew x)
  (let ((mm (@ pow1 `(Zpos ,`(XO ,`(XH))) mw)))
    (let ((em (@ pow1 `(Zpos ,`(XO ,`(XH))) ew)))
      `(Pair ,`(Pair ,(@ leb1 (@ mul1 mm em) x) ,(@ modulo0 x mm))
      ,(@ modulo0 (@ div1 x mm) em))))))

(define bits_of_binary_float (lambdas (mw ew)
  (let ((emax (@ pow1 `(Zpos ,`(XO ,`(XH))) (@ sub1 ew `(Zpos ,`(XH))))))
    (let ((prec (@ add1 mw `(Zpos ,`(XH)))))
      (let ((emin (@ sub1 (@ sub1 `(Zpos ,`(XI ,`(XH))) emax) prec)))
        (lambda (x)
        (match x
           ((B754_zero sx) (@ join_bits mw ew sx `(Z0) `(Z0)))
           ((B754_infinity sx)
             (@ join_bits mw ew sx `(Z0)
               (@ sub1 (@ pow1 `(Zpos ,`(XO ,`(XH))) ew) `(Zpos ,`(XH)))))
           ((B754_nan)
             (@ join_bits mw ew `(False)
               (@ sub1 (@ pow1 `(Zpos ,`(XO ,`(XH))) mw) `(Zpos ,`(XH)))
               (@ sub1 (@ pow1 `(Zpos ,`(XO ,`(XH))) ew) `(Zpos ,`(XH)))))
           ((B754_finite sx mx ex)
             (match (@ leb1 (@ pow1 `(Zpos ,`(XO ,`(XH))) mw) `(Zpos ,mx))
                ((True)
                  (@ join_bits mw ew sx
                    (@ sub1 `(Zpos ,mx) (@ pow1 `(Zpos ,`(XO ,`(XH))) mw))
                    (@ add1 (@ sub1 ex emin) `(Zpos ,`(XH)))))
                ((False) (@ join_bits mw ew sx `(Zpos ,mx) `(Z0))))))))))))

(define binary_float_of_bits_aux (lambdas (mw ew)
  (let ((emax (@ pow1 `(Zpos ,`(XO ,`(XH))) (@ sub1 ew `(Zpos ,`(XH))))))
    (let ((prec (@ add1 mw `(Zpos ,`(XH)))))
      (let ((emin (@ sub1 (@ sub1 `(Zpos ,`(XI ,`(XH))) emax) prec)))
        (lambda (x)
        (match (@ split_bits mw ew x)
           ((Pair p ex)
             (match p
                ((Pair sx mx)
                  (match (@ zeq_bool ex `(Z0))
                     ((True)
                       (match mx
                          ((Z0) `(F754_zero ,sx))
                          ((Zpos px) `(F754_finite ,sx ,px ,emin))
                          ((Zneg p0) `(F754_nan))))
                     ((False)
                       (match (@ zeq_bool ex
                                (@ sub1 (@ pow1 `(Zpos ,`(XO ,`(XH))) ew)
                                  `(Zpos ,`(XH))))
                          ((True)
                            (match (@ zeq_bool mx `(Z0))
                               ((True) `(F754_infinity ,sx))
                               ((False) `(F754_nan))))
                          ((False)
                            (match (@ add1 mx
                                     (@ pow1 `(Zpos ,`(XO ,`(XH))) mw))
                               ((Z0) `(F754_nan))
                               ((Zpos px) `(F754_finite ,sx ,px
                                 ,(@ sub1 (@ add1 ex emin) `(Zpos ,`(XH)))))
                               ((Zneg p0) `(F754_nan)))))))))))))))))

(define binary_float_of_bits (lambdas (mw ew x)
  (let ((emax (@ pow1 `(Zpos ,`(XO ,`(XH))) (@ sub1 ew `(Zpos ,`(XH))))))
    (let ((prec (@ add1 mw `(Zpos ,`(XH)))))
      (@ fF2B prec emax (@ binary_float_of_bits_aux mw ew x))))))

(define size1 `(O))

(define size2 `(S ,`(O)))

(define size3 `(S ,`(S ,`(O))))

(define size8 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))

(define size32 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))))))))))))))))))))

(define size_addr size32)

(define flag_rect (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
  f14 f15 f16)
  (match f16
     ((ID) f)
     ((VIP) f0)
     ((VIF) f1)
     ((AC) f2)
     ((VM) f3)
     ((RF) f4)
     ((NT) f5)
     ((IOPL) f6)
     ((OF) f7)
     ((DF) f8)
     ((IF_flag) f9)
     ((TF) f10)
     ((SF) f11)
     ((ZF) f12)
     ((AF) f13)
     ((PF) f14)
     ((CF) f15))))

(define flag_rec (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
  f14 f15 f16)
  (match f16
     ((ID) f)
     ((VIP) f0)
     ((VIF) f1)
     ((AC) f2)
     ((VM) f3)
     ((RF) f4)
     ((NT) f5)
     ((IOPL) f6)
     ((OF) f7)
     ((DF) f8)
     ((IF_flag) f9)
     ((TF) f10)
     ((SF) f11)
     ((ZF) f12)
     ((AF) f13)
     ((PF) f14)
     ((CF) f15))))

(define flag_eq_dec (lambdas (f1 f2)
  (match f1
     ((ID)
       (match f2
          ((ID) `(Left))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((VIP)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Left))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((VIF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Left))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((AC)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Left))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((VM)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Left))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((RF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Left))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((NT)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Left))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((IOPL)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Left))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((OF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Left))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((DF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Left))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((IF_flag)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Left))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((TF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Left))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((SF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Left))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((ZF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Left))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((AF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Left))
          ((PF) `(Right))
          ((CF) `(Right))))
     ((PF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Left))
          ((CF) `(Right))))
     ((CF)
       (match f2
          ((ID) `(Right))
          ((VIP) `(Right))
          ((VIF) `(Right))
          ((AC) `(Right))
          ((VM) `(Right))
          ((RF) `(Right))
          ((NT) `(Right))
          ((IOPL) `(Right))
          ((OF) `(Right))
          ((DF) `(Right))
          ((IF_flag) `(Right))
          ((TF) `(Right))
          ((SF) `(Right))
          ((ZF) `(Right))
          ((AF) `(Right))
          ((PF) `(Right))
          ((CF) `(Left)))))))

(define fpu_flag_rect (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12)
  (match f12
     ((F_Busy) f)
     ((F_C3) f0)
     ((F_C2) f1)
     ((F_C1) f2)
     ((F_C0) f3)
     ((F_ES) f4)
     ((F_SF) f5)
     ((F_PE) f6)
     ((F_UE) f7)
     ((F_OE) f8)
     ((F_ZE) f9)
     ((F_DE) f10)
     ((F_IE) f11))))

(define fpu_flag_rec (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12)
  (match f12
     ((F_Busy) f)
     ((F_C3) f0)
     ((F_C2) f1)
     ((F_C1) f2)
     ((F_C0) f3)
     ((F_ES) f4)
     ((F_SF) f5)
     ((F_PE) f6)
     ((F_UE) f7)
     ((F_OE) f8)
     ((F_ZE) f9)
     ((F_DE) f10)
     ((F_IE) f11))))

(define fpu_ctrl_flag_rect (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11)
  (match f11
     ((F_Res15) f)
     ((F_Res14) f0)
     ((F_Res13) f1)
     ((F_Res7) f2)
     ((F_Res6) f3)
     ((F_IC) f4)
     ((F_PM) f5)
     ((F_UM) f6)
     ((F_OM) f7)
     ((F_ZM) f8)
     ((F_DM) f9)
     ((F_IM) f10))))

(define fpu_ctrl_flag_rec (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11)
  (match f11
     ((F_Res15) f)
     ((F_Res14) f0)
     ((F_Res13) f1)
     ((F_Res7) f2)
     ((F_Res6) f3)
     ((F_IC) f4)
     ((F_PM) f5)
     ((F_UM) f6)
     ((F_OM) f7)
     ((F_ZM) f8)
     ((F_DM) f9)
     ((F_IM) f10))))

(define size11 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(O))))))))))))

(define size48 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(O)))))))))))))))))))))))))))))))))))))))))))))))))

(define loc_rect (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 n
  l)
  (match l
     ((Reg_loc x) (f x))
     ((Seg_reg_start_loc x) (f0 x))
     ((Seg_reg_limit_loc x) (f1 x))
     ((Flag_loc x) (f2 x))
     ((Control_register_loc x) (f3 x))
     ((Debug_register_loc x) (f4 x))
     ((Pc_loc) f5)
     ((Fpu_stktop_loc) f6)
     ((Fpu_flag_loc x) (f7 x))
     ((Fpu_rctrl_loc) f8)
     ((Fpu_pctrl_loc) f9)
     ((Fpu_ctrl_flag_loc x) (f10 x))
     ((Fpu_lastInstrPtr_loc) f11)
     ((Fpu_lastDataPtr_loc) f12)
     ((Fpu_lastOpcode_loc) f13))))

(define loc_rec (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 n
  l)
  (match l
     ((Reg_loc x) (f x))
     ((Seg_reg_start_loc x) (f0 x))
     ((Seg_reg_limit_loc x) (f1 x))
     ((Flag_loc x) (f2 x))
     ((Control_register_loc x) (f3 x))
     ((Debug_register_loc x) (f4 x))
     ((Pc_loc) f5)
     ((Fpu_stktop_loc) f6)
     ((Fpu_flag_loc x) (f7 x))
     ((Fpu_rctrl_loc) f8)
     ((Fpu_pctrl_loc) f9)
     ((Fpu_ctrl_flag_loc x) (f10 x))
     ((Fpu_lastInstrPtr_loc) f11)
     ((Fpu_lastDataPtr_loc) f12)
     ((Fpu_lastOpcode_loc) f13))))

(define arr_rect (lambdas (f f0 n n0 a)
  (match a
     ((Fpu_datareg) f)
     ((Fpu_tag) f0))))

(define arr_rec (lambdas (f f0 n n0 a)
  (match a
     ((Fpu_datareg) f)
     ((Fpu_tag) f0))))

(define upd (lambdas (eq_dec3 f x v y)
  (match (@ eq_dec3 x y)
     ((Left) v)
     ((Right) (f y)))))

(define look (lambdas (f x) (f x)))

(define core_state_rect (lambdas (f c)
  (match c
     ((Build_core_state x x0 x1 x2 x3 x4 x5) (@ f x x0 x1 x2 x3 x4 x5)))))

(define core_state_rec (lambdas (f c)
  (match c
     ((Build_core_state x x0 x1 x2 x3 x4 x5) (@ f x x0 x1 x2 x3 x4 x5)))))

(define gp_regs (lambda (c)
  (match c
     ((Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
       control_regs0 debug_regs0 pc_reg0) gp_regs0))))

(define seg_regs_starts (lambda (c)
  (match c
     ((Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
       control_regs0 debug_regs0 pc_reg0) seg_regs_starts0))))

(define seg_regs_limits (lambda (c)
  (match c
     ((Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
       control_regs0 debug_regs0 pc_reg0) seg_regs_limits0))))

(define flags_reg (lambda (c)
  (match c
     ((Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
       control_regs0 debug_regs0 pc_reg0) flags_reg0))))

(define control_regs (lambda (c)
  (match c
     ((Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
       control_regs0 debug_regs0 pc_reg0) control_regs0))))

(define debug_regs (lambda (c)
  (match c
     ((Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
       control_regs0 debug_regs0 pc_reg0) debug_regs0))))

(define pc_reg (lambda (c)
  (match c
     ((Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
       control_regs0 debug_regs0 pc_reg0) pc_reg0))))

(define fpu_state_rect (lambdas (f f0)
  (match f0
     ((Build_fpu_state x x0 x1 x2 x3 x4 x5) (@ f x x0 x1 x2 x3 x4 x5)))))

(define fpu_state_rec (lambdas (f f0)
  (match f0
     ((Build_fpu_state x x0 x1 x2 x3 x4 x5) (@ f x x0 x1 x2 x3 x4 x5)))))

(define fpu_data_regs (lambda (f)
  (match f
     ((Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
       fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0) fpu_data_regs0))))

(define fpu_status (lambda (f)
  (match f
     ((Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
       fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0) fpu_status0))))

(define fpu_control (lambda (f)
  (match f
     ((Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
       fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0) fpu_control0))))

(define fpu_tags (lambda (f)
  (match f
     ((Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
       fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0) fpu_tags0))))

(define fpu_lastInstrPtr (lambda (f)
  (match f
     ((Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
       fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0) fpu_lastInstrPtr0))))

(define fpu_lastDataPtr (lambda (f)
  (match f
     ((Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
       fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0) fpu_lastDataPtr0))))

(define fpu_lastOpcode (lambda (f)
  (match f
     ((Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
       fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0) fpu_lastOpcode0))))

(define mach_rect (lambdas (f m)
  (match m
     ((Build_mach x x0) (@ f x x0)))))

(define mach_rec (lambdas (f m)
  (match m
     ((Build_mach x x0) (@ f x x0)))))

(define core (lambda (m)
  (match m
     ((Build_mach core0 fpu0) core0))))

(define fpu (lambda (m)
  (match m
     ((Build_mach core0 fpu0) fpu0))))

(define get_bits_rng (lambdas (s i n m)
  (@ repr (@ minus m n) (@ unsigned s (@ shru s i (@ repr s (of_nat1 n)))))))

(define set_bits_rng (lambdas (s i n m v)
  (let ((highbits
    (@ unsigned s
      (@ shru s i (@ repr s (@ add1 (of_nat1 m) `(Zpos ,`(XH))))))))
    (let ((lowbits (@ modulo0 (@ unsigned s i) (two_power_nat n))))
      (@ repr s
        (@ add1
          (@ add1 lowbits
            (@ mul1 (@ unsigned (@ minus m n) v) (two_power_nat n)))
          (@ mul1 highbits (two_power_nat (@ plus m `(S ,`(O)))))))))))

(define get_bit (lambdas (s i n)
  (let ((wordsize0 `(S ,s)))
    (match (@ bits_of_Z wordsize0 (@ unsigned s i) n)
       ((True) (one1 `(O)))
       ((False) (zero1 `(O)))))))

(define set_bit (lambdas (s i n v)
  (@ set_bits_rng s i n n (@ bool_to_int (@ minus n n) v))))

(define get_fpu_flag_reg (lambdas (f fs)
  (match f
     ((F_Busy)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XI
         ,`(XI ,`(XI ,`(XH)))))))
     ((F_C3)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XO
         ,`(XI ,`(XI ,`(XH)))))))
     ((F_C2)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XO
         ,`(XI ,`(XO ,`(XH)))))))
     ((F_C1)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XI
         ,`(XO ,`(XO ,`(XH)))))))
     ((F_C0)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XO
         ,`(XO ,`(XO ,`(XH)))))))
     ((F_ES)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XI
         ,`(XI ,`(XH))))))
     ((F_SF)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XO
         ,`(XI ,`(XH))))))
     ((F_PE)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XI
         ,`(XO ,`(XH))))))
     ((F_UE)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XO
         ,`(XO ,`(XH))))))
     ((F_OE)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XI
         ,`(XH)))))
     ((F_ZE)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XO
         ,`(XH)))))
     ((F_DE)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Zpos ,`(XH))))
     ((F_IE)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(Z0))))))

(define get_stktop_reg (lambda (fs)
  (@ get_bits_rng `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status fs) `(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))) `(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))))

(define get_fpu_ctrl_flag_reg (lambdas (f fs)
  (match f
     ((F_Res15)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XI
         ,`(XI ,`(XI ,`(XH)))))))
     ((F_Res14)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XO
         ,`(XI ,`(XI ,`(XH)))))))
     ((F_Res13)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XI
         ,`(XO ,`(XI ,`(XH)))))))
     ((F_Res7)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XI
         ,`(XI ,`(XH))))))
     ((F_Res6)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XO
         ,`(XI ,`(XH))))))
     ((F_IC)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XO
         ,`(XO ,`(XI ,`(XH)))))))
     ((F_PM)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XI
         ,`(XO ,`(XH))))))
     ((F_UM)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XO
         ,`(XO ,`(XH))))))
     ((F_OM)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XI
         ,`(XH)))))
     ((F_ZM)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XO
         ,`(XH)))))
     ((F_DM)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Zpos ,`(XH))))
     ((F_IM)
       (@ get_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(Z0))))))

(define get_rctrl_reg (lambda (fs)
  (@ get_bits_rng `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))) `(S ,`(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))

(define get_pctrl_reg (lambda (fs)
  (@ get_bits_rng `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control fs) `(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(S ,`(O))))))))) `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
    ,`(S ,`(O)))))))))))))

(define get_location (lambdas (s l m)
  (match l
     ((Reg_loc r) (@ look (gp_regs (core m)) r))
     ((Seg_reg_start_loc r) (@ look (seg_regs_starts (core m)) r))
     ((Seg_reg_limit_loc r) (@ look (seg_regs_limits (core m)) r))
     ((Flag_loc f) (@ look (flags_reg (core m)) f))
     ((Control_register_loc r) (@ look (control_regs (core m)) r))
     ((Debug_register_loc r) (@ look (debug_regs (core m)) r))
     ((Pc_loc) (pc_reg (core m)))
     ((Fpu_stktop_loc) (get_stktop_reg (fpu m)))
     ((Fpu_flag_loc f) (@ get_fpu_flag_reg f (fpu m)))
     ((Fpu_rctrl_loc) (get_rctrl_reg (fpu m)))
     ((Fpu_pctrl_loc) (get_rctrl_reg (fpu m)))
     ((Fpu_ctrl_flag_loc f) (@ get_fpu_ctrl_flag_reg f (fpu m)))
     ((Fpu_lastInstrPtr_loc) (fpu_lastInstrPtr (fpu m)))
     ((Fpu_lastDataPtr_loc) (fpu_lastDataPtr (fpu m)))
     ((Fpu_lastOpcode_loc) (fpu_lastOpcode (fpu m))))))

(define set_gp_reg (lambdas (r v m) `(Build_mach ,`(Build_core_state
  ,(@ upd register_eq_dec (gp_regs (core m)) r v) ,(seg_regs_starts (core m))
  ,(seg_regs_limits (core m)) ,(flags_reg (core m)) ,(control_regs (core m))
  ,(debug_regs (core m)) ,(pc_reg (core m))) ,(fpu m))))

(define set_seg_reg_start (lambdas (r v m) `(Build_mach ,`(Build_core_state
  ,(gp_regs (core m))
  ,(@ upd segment_register_eq_dec (seg_regs_starts (core m)) r v)
  ,(seg_regs_limits (core m)) ,(flags_reg (core m)) ,(control_regs (core m))
  ,(debug_regs (core m)) ,(pc_reg (core m))) ,(fpu m))))

(define set_seg_reg_limit (lambdas (r v m) `(Build_mach ,`(Build_core_state
  ,(gp_regs (core m)) ,(seg_regs_starts (core m))
  ,(@ upd segment_register_eq_dec (seg_regs_limits (core m)) r v)
  ,(flags_reg (core m)) ,(control_regs (core m)) ,(debug_regs (core m))
  ,(pc_reg (core m))) ,(fpu m))))

(define set_flags_reg (lambdas (r v m) `(Build_mach ,`(Build_core_state
  ,(gp_regs (core m)) ,(seg_regs_starts (core m)) ,(seg_regs_limits (core m))
  ,(@ upd flag_eq_dec (flags_reg (core m)) r v) ,(control_regs (core m))
  ,(debug_regs (core m)) ,(pc_reg (core m))) ,(fpu m))))

(define set_control_reg (lambdas (r v m) `(Build_mach ,`(Build_core_state
  ,(gp_regs (core m)) ,(seg_regs_starts (core m)) ,(seg_regs_limits (core m))
  ,(flags_reg (core m))
  ,(@ upd control_register_eq_dec (control_regs (core m)) r v)
  ,(debug_regs (core m)) ,(pc_reg (core m))) ,(fpu m))))

(define set_debug_reg (lambdas (r v m) `(Build_mach ,`(Build_core_state
  ,(gp_regs (core m)) ,(seg_regs_starts (core m)) ,(seg_regs_limits (core m))
  ,(flags_reg (core m)) ,(control_regs (core m))
  ,(@ upd debug_register_eq_dec (debug_regs (core m)) r v)
  ,(pc_reg (core m))) ,(fpu m))))

(define set_pc (lambdas (v m) `(Build_mach ,`(Build_core_state
  ,(gp_regs (core m)) ,(seg_regs_starts (core m)) ,(seg_regs_limits (core m))
  ,(flags_reg (core m)) ,(control_regs (core m)) ,(debug_regs (core m)) ,v)
  ,(fpu m))))

(define set_fpu_stktop_reg (lambdas (v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(fpu_data_regs (fpu m))
  ,(@ set_bits_rng `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
     ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_status (fpu m)) `(S ,`(S ,`(S
     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))) `(S ,`(S ,`(S
     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))) v)
  ,(fpu_control (fpu m)) ,(fpu_tags (fpu m)) ,(fpu_lastInstrPtr (fpu m))
  ,(fpu_lastDataPtr (fpu m)) ,(fpu_lastOpcode (fpu m))))))

(define set_fpu_flags_reg (lambdas (f v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(fpu_data_regs (fpu m))
  ,(let ((old_status (fpu_status (fpu m))))
     (let ((b (negb (@ eq `(O) v (zero1 `(O))))))
       (match f
          ((F_Busy)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(O)))))))))))))))) b))
          ((F_C3)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(O))))))))))))))) b))
          ((F_C2)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))) b))
          ((F_C1)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))) b))
          ((F_C0)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))) b))
          ((F_ES)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))) b))
          ((F_SF)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O))))))) b))
          ((F_PE)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(S ,`(S ,`(O)))))) b))
          ((F_UE)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(S ,`(O))))) b))
          ((F_OE)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(S ,`(O)))) b))
          ((F_ZE)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(S
              ,`(O))) b))
          ((F_DE)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(S ,`(O))
              b))
          ((F_IE)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_status `(O) b)))))
  ,(fpu_control (fpu m)) ,(fpu_tags (fpu m)) ,(fpu_lastInstrPtr (fpu m))
  ,(fpu_lastDataPtr (fpu m)) ,(fpu_lastOpcode (fpu m))))))

(define set_fpu_rctrl_reg (lambdas (v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(fpu_data_regs (fpu m)) ,(fpu_status (fpu m))
  ,(@ set_bits_rng `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
     ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control (fpu m)) `(S ,`(S ,`(S
     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))) `(S ,`(S ,`(S ,`(S
     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))) v)
  ,(fpu_tags (fpu m)) ,(fpu_lastInstrPtr (fpu m)) ,(fpu_lastDataPtr (fpu m))
  ,(fpu_lastOpcode (fpu m))))))

(define set_fpu_pctrl_reg (lambdas (v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(fpu_data_regs (fpu m)) ,(fpu_status (fpu m))
  ,(@ set_bits_rng `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
     ,`(S ,`(S ,`(S ,`(O)))))))))))))))) (fpu_control (fpu m)) `(S ,`(S ,`(S
     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))) `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
     ,`(S ,`(S ,`(O)))))))))) v) ,(fpu_tags (fpu m))
  ,(fpu_lastInstrPtr (fpu m)) ,(fpu_lastDataPtr (fpu m))
  ,(fpu_lastOpcode (fpu m))))))

(define set_fpu_ctrl_reg (lambdas (f v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(fpu_data_regs (fpu m)) ,(fpu_status (fpu m))
  ,(let ((old_ctrl (fpu_control (fpu m))))
     (let ((b (negb (@ eq `(O) v (zero1 `(O))))))
       (match f
          ((F_Res15)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(O)))))))))))))))) b))
          ((F_Res14)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(O))))))))))))))) b))
          ((F_Res13)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(O)))))))))))))) b))
          ((F_Res7)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))) b))
          ((F_Res6)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(O))))))) b))
          ((F_IC)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))
              b))
          ((F_PM)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S ,`(S
              ,`(S ,`(S ,`(O)))))) b))
          ((F_UM)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S ,`(S
              ,`(S ,`(O))))) b))
          ((F_OM)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S ,`(S
              ,`(O)))) b))
          ((F_ZM)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(S
              ,`(O))) b))
          ((F_DM)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(S ,`(O)) b))
          ((F_IM)
            (@ set_bit `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
              ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))) old_ctrl `(O) b)))))
  ,(fpu_tags (fpu m)) ,(fpu_lastInstrPtr (fpu m)) ,(fpu_lastDataPtr (fpu m))
  ,(fpu_lastOpcode (fpu m))))))

(define set_fpu_lastInstrPtr_reg (lambdas (v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(fpu_data_regs (fpu m)) ,(fpu_status (fpu m))
  ,(fpu_control (fpu m)) ,(fpu_tags (fpu m)) ,v ,(fpu_lastDataPtr (fpu m))
  ,(fpu_lastOpcode (fpu m))))))

(define set_fpu_lastDataPtr_reg (lambdas (v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(fpu_data_regs (fpu m)) ,(fpu_status (fpu m))
  ,(fpu_control (fpu m)) ,(fpu_tags (fpu m)) ,(fpu_lastInstrPtr (fpu m)) ,v
  ,(fpu_lastOpcode (fpu m))))))

(define set_lastOpcode_reg (lambdas (v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(fpu_data_regs (fpu m)) ,(fpu_status (fpu m))
  ,(fpu_control (fpu m)) ,(fpu_tags (fpu m)) ,(fpu_lastInstrPtr (fpu m))
  ,(fpu_lastDataPtr (fpu m)) ,v))))

(define set_location (lambdas (s l v m)
  (match l
     ((Reg_loc r) (@ set_gp_reg r v m))
     ((Seg_reg_start_loc r) (@ set_seg_reg_start r v m))
     ((Seg_reg_limit_loc r) (@ set_seg_reg_limit r v m))
     ((Flag_loc f) (@ set_flags_reg f v m))
     ((Control_register_loc r) (@ set_control_reg r v m))
     ((Debug_register_loc r) (@ set_debug_reg r v m))
     ((Pc_loc) (@ set_pc v m))
     ((Fpu_stktop_loc) (@ set_fpu_stktop_reg v m))
     ((Fpu_flag_loc f) (@ set_fpu_flags_reg f v m))
     ((Fpu_rctrl_loc) (@ set_fpu_rctrl_reg v m))
     ((Fpu_pctrl_loc) (@ set_fpu_pctrl_reg v m))
     ((Fpu_ctrl_flag_loc f) (@ set_fpu_ctrl_reg f v m))
     ((Fpu_lastInstrPtr_loc) (@ set_fpu_lastInstrPtr_reg v m))
     ((Fpu_lastDataPtr_loc) (@ set_fpu_lastDataPtr_reg v m))
     ((Fpu_lastOpcode_loc) (@ set_lastOpcode_reg v m)))))

(define array_sub (lambdas (l s a i m)
  (match a
     ((Fpu_datareg) (@ look (fpu_data_regs (fpu m)) i))
     ((Fpu_tag) (@ look (fpu_tags (fpu m)) i)))))

(define set_fpu_datareg (lambdas (r v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(@ upd (eq_dec2 size3) (fpu_data_regs (fpu m)) r v)
  ,(fpu_status (fpu m)) ,(fpu_control (fpu m)) ,(fpu_tags (fpu m))
  ,(fpu_lastInstrPtr (fpu m)) ,(fpu_lastDataPtr (fpu m))
  ,(fpu_lastOpcode (fpu m))))))

(define set_fpu_tags_reg (lambdas (r v m) `(Build_mach ,(core m)
  ,`(Build_fpu_state ,(fpu_data_regs (fpu m)) ,(fpu_status (fpu m))
  ,(fpu_control (fpu m)) ,(@ upd (eq_dec2 size3) (fpu_tags (fpu m)) r v)
  ,(fpu_lastInstrPtr (fpu m)) ,(fpu_lastDataPtr (fpu m))
  ,(fpu_lastOpcode (fpu m))))))

(define array_upd (lambdas (l s a i v m)
  (match a
     ((Fpu_datareg) (@ set_fpu_datareg i v m))
     ((Fpu_tag) (@ set_fpu_tags_reg i v m)))))

(define index0 (lambda (i) (index (@ unsigned size_addr i))))

(define eq3 (eq_dec2 size_addr))

(define elt_eq1 eq3)

(define eq4 (lambdas (x a b) (@ eq1 x a b)))

(define init0 (lambda (x) (init x)))

(define get1 (lambdas (i m) (@ get0 (index0 i) m)))

(define set1 (lambdas (i v m) (@ set0 (index0 i) v m)))

(define map2 (lambdas (f m) (@ map1 f m)))

(define bit_vector_op_rect (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
  f12 f13 b)
  (match b
     ((Add_op) f)
     ((Sub_op) f0)
     ((Mul_op) f1)
     ((Divs_op) f2)
     ((Divu_op) f3)
     ((Modu_op) f4)
     ((Mods_op) f5)
     ((And_op) f6)
     ((Or_op) f7)
     ((Xor_op) f8)
     ((Shl_op) f9)
     ((Shr_op) f10)
     ((Shru_op) f11)
     ((Ror_op) f12)
     ((Rol_op) f13))))

(define bit_vector_op_rec (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
  f12 f13 b)
  (match b
     ((Add_op) f)
     ((Sub_op) f0)
     ((Mul_op) f1)
     ((Divs_op) f2)
     ((Divu_op) f3)
     ((Modu_op) f4)
     ((Mods_op) f5)
     ((And_op) f6)
     ((Or_op) f7)
     ((Xor_op) f8)
     ((Shl_op) f9)
     ((Shr_op) f10)
     ((Shru_op) f11)
     ((Ror_op) f12)
     ((Rol_op) f13))))

(define float_arith_op_rect (lambdas (f f0 f1 f2 f3)
  (match f3
     ((Fadd_op) f)
     ((Fsub_op) f0)
     ((Fmul_op) f1)
     ((Fdiv_op) f2))))

(define float_arith_op_rec (lambdas (f f0 f1 f2 f3)
  (match f3
     ((Fadd_op) f)
     ((Fsub_op) f0)
     ((Fmul_op) f1)
     ((Fdiv_op) f2))))

(define test_op_rect (lambdas (f f0 f1 t)
  (match t
     ((Eq_op) f)
     ((Lt_op) f0)
     ((Ltu_op) f1))))

(define test_op_rec (lambdas (f f0 f1 t)
  (match t
     ((Eq_op) f)
     ((Lt_op) f0)
     ((Ltu_op) f1))))

(define rtl_exp_rect (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 n r)
  (match r
     ((Arith_rtl_exp s b e1 e2)
       (@ f s b e1 (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e1)
         e2 (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e2)))
     ((Test_rtl_exp s top e1 e2)
       (@ f0 s top e1
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e1) e2
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e2)))
     ((If_rtl_exp s cond e1 e2)
       (@ f1 s cond
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size1 cond) e1
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e1) e2
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e2)))
     ((Cast_s_rtl_exp s1 s2 e)
       (@ f2 s1 s2 e
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s1 e)))
     ((Cast_u_rtl_exp s1 s2 e)
       (@ f3 s1 s2 e
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s1 e)))
     ((Imm_rtl_exp s i) (@ f4 s i))
     ((Get_loc_rtl_exp s l) (@ f5 s l))
     ((Get_array_rtl_exp l s a r0)
       (@ f6 l s a r0
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 l r0)))
     ((Get_byte_rtl_exp addr)
       (@ f7 addr
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size_addr addr)))
     ((Get_random_rtl_exp s) (f8 s))
     ((Farith_rtl_exp ew mw fop rounding x x0)
       (let ((len (@ plus (to_nat ew) (to_nat mw))))
         (@ f9 ew mw __ fop rounding
           (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size2
             rounding) x
           (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 len x) x0
           (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 len x0))))
     ((Fcast_rtl_exp ew1 mw1 ew2 mw2 rounding r0)
       (@ f10 ew1 mw1 ew2 mw2 __ __ rounding
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size2 rounding)
         r0
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
           (@ plus (to_nat ew1) (to_nat mw1)) r0))))))
  
(define rtl_exp_rec (lambdas (f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 n r)
  (match r
     ((Arith_rtl_exp s b e1 e2)
       (@ f s b e1 (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e1)
         e2 (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e2)))
     ((Test_rtl_exp s top e1 e2)
       (@ f0 s top e1
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e1) e2
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e2)))
     ((If_rtl_exp s cond e1 e2)
       (@ f1 s cond
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size1 cond) e1
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e1) e2
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e2)))
     ((Cast_s_rtl_exp s1 s2 e)
       (@ f2 s1 s2 e
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s1 e)))
     ((Cast_u_rtl_exp s1 s2 e)
       (@ f3 s1 s2 e
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s1 e)))
     ((Imm_rtl_exp s i) (@ f4 s i))
     ((Get_loc_rtl_exp s l) (@ f5 s l))
     ((Get_array_rtl_exp l s a r0)
       (@ f6 l s a r0
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 l r0)))
     ((Get_byte_rtl_exp addr)
       (@ f7 addr
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size_addr addr)))
     ((Get_random_rtl_exp s) (f8 s))
     ((Farith_rtl_exp ew mw fop rounding x x0)
       (let ((len (@ plus (to_nat ew) (to_nat mw))))
         (@ f9 ew mw __ fop rounding
           (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size2 rounding)
           x (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 len x) x0
           (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 len x0))))
     ((Fcast_rtl_exp ew1 mw1 ew2 mw2 rounding r0)
       (@ f10 ew1 mw1 ew2 mw2 __ __ rounding
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size2 rounding)
         r0
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
           (@ plus (to_nat ew1) (to_nat mw1)) r0))))))
  
(define rtl_instr_rect (lambdas (f f0 f1 f2 f3 f4 f5 r)
  (match r
     ((Set_loc_rtl s e l) (@ f s e l))
     ((Set_array_rtl l s a r0 r1) (@ f0 l s a r0 r1))
     ((Set_byte_rtl e addr) (@ f1 e addr))
     ((Advance_oracle_rtl) f2)
     ((If_rtl r0 r1) (@ f3 r0 r1 (@ rtl_instr_rect f f0 f1 f2 f3 f4 f5 r1)))
     ((Error_rtl) f4)
     ((Trap_rtl) f5))))
  
(define rtl_instr_rec (lambdas (f f0 f1 f2 f3 f4 f5 r)
  (match r
     ((Set_loc_rtl s e l) (@ f s e l))
     ((Set_array_rtl l s a r0 r1) (@ f0 l s a r0 r1))
     ((Set_byte_rtl e addr) (@ f1 e addr))
     ((Advance_oracle_rtl) f2)
     ((If_rtl r0 r1) (@ f3 r0 r1 (@ rtl_instr_rec f f0 f1 f2 f3 f4 f5 r1)))
     ((Error_rtl) f4)
     ((Trap_rtl) f5))))
  
(define oracle_rect (lambdas (f o)
  (match o
     ((Build_oracle x x0) (@ f x x0)))))

(define oracle_rec (lambdas (f o)
  (match o
     ((Build_oracle x x0) (@ f x x0)))))

(define oracle_bits (lambda (o)
  (match o
     ((Build_oracle oracle_bits0 oracle_offset0) oracle_bits0))))

(define oracle_offset (lambda (o)
  (match o
     ((Build_oracle oracle_bits0 oracle_offset0) oracle_offset0))))

(define rtl_state_rect (lambdas (f r)
  (match r
     ((Build_rtl_state x x0 x1) (@ f x x0 x1)))))

(define rtl_state_rec (lambdas (f r)
  (match r
     ((Build_rtl_state x x0 x1) (@ f x x0 x1)))))

(define rtl_oracle (lambda (r)
  (match r
     ((Build_rtl_state rtl_oracle0 rtl_mach_state0 rtl_memory0) rtl_oracle0))))

(define rtl_mach_state (lambda (r)
  (match r
     ((Build_rtl_state rtl_oracle0 rtl_mach_state0 rtl_memory0)
       rtl_mach_state0))))

(define rtl_memory (lambda (r)
  (match r
     ((Build_rtl_state rtl_oracle0 rtl_mach_state0 rtl_memory0) rtl_memory0))))

(define rTL_ans_rect (lambdas (f f0 f1 r)
  (match r
     ((Fail_ans) f)
     ((Trap_ans) f0)
     ((Okay_ans x) (f1 x)))))

(define rTL_ans_rec (lambdas (f f0 f1 r)
  (match r
     ((Fail_ans) f)
     ((Trap_ans) f0)
     ((Okay_ans x) (f1 x)))))

(define rTL_monad `(Build_Monad ,(lambdas (_ x rs) `(Pair ,`(Okay_ans ,x)
  ,rs)) ,(lambdas (_ _ c f rs)
  (match (c rs)
     ((Pair r rs~)
       (match r
          ((Fail_ans) `(Pair ,`(Fail_ans) ,rs~))
          ((Trap_ans) `(Pair ,`(Trap_ans) ,rs~))
          ((Okay_ans v) (@ f v rs~))))))))

(define fail (lambda (rs) `(Pair ,`(Fail_ans) ,rs)))

(define trap (lambda (rs) `(Pair ,`(Trap_ans) ,rs)))

(define set_loc (lambdas (s l v rs) `(Pair ,`(Okay_ans ,`(Tt))
  ,`(Build_rtl_state ,(rtl_oracle rs)
  ,(@ set_location s l v (rtl_mach_state rs)) ,(rtl_memory rs)))))

(define set_array (lambdas (l s a i v rs) `(Pair ,`(Okay_ans ,`(Tt))
  ,`(Build_rtl_state ,(rtl_oracle rs)
  ,(@ array_upd l s a i v (rtl_mach_state rs)) ,(rtl_memory rs)))))

(define set_byte (lambdas (addr v rs) `(Pair ,`(Okay_ans ,`(Tt))
  ,`(Build_rtl_state ,(rtl_oracle rs) ,(rtl_mach_state rs)
  ,(@ set1 addr v (rtl_memory rs))))))

(define advance_oracle (lambda (rs)
  (let ((o (rtl_oracle rs)))
    (let ((o~ `(Build_oracle ,(oracle_bits o)
      ,(@ add1 (oracle_offset o) `(Zpos ,`(XH))))))
      `(Pair ,`(Okay_ans ,`(Tt)) ,`(Build_rtl_state ,o~ ,(rtl_mach_state rs)
      ,(rtl_memory rs)))))))

(define interp_arith (lambdas (s b v1 v2)
  (match b
     ((Add_op) (@ add2 s v1 v2))
     ((Sub_op) (@ sub2 s v1 v2))
     ((Mul_op) (@ mul2 s v1 v2))
     ((Divs_op) (@ divs s v1 v2))
     ((Divu_op) (@ divu s v1 v2))
     ((Modu_op) (@ modu s v1 v2))
     ((Mods_op) (@ mods s v1 v2))
     ((And_op) (@ and s v1 v2))
     ((Or_op) (@ or s v1 v2))
     ((Xor_op) (@ xor s v1 v2))
     ((Shl_op) (@ shl s v1 v2))
     ((Shr_op) (@ shr s v1 v2))
     ((Shru_op) (@ shru s v1 v2))
     ((Ror_op) (@ ror s v1 v2))
     ((Rol_op) (@ rol s v1 v2)))))

(define interp_test (lambdas (s t v1 v2)
  (match (match t
            ((Eq_op) (@ eq s v1 v2))
            ((Lt_op) (@ lt s v1 v2))
            ((Ltu_op) (@ ltu s v1 v2)))
     ((True) (one1 size1))
     ((False) (zero1 size1)))))

(define dec_rounding_mode (lambda (rm)
  (match (@ eq size2 rm (@ repr size2 `(Z0)))
     ((True) `(Mode_NE))
     ((False)
       (match (@ eq size2 rm (@ repr size2 `(Zpos ,`(XH))))
          ((True) `(Mode_DN))
          ((False)
            (match (@ eq size2 rm (@ repr size2 `(Zpos ,`(XO ,`(XH)))))
               ((True) `(Mode_UP))
               ((False) `(Mode_ZR)))))))))

(define interp_farith (lambdas (ew mw fop rm v1 v2)
  (let ((prec (@ add1 `(Zpos ,mw) `(Zpos ,`(XH)))))
    (let ((emax
      (@ pow1 `(Zpos ,`(XO ,`(XH))) (@ sub1 `(Zpos ,ew) `(Zpos ,`(XH))))))
      (let ((bf_of_bits (@ binary_float_of_bits `(Zpos ,mw) `(Zpos ,ew))))
        (let ((bf1
          (bf_of_bits (@ unsigned (@ plus (to_nat ew) (to_nat mw)) v1))))
          (let ((bf2
            (bf_of_bits (@ unsigned (@ plus (to_nat ew) (to_nat mw)) v2))))
            (let ((md (dec_rounding_mode rm)))
              (let ((res
                (match fop
                   ((Fadd_op) (@ bplus prec emax md bf1 bf2))
                   ((Fsub_op) (@ bminus prec emax md bf1 bf2))
                   ((Fmul_op) (@ bmult prec emax md bf1 bf2))
                   ((Fdiv_op) (@ bdiv prec emax md bf1 bf2)))))
                (@ repr (@ plus (to_nat ew) (to_nat mw))
                  (@ bits_of_binary_float `(Zpos ,mw) `(Zpos ,ew) res)))))))))))

(define cond_Zopp0 (lambdas (b m)
  (match b
     ((True) (opp m))
     ((False) m))))

(define binary_float_cast (lambdas (prec1 emax1 prec2 emax2 rm bf)
  (let ((md (dec_rounding_mode rm)))
    (match bf
       ((B754_zero sign) `(B754_zero ,sign))
       ((B754_infinity sign) `(B754_infinity ,sign))
       ((B754_nan) `(B754_nan))
       ((B754_finite sign mant ep)
         (@ binary_normalize prec2 emax2 md (@ cond_Zopp0 sign `(Zpos ,mant))
           ep `(True)))))))

(define interp_fcast (lambdas (ew1 mw1 ew2 mw2 rm v)
  (let ((bf_of_bits (@ binary_float_of_bits `(Zpos ,mw1) `(Zpos ,ew1))))
    (let ((bf
      (bf_of_bits (@ unsigned (@ plus (to_nat ew1) (to_nat mw1)) v))))
      (let ((bf~
        (@ binary_float_cast (@ add1 `(Zpos ,mw1) `(Zpos ,`(XH)))
          (@ pow1 `(Zpos ,`(XO ,`(XH))) (@ sub1 `(Zpos ,ew1) `(Zpos ,`(XH))))
          (@ add1 `(Zpos ,mw2) `(Zpos ,`(XH)))
          (@ pow1 `(Zpos ,`(XO ,`(XH))) (@ sub1 `(Zpos ,ew2) `(Zpos ,`(XH))))
          rm bf)))
        (@ repr (@ plus (to_nat ew2) (to_nat mw2))
          (@ bits_of_binary_float `(Zpos ,mw2) `(Zpos ,ew2) bf~)))))))

(define interp_rtl_exp (lambdas (s e rs)
  (match e
     ((Arith_rtl_exp s0 b e1 e2)
       (let ((v1 (@ interp_rtl_exp s0 e1 rs)))
         (let ((v2 (@ interp_rtl_exp s0 e2 rs))) (@ interp_arith s0 b v1 v2))))
     ((Test_rtl_exp s0 t e1 e2)
       (let ((v1 (@ interp_rtl_exp s0 e1 rs)))
         (let ((v2 (@ interp_rtl_exp s0 e2 rs))) (@ interp_test s0 t v1 v2))))
     ((If_rtl_exp s0 cd e1 e2)
       (let ((v (@ interp_rtl_exp size1 cd rs)))
         (match (@ eq size1 v (one1 size1))
            ((True) (@ interp_rtl_exp s0 e1 rs))
            ((False) (@ interp_rtl_exp s0 e2 rs)))))
     ((Cast_s_rtl_exp s1 s2 e0)
       (let ((v (@ interp_rtl_exp s1 e0 rs))) (@ repr s2 (@ signed s1 v))))
     ((Cast_u_rtl_exp s1 s2 e0)
       (let ((v (@ interp_rtl_exp s1 e0 rs))) (@ repr s2 (@ unsigned s1 v))))
     ((Imm_rtl_exp s0 v) v)
     ((Get_loc_rtl_exp s0 l) (@ get_location s0 l (rtl_mach_state rs)))
     ((Get_array_rtl_exp l s0 a e0)
       (let ((i (@ interp_rtl_exp l e0 rs)))
         (@ array_sub l s0 a i (rtl_mach_state rs))))
     ((Get_byte_rtl_exp addr)
       (let ((v (@ interp_rtl_exp size_addr addr rs)))
         (@ get1 v (rtl_memory rs))))
     ((Get_random_rtl_exp s0)
       (let ((oracle (rtl_oracle rs)))
         (@ oracle_bits oracle s0 (oracle_offset oracle))))
     ((Farith_rtl_exp ew mw fop rm x x0)
       (let ((len (@ plus (to_nat ew) (to_nat mw))))
         (let ((v1 (@ interp_rtl_exp len x rs)))
           (let ((v2 (@ interp_rtl_exp len x0 rs)))
             (let ((vrm (@ interp_rtl_exp size2 rm rs)))
               (@ interp_farith ew mw fop vrm v1 v2))))))
     ((Fcast_rtl_exp ew1 mw1 ew2 mw2 rm e0)
       (let ((v (@ interp_rtl_exp (@ plus (to_nat ew1) (to_nat mw1)) e0 rs)))
         (let ((vrm (@ interp_rtl_exp size2 rm rs)))
           (@ interp_fcast ew1 mw1 ew2 mw2 vrm v)))))))
  
(define interp_rtl_exp_comp (lambdas (s e rs) `(Pair ,`(Okay_ans
  ,(@ interp_rtl_exp s e rs)) ,rs)))

(define get_loc (lambdas (s l)
  (@ interp_rtl_exp_comp s `(Get_loc_rtl_exp ,s ,l))))

(define get_array (lambdas (l s a i)
  (@ interp_rtl_exp_comp s `(Get_array_rtl_exp ,l ,s ,a ,`(Imm_rtl_exp ,l
    ,i)))))

(define get_byte (lambda (addr)
  (@ interp_rtl_exp_comp size8 `(Get_byte_rtl_exp ,`(Imm_rtl_exp ,size_addr
    ,addr)))))

(define get_random (lambda (s)
  (@ interp_rtl_exp_comp s `(Get_random_rtl_exp ,s))))

(define interp_rtl (lambda (instr)
  (match instr
     ((Set_loc_rtl s e l)
       (@ bind rTL_monad (@ interp_rtl_exp_comp s e) (lambda (v)
         (@ set_loc s l v))))
     ((Set_array_rtl l s a e1 e2)
       (@ bind rTL_monad (@ interp_rtl_exp_comp l e1) (lambda (i)
         (@ bind rTL_monad (@ interp_rtl_exp_comp s e2) (lambda (v)
           (@ set_array l s a i v))))))
     ((Set_byte_rtl e addr)
       (@ bind rTL_monad (@ interp_rtl_exp_comp size8 e) (lambda (v)
         (@ bind rTL_monad (@ interp_rtl_exp_comp size_addr addr) (lambda (a)
           (@ set_byte a v))))))
     ((Advance_oracle_rtl) advance_oracle)
     ((If_rtl r i)
       (@ bind rTL_monad (@ interp_rtl_exp_comp size1 r) (lambda (v)
         (match (@ eq size1 v (one1 size1))
            ((True) (interp_rtl i))
            ((False) (@ return rTL_monad `(Tt)))))))
     ((Error_rtl) fail)
     ((Trap_rtl) trap))))
  
(define instruction_rect (lambdas (f i)
  (match i
     ((Build_instruction x x0) (@ f x x0)))))

(define instruction_rec (lambdas (f i)
  (match i
     ((Build_instruction x x0) (@ f x x0)))))

(define instr_assembly (lambda (i)
  (match i
     ((Build_instruction instr_assembly0 instr_rtl0) instr_assembly0))))

(define instr_rtl (lambda (i)
  (match i
     ((Build_instruction instr_assembly0 instr_rtl0) instr_rtl0))))

(define rTL_step_list (lambda (l)
  (match l
     ((Nil) (@ return rTL_monad `(Tt)))
     ((Cons i l~)
       (@ bind rTL_monad (interp_rtl i) (lambda (x) (rTL_step_list l~)))))))
  
(define empty0 (lambda (spaceSearch)
  (match spaceSearch
     ((Build_SpaceSearch empty1 single0 union0 bind1 search0) (empty1 __)))))

(define single (lambdas (spaceSearch x)
  (match spaceSearch
     ((Build_SpaceSearch empty1 single0 union0 bind1 search0)
       (@ single0 __ x)))))

(define union (lambdas (spaceSearch x x0)
  (match spaceSearch
     ((Build_SpaceSearch empty1 single0 union0 bind1 search0)
       (@ union0 __ x x0)))))

(define bind0 (lambdas (spaceSearch x x0)
  (match spaceSearch
     ((Build_SpaceSearch empty1 single0 union0 bind1 search0)
       (@ bind1 __ __ x x0)))))

(define search (lambdas (spaceSearch x)
  (match spaceSearch
     ((Build_SpaceSearch empty1 single0 union0 bind1 search0)
       (@ search0 __ x)))))

(define symbolicFail (lambda  (_) (assert false)))

(define symbolicReturn (lambdas (a _) a))

(define symbolicUnion
  (lambdas (s t v) (define-symbolic* b boolean?) (if b (s v) (t v))))

(define symbolicBind (lambdas (s f v) (@ f (s v) v)))

(define symbolicRun (lambda  (e) (solve/evaluate/concretize e)))

(define rosette `(Build_SpaceSearch ,(lambda (_) symbolicFail) ,(lambda (_)
  symbolicReturn) ,(lambda (_) symbolicUnion) ,(lambdas (_ _) symbolicBind)
  ,(lambda (_) symbolicRun)))

(define bii id)

(define empty_mem `(Pair
  ,(zero1 (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))) ,empty))

(define empty_reg (lambda (reg)
  (zero1
    (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))))))

(define empty_seg (lambda (seg)
  (zero1
    (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))))))

(define pc
  (zero1
    (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(O)))))))))))))))))))))))))))))))))))

(define empty_oracle `(Build_oracle ,(lambdas (a b) (zero1 (bii a))) ,`(Z0)))

(define init_machine `(Build_core_state ,empty_reg ,empty_seg
  ,(lambda (seg_reg)
  (@ repr
    (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(O)))))))))))))))))))))))))))))))))
    (max_unsigned
      (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
        ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))))))
  ,(lambda (f) (zero1 (bii `(O)))) ,(lambda (c)
  (zero1
    (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))))) ,(lambda (d)
  (zero1
    (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))))) ,pc))

(define empty_fpu_machine `(Build_fpu_state ,(lambda (fpr)
  (zero1
    (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ,(zero1
     (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(S ,`(S ,`(O))))))))))))))))))
  ,(zero1
     (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(S ,`(S ,`(O)))))))))))))))))) ,(lambda (t)
  (zero1 (bii `(S ,`(O)))))
  ,(zero1
     (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))
  ,(zero1
     (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
       ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))
  ,(zero1
     (bii `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))

(define init_full_machine `(Build_mach ,init_machine ,empty_fpu_machine))

(define init_rtl_state `(Build_rtl_state ,empty_oracle ,init_full_machine
  ,empty_mem))

(define four `(Zpos ,`(XO ,`(XO ,`(XH)))))

(define six `(Zpos ,`(XO ,`(XI ,`(XH)))))

(define fast_eax_plus (lambda (n) `(Cons ,`(Set_loc_rtl ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(O)))))))))))))))))))))))))))))))) ,`(Cast_u_rtl_exp ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(O)))))))) ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))
  ,`(Arith_rtl_exp ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))) ,`(Add_op)
  ,`(Cast_u_rtl_exp ,size32 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))
  ,`(Get_loc_rtl_exp ,size32 ,`(Reg_loc ,`(EAX)))) ,`(Cast_u_rtl_exp ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(O)))))))))))))))))))))))))))))))) ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(O)))))))) ,`(Imm_rtl_exp ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))
  ,n)))) ,`(Reg_loc ,`(EAX))) ,`(Nil))))

(define add3 (lambdas (n m) (@ app (fast_eax_plus n) (fast_eax_plus m))))

(define run (lambda (p) (@ rTL_step_list p init_rtl_state)))

(define inputs
  (@ union rosette (@ single rosette four) (@ single rosette six)))

(define verification
  (@ search rosette
    (@ bind0 rosette inputs (lambda (n)
      (@ bind0 rosette inputs (lambda (m)
        (let ((s (run (@ add3 n m))))
          (match (fst s)
             ((Fail_ans)
               (@ single rosette `(Pair ,`(Pair ,n ,m) ,`(Inl ,`(Fail_ans)))))
             ((Trap_ans)
               (@ single rosette `(Pair ,`(Pair ,n ,m) ,`(Inl ,`(Trap_ans)))))
             ((Okay_ans u)
               (let ((r (@ gp_regs (core (rtl_mach_state (snd s))) `(EAX))))
                 (match (@ eq `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                          ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))
                          (@ add2 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                            ,`(S ,`(S ,`(O)))))))))))))))))))))))))))))))) n
                            n) r)
                    ((True) (empty0 rosette))
                    ((False)
                      (@ single rosette `(Pair ,`(Pair ,n ,m) ,`(Inr ,r)))))))))))))))

