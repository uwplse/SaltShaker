#lang racket

(require "extraction.rkt")
(require profile)

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
  
(define mult (lambdas (n m)
  (match n
     ((O) `(O))
     ((S p) (@ plus m (@ mult p m))))))
  
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

(define append (lambdas (s1 s2)
  (match s1
     ((EmptyString) s2)
     ((String c s1~) `(String ,c ,(@ append s1~ s2))))))
  
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

(define addrDisp (lambda (a)
  (match a
     ((MkAddress addrDisp0 addrBase0 addrIndex0) addrDisp0))))

(define addrBase (lambda (a)
  (match a
     ((MkAddress addrDisp0 addrBase0 addrIndex0) addrBase0))))

(define addrIndex (lambda (a)
  (match a
     ((MkAddress addrDisp0 addrBase0 addrIndex0) addrIndex0))))

(define seg_override (lambda (p)
  (match p
     ((MkPrefix lock_rep seg_override0 op_override0 addr_override0)
       seg_override0))))

(define op_override (lambda (p)
  (match p
     ((MkPrefix lock_rep seg_override0 op_override0 addr_override0)
       op_override0))))

(define addr_override (lambda (p)
  (match p
     ((MkPrefix lock_rep seg_override0 op_override0 addr_override0)
       addr_override0))))

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
     ((Node l1 o1 r2)
       (match m2
          ((Leaf) (bempty m1))
          ((Node l2 o2 r3)
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
               ((True) (@ beq beqA r2 r3))
               ((False) `(False)))))))))
  
(define append0 (lambdas (i j)
  (match i
     ((XI ii) `(XI ,(@ append0 ii j)))
     ((XO ii) `(XO ,(@ append0 ii j)))
     ((XH) j))))
  
(define xmap (lambdas (f m i)
  (match m
     ((Leaf) `(Leaf))
     ((Node l o r) `(Node ,(@ xmap f l (@ append0 i `(XO ,`(XH))))
       ,(@ option_map (f i) o) ,(@ xmap f r (@ append0 i `(XI ,`(XH)))))))))
  
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
     ((Node l1 o1 r2)
       (match m2
          ((Leaf) (@ xcombine_l f m1))
          ((Node l2 o2 r3)
            (@ node~ (@ combine f l1 l2) (@ f o1 o2) (@ combine f r2 r3))))))))
  
(define xelements (lambdas (m i)
  (match m
     ((Leaf) `(Nil))
     ((Node l o r)
       (match o
          ((Some x)
            (@ app (@ xelements l (@ append0 i `(XO ,`(XH)))) `(Cons ,`(Pair
              ,i ,x) ,(@ xelements r (@ append0 i `(XI ,`(XH)))))))
          ((None)
            (@ app (@ xelements l (@ append0 i `(XO ,`(XH))))
              (@ xelements r (@ append0 i `(XI ,`(XH)))))))))))
  
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
            (let ((v1 (@ xfold f (@ append0 i `(XO ,`(XH))) l v)))
              (let ((v2 (@ f v1 i x)))
                (@ xfold f (@ append0 i `(XI ,`(XH))) r v2))))
          ((None)
            (let ((v1 (@ xfold f (@ append0 i `(XO ,`(XH))) l v)))
              (@ xfold f (@ append0 i `(XI ,`(XH))) r v1))))))))
  
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
     ((Build_Monad return0 bind0) (@ return0 __ x)))))

(define bind (lambdas (monad x x0)
  (match monad
     ((Build_Monad return0 bind0) (@ bind0 __ __ x x0)))))

(define r0 (void))

(define r1 (void))

(define rplus (void))

(define rmult (void))

(define ropp (void))

(define rinv (void))

(define total_order_T (void))

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

(define radix_val (lambda (r) r))

(define cond_Zopp (lambdas (b m)
  (match b
     ((True) (opp m))
     ((False) m))))

(define p2R (lambda (p)
  (match p
     ((XI t)
       (match t
          ((XI p0) (@ rplus r1 (@ rmult (@ rplus r1 r1) (p2R t))))
          ((XO p0) (@ rplus r1 (@ rmult (@ rplus r1 r1) (p2R t))))
          ((XH) (@ rplus r1 (@ rplus r1 r1)))))
     ((XO t)
       (match t
          ((XI p0) (@ rmult (@ rplus r1 r1) (p2R t)))
          ((XO p0) (@ rmult (@ rplus r1 r1) (p2R t)))
          ((XH) (@ rplus r1 r1))))
     ((XH) r1))))
  
(define z2R (lambda (n)
  (match n
     ((Z0) r0)
     ((Zpos p) (p2R p))
     ((Zneg p) (ropp (p2R p))))))

(define rcompare (lambdas (x y)
  (match (@ total_order_T x y)
     ((Inleft s)
       (match s
          ((Left) `(Lt))
          ((Right) `(Eq))))
     ((Inright) `(Gt)))))

(define bpow (lambdas (r e)
  (match e
     ((Z0) r1)
     ((Zpos p) (z2R (@ pow_pos (radix_val r) p)))
     ((Zneg p) (rinv (z2R (@ pow_pos (radix_val r) p)))))))

(define fnum (lambdas (beta f)
  (match f
     ((Float fnum0 fexp0) fnum0))))

(define fexp (lambdas (beta f)
  (match f
     ((Float fnum0 fexp0) fexp0))))

(define f2R (lambdas (beta f)
  (@ rmult (z2R (@ fnum beta f)) (@ bpow beta (@ fexp beta f)))))

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

(define radix2 `(Zpos ,`(XO ,`(XH))))

(define b2R (lambdas (prec emax f)
  (match f
     ((B754_zero b) r0)
     ((B754_infinity b) r0)
     ((B754_nan) r0)
     ((B754_finite s m e)
       (@ f2R radix2 `(Float ,(@ cond_Zopp s `(Zpos ,m)) ,e))))))

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
    (let ((fexp0 (@ fLT_exp emin prec)))
      (lambdas (m e l)
      (@ shr0 (@ shr_record_of_loc m l) e
        (@ sub1 (fexp0 (@ add1 (zdigits2 m) e)) e)))))))

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
    (let ((fexp0 (@ fLT_exp emin prec)))
      (lambdas (mx ex)
      (@ shl_align mx ex
        (fexp0 (@ add1 (of_nat1 `(S ,(digits2_Pnat mx))) ex))))))))

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

(define b32_of_bits
  (@ binary_float_of_bits `(Zpos ,`(XI ,`(XI ,`(XI ,`(XO ,`(XH)))))) `(Zpos
    ,`(XO ,`(XO ,`(XO ,`(XH)))))))

(define bits_of_b32
  (@ bits_of_binary_float `(Zpos ,`(XI ,`(XI ,`(XI ,`(XO ,`(XH)))))) `(Zpos
    ,`(XO ,`(XO ,`(XO ,`(XH)))))))

(define b64_of_bits
  (@ binary_float_of_bits `(Zpos ,`(XO ,`(XO ,`(XI ,`(XO ,`(XI ,`(XH)))))))
    `(Zpos ,`(XI ,`(XI ,`(XO ,`(XH)))))))

(define bits_of_b64
  (@ bits_of_binary_float `(Zpos ,`(XO ,`(XO ,`(XI ,`(XO ,`(XI ,`(XH)))))))
    `(Zpos ,`(XI ,`(XI ,`(XO ,`(XH)))))))

(define size1 `(O))

(define size2 `(S ,`(O)))

(define size3 `(S ,`(S ,`(O))))

(define size4 `(S ,`(S ,`(S ,`(O)))))

(define size8 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))

(define size16 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(O)))))))))))))))))

(define size32 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))))))))))))))))))))

(define size64 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define size79 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define size80 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define b79_of_bits
  (@ binary_float_of_bits `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH)))))))
    `(Zpos ,`(XI ,`(XI ,`(XI ,`(XH)))))))

(define bits_of_b79
  (@ bits_of_binary_float `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH)))))))
    `(Zpos ,`(XI ,`(XI ,`(XI ,`(XH)))))))

(define de_float_of_bits (lambda (x)
  (match (@ split_bits `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
           ,`(XH)))))))) `(Zpos ,`(XI ,`(XI ,`(XI ,`(XH))))) x)
     ((Pair p ex)
       (match p
          ((Pair sx mx)
            (let ((mx~
              (@ modulo0 mx
                (@ pow1 `(Zpos ,`(XO ,`(XH))) `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI
                  ,`(XI ,`(XH)))))))))))
              (b79_of_bits
                (@ join_bits `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI
                  ,`(XH))))))) `(Zpos ,`(XI ,`(XI ,`(XI ,`(XH))))) sx mx~ ex)))))))))

(define bits_of_de_float (lambda (f)
  (let ((x (bits_of_b79 f)))
    (match (@ split_bits `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH)))))))
             `(Zpos ,`(XI ,`(XI ,`(XI ,`(XH))))) x)
       ((Pair p ex)
         (match p
            ((Pair sx mx)
              (match (@ zeq_bool ex `(Z0))
                 ((True)
                   (@ join_bits `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                     ,`(XH)))))))) `(Zpos ,`(XI ,`(XI ,`(XI ,`(XH))))) sx mx
                     ex))
                 ((False)
                   (match (@ zeq_bool ex
                            (@ sub1
                              (@ pow1 `(Zpos ,`(XO ,`(XH))) `(Zpos ,`(XI
                                ,`(XI ,`(XI ,`(XH)))))) `(Zpos ,`(XH))))
                      ((True)
                        (@ join_bits `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                          ,`(XO ,`(XH)))))))) `(Zpos ,`(XI ,`(XI ,`(XI
                          ,`(XH))))) sx mx ex))
                      ((False)
                        (@ join_bits `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                          ,`(XO ,`(XH)))))))) `(Zpos ,`(XI ,`(XI ,`(XI
                          ,`(XH))))) sx
                          (@ add1
                            (@ pow1 `(Zpos ,`(XO ,`(XH))) `(Zpos ,`(XI ,`(XI
                              ,`(XI ,`(XI ,`(XI ,`(XH)))))))) mx) ex))))))))))))

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
     ((Get_array_rtl_exp l s a r2)
       (@ f6 l s a r2
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 l r2)))
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
     ((Fcast_rtl_exp ew1 mw1 ew2 mw2 rounding r2)
       (@ f10 ew1 mw1 ew2 mw2 __ __ rounding
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size2 rounding)
         r2
         (@ rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
           (@ plus (to_nat ew1) (to_nat mw1)) r2))))))
  
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
     ((Get_array_rtl_exp l s a r2)
       (@ f6 l s a r2
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 l r2)))
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
     ((Fcast_rtl_exp ew1 mw1 ew2 mw2 rounding r2)
       (@ f10 ew1 mw1 ew2 mw2 __ __ rounding
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size2 rounding)
         r2
         (@ rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
           (@ plus (to_nat ew1) (to_nat mw1)) r2))))))
  
(define rtl_instr_rect (lambdas (f f0 f1 f2 f3 f4 f5 r)
  (match r
     ((Set_loc_rtl s e l) (@ f s e l))
     ((Set_array_rtl l s a r2 r3) (@ f0 l s a r2 r3))
     ((Set_byte_rtl e addr) (@ f1 e addr))
     ((Advance_oracle_rtl) f2)
     ((If_rtl r2 r3) (@ f3 r2 r3 (@ rtl_instr_rect f f0 f1 f2 f3 f4 f5 r3)))
     ((Error_rtl) f4)
     ((Trap_rtl) f5))))
  
(define rtl_instr_rec (lambdas (f f0 f1 f2 f3 f4 f5 r)
  (match r
     ((Set_loc_rtl s e l) (@ f s e l))
     ((Set_array_rtl l s a r2 r3) (@ f0 l s a r2 r3))
     ((Set_byte_rtl e addr) (@ f1 e addr))
     ((Advance_oracle_rtl) f2)
     ((If_rtl r2 r3) (@ f3 r2 r3 (@ rtl_instr_rec f f0 f1 f2 f3 f4 f5 r3)))
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

(define conv_state_rect (lambdas (f c) (f c)))

(define conv_state_rec (lambdas (f c) (f c)))

(define c_rev_i (lambda (c) c))

(define conv_monad `(Build_Monad ,(lambdas (_ x s) `(Pair ,x ,s))
  ,(lambdas (_ _ c f s)
  (match (c s)
     ((Pair v s~) (@ f v s~))))))

(define runConv (lambda (c)
  (match (c `(Nil))
     ((Pair u c~) (rev (c_rev_i c~))))))

(define eMIT (lambdas (i s) `(Pair ,`(Tt) ,`(Cons ,i ,(c_rev_i s)))))

(define raise_error (eMIT `(Error_rtl)))

(define raise_trap (eMIT `(Trap_rtl)))

(define no_op (@ return conv_monad `(Tt)))

(define load_int (lambdas (s i) (@ return conv_monad `(Imm_rtl_exp ,s ,i))))

(define arith (lambdas (s b e1 e2)
  (@ return conv_monad `(Arith_rtl_exp ,s ,b ,e1 ,e2))))

(define test (lambdas (s t e1 e2)
  (@ return conv_monad `(Test_rtl_exp ,s ,t ,e1 ,e2))))

(define cast_u (lambdas (s1 s2 e)
  (@ return conv_monad `(Cast_u_rtl_exp ,s1 ,s2 ,e))))

(define cast_s (lambdas (s1 s2 e)
  (@ return conv_monad `(Cast_s_rtl_exp ,s1 ,s2 ,e))))

(define read_loc (lambdas (s l)
  (@ return conv_monad `(Get_loc_rtl_exp ,s ,l))))

(define write_loc (lambdas (s e l) (eMIT `(Set_loc_rtl ,s ,e ,l))))

(define read_array (lambdas (l s a idx)
  (@ return conv_monad `(Get_array_rtl_exp ,l ,s ,a ,idx))))

(define write_array (lambdas (l s a idx v)
  (eMIT `(Set_array_rtl ,l ,s ,a ,idx ,v))))

(define read_byte (lambda (a) (@ return conv_monad `(Get_byte_rtl_exp ,a))))

(define write_byte (lambdas (v a) (eMIT `(Set_byte_rtl ,v ,a))))

(define if_exp (lambdas (s g e1 e2)
  (@ return conv_monad `(If_rtl_exp ,s ,g ,e1 ,e2))))

(define if_trap (lambda (g) (eMIT `(If_rtl ,g ,`(Trap_rtl)))))

(define if_set_loc (lambdas (cond s e l)
  (eMIT `(If_rtl ,cond ,`(Set_loc_rtl ,s ,e ,l)))))

(define choose (lambda (s)
  (@ bind conv_monad (eMIT `(Advance_oracle_rtl)) (lambda (x)
    (@ return conv_monad `(Get_random_rtl_exp ,s))))))

(define fcast (lambdas (ew1 mw1 ew2 mw2 rm e)
  (@ return conv_monad `(Fcast_rtl_exp ,ew1 ,mw1 ,ew2 ,mw2 ,rm ,e))))

(define farith_float79 (lambdas (op rm e1 e2)
  (@ return conv_monad `(Farith_rtl_exp ,`(XI ,`(XI ,`(XI ,`(XH)))) ,`(XI
    ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH)))))) ,op ,rm ,e1 ,e2))))

(define load_Z (lambdas (s z) (@ load_int s (@ repr s z))))

(define load_reg (lambda (r) (@ read_loc size32 `(Reg_loc ,r))))

(define set_reg (lambdas (p r) (@ write_loc size32 p `(Reg_loc ,r))))

(define get_seg_start (lambda (s)
  (@ read_loc size32 `(Seg_reg_start_loc ,s))))

(define get_seg_limit (lambda (s)
  (@ read_loc size32 `(Seg_reg_limit_loc ,s))))

(define get_flag (lambda (fl) (@ read_loc size1 `(Flag_loc ,fl))))

(define set_flag (lambdas (fl r) (@ write_loc size1 r `(Flag_loc ,fl))))

(define get_pc (@ read_loc size32 `(Pc_loc)))

(define set_pc0 (lambda (v) (@ write_loc size32 v `(Pc_loc))))

(define not0 (lambdas (s p)
  (@ bind conv_monad (@ load_Z s (max_unsigned s)) (lambda (mask)
    (@ arith s `(Xor_op) p mask)))))

(define undef_flag (lambda (f)
  (@ bind conv_monad (choose size1) (lambda (v) (@ set_flag f v)))))

(define first_bits (lambdas (s1 s2 x)
  (@ bind conv_monad (@ load_Z s2 (of_nat1 (@ minus s2 s1))) (lambda (c)
    (@ bind conv_monad (@ arith s2 `(Shru_op) x c) (lambda (r)
      (@ cast_u s2 s1 r)))))))

(define last_bits (lambdas (s1 s2 x)
  (@ bind conv_monad (@ load_Z s2 (two_power_nat (@ plus s1 `(S ,`(O)))))
    (lambda (c)
    (@ bind conv_monad (@ arith s2 `(Modu_op) x c) (lambda (r)
      (@ cast_u s2 s1 r)))))))

(define concat_bits (lambdas (s1 s2 x y)
  (@ bind conv_monad (@ cast_u s1 (@ plus (@ plus s1 s2) `(S ,`(O))) x)
    (lambda (x~)
    (@ bind conv_monad
      (@ load_Z (@ plus (@ plus s1 s2) `(S ,`(O)))
        (of_nat1 (@ plus s2 `(S ,`(O))))) (lambda (c)
      (@ bind conv_monad
        (@ arith (@ plus (@ plus s1 s2) `(S ,`(O))) `(Shl_op) x~ c)
        (lambda (raised_x)
        (@ bind conv_monad (@ cast_u s2 (@ plus (@ plus s1 s2) `(S ,`(O))) y)
          (lambda (y~)
          (@ arith (@ plus (@ plus s1 s2) `(S ,`(O))) `(Add_op) raised_x y~)))))))))))

(define copy_ps (lambdas (s rs) (@ cast_u s s rs)))

(define scale_to_int32 (lambda (s)
  (@ repr `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
    ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))
    (match s
       ((Scale1) `(Zpos ,`(XH)))
       ((Scale2) `(Zpos ,`(XO ,`(XH))))
       ((Scale4) `(Zpos ,`(XO ,`(XO ,`(XH)))))
       ((Scale8) `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH))))))))))

(define compute_addr (lambda (a)
  (let ((disp (addrDisp a)))
    (match (addrBase a)
       ((Some r2)
         (match (addrIndex a)
            ((Some p)
              (match p
                 ((Pair s r3)
                   (@ bind conv_monad (load_reg r2) (lambda (b)
                     (@ bind conv_monad (load_reg r3) (lambda (i)
                       (@ bind conv_monad
                         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                           ,`(S ,`(S ,`(S
                           ,`(O))))))))))))))))))))))))))))))))
                           (scale_to_int32 s)) (lambda (s0)
                         (@ bind conv_monad (@ arith size32 `(Mul_op) i s0)
                           (lambda (p0)
                           (@ bind conv_monad (@ arith size32 `(Add_op) b p0)
                             (lambda (p1)
                             (@ bind conv_monad
                               (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                 ,`(O)))))))))))))))))))))))))))))))) disp)
                               (lambda (disp0)
                               (@ arith size32 `(Add_op) p1 disp0))))))))))))))))
            ((None)
              (@ bind conv_monad (load_reg r2) (lambda (p1)
                (@ bind conv_monad
                  (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                    ,`(O)))))))))))))))))))))))))))))))) disp) (lambda (p2)
                  (@ arith size32 `(Add_op) p1 p2))))))))
       ((None)
         (match (addrIndex a)
            ((Some p)
              (match p
                 ((Pair s r)
                   (@ bind conv_monad (load_reg r) (lambda (i)
                     (@ bind conv_monad
                       (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                         ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))
                         (scale_to_int32 s)) (lambda (s0)
                       (@ bind conv_monad
                         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                           ,`(S ,`(S ,`(S
                           ,`(O)))))))))))))))))))))))))))))))) disp)
                         (lambda (disp0)
                         (@ bind conv_monad (@ arith size32 `(Mul_op) i s0)
                           (lambda (p0)
                           (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                             ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                             ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                             ,`(S ,`(S ,`(S ,`(S ,`(S
                             ,`(O)))))))))))))))))))))))))))))))) `(Add_op)
                             disp0 p0))))))))))))
            ((None)
              (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                ,`(O)))))))))))))))))))))))))))))))) disp))))))))

(define add_and_check_segment (lambdas (seg a)
  (@ bind conv_monad (get_seg_start seg) (lambda (start)
    (@ bind conv_monad (get_seg_limit seg) (lambda (limit)
      (@ bind conv_monad (@ test size32 `(Ltu_op) limit a) (lambda (guard)
        (@ bind conv_monad (if_trap guard) (lambda (x)
          (@ arith size32 `(Add_op) start a)))))))))))

(define lmem (lambdas (seg a)
  (@ bind conv_monad (@ add_and_check_segment seg a) (lambda (p)
    (read_byte p)))))

(define smem (lambdas (seg v a)
  (@ bind conv_monad (@ add_and_check_segment seg a) (lambda (p)
    (@ write_byte v p)))))

(define load_mem_n (lambdas (seg addr nbytes_minus_one)
  (match nbytes_minus_one
     ((O) (@ lmem seg addr))
     ((S n)
       (@ bind conv_monad (@ load_mem_n seg addr n) (lambda (rec)
         (@ bind conv_monad (@ load_Z size32 (of_nat1 `(S ,n)))
           (lambda (count)
           (@ bind conv_monad (@ arith size32 `(Add_op) addr count)
             (lambda (p3)
             (@ bind conv_monad (@ lmem seg p3) (lambda (nb)
               (@ bind conv_monad
                 (@ cast_u
                   (@ minus
                     (@ mult (@ plus n `(S ,`(O))) `(S ,`(S ,`(S ,`(S ,`(S
                       ,`(S ,`(S ,`(S ,`(O)))))))))) `(S ,`(O)))
                   (@ minus
                     (@ mult (@ plus nbytes_minus_one `(S ,`(O))) `(S ,`(S
                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))) `(S
                     ,`(O))) rec) (lambda (p5)
                 (@ bind conv_monad
                   (@ cast_u size8
                     (@ minus
                       (@ mult (@ plus nbytes_minus_one `(S ,`(O))) `(S ,`(S
                         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))) `(S
                       ,`(O))) nb) (lambda (p6)
                   (@ bind conv_monad
                     (@ load_Z
                       (@ minus
                         (@ mult (@ plus nbytes_minus_one `(S ,`(O))) `(S
                           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))
                         `(S ,`(O)))
                       (@ mul1 (of_nat1 `(S ,n)) `(Zpos ,`(XO ,`(XO ,`(XO
                         ,`(XH))))))) (lambda (p7)
                     (@ bind conv_monad
                       (@ arith
                         (@ minus
                           (@ mult (@ plus nbytes_minus_one `(S ,`(O))) `(S
                             ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                             ,`(O)))))))))) `(S ,`(O))) `(Shl_op) p6 p7)
                       (lambda (p8)
                       (@ arith
                         (@ minus
                           (@ mult (@ plus `(S ,n) `(S ,`(O))) `(S ,`(S ,`(S
                             ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))) `(S
                           ,`(O))) `(Or_op) p5 p8)))))))))))))))))))))
  
(define load_mem80 (lambdas (seg addr)
  (@ load_mem_n seg addr `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
    ,`(O)))))))))))))

(define load_mem64 (lambdas (seg addr)
  (@ load_mem_n seg addr `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))

(define load_mem32 (lambdas (seg addr)
  (@ load_mem_n seg addr `(S ,`(S ,`(S ,`(O)))))))

(define load_mem16 (lambdas (seg addr) (@ load_mem_n seg addr `(S ,`(O)))))

(define load_mem8 (lambdas (seg addr) (@ load_mem_n seg addr `(O))))

(define opsize (lambdas (override w)
  (match override
     ((True)
       (match w
          ((True) size16)
          ((False) size8)))
     ((False)
       (match w
          ((True) size32)
          ((False) size8))))))

(define load_mem (lambdas (p w seg op)
  (match (op_override p)
     ((True)
       (match w
          ((True) (@ load_mem16 seg op))
          ((False) (@ load_mem8 seg op))))
     ((False)
       (match w
          ((True) (@ load_mem32 seg op))
          ((False) (@ load_mem8 seg op)))))))

(define iload_op32 (lambdas (seg op)
  (match op
     ((Imm_op i)
       (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))
         i))
     ((Reg_op r) (load_reg r))
     ((Address_op a)
       (@ bind conv_monad (compute_addr a) (lambda (p1)
         (@ load_mem32 seg p1))))
     ((Offset_op off)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) off) (lambda (p1)
         (@ load_mem32 seg p1)))))))

(define iload_op16 (lambdas (seg op)
  (match op
     ((Imm_op i)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) i) (lambda (tmp)
         (@ cast_u `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))
           size16 tmp))))
     ((Reg_op r)
       (@ bind conv_monad (load_reg r) (lambda (tmp)
         (@ cast_u size32 size16 tmp))))
     ((Address_op a)
       (@ bind conv_monad (compute_addr a) (lambda (p1)
         (@ load_mem16 seg p1))))
     ((Offset_op off)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) off) (lambda (p1)
         (@ load_mem16 seg p1)))))))

(define iload_op8 (lambdas (seg op)
  (match op
     ((Imm_op i)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) i) (lambda (tmp)
         (@ cast_u `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))
           size8 tmp))))
     ((Reg_op r)
       (@ bind conv_monad
         (load_reg
           (match r
              ((EAX) `(EAX))
              ((ECX) `(ECX))
              ((EDX) `(EDX))
              ((EBX) `(EBX))
              ((ESP) `(EAX))
              ((EBP) `(ECX))
              ((ESI) `(EDX))
              ((EDI) `(EBX)))) (lambda (tmp)
         (match r
            ((EAX) (@ cast_u size32 size8 tmp))
            ((ECX) (@ cast_u size32 size8 tmp))
            ((EDX) (@ cast_u size32 size8 tmp))
            ((EBX) (@ cast_u size32 size8 tmp))
            ((ESP)
              (@ bind conv_monad
                (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH))))))
                (lambda (eight)
                (@ bind conv_monad (@ arith size32 `(Shru_op) tmp eight)
                  (lambda (tmp2) (@ cast_u size32 size8 tmp2))))))
            ((EBP)
              (@ bind conv_monad
                (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH))))))
                (lambda (eight)
                (@ bind conv_monad (@ arith size32 `(Shru_op) tmp eight)
                  (lambda (tmp2) (@ cast_u size32 size8 tmp2))))))
            ((ESI)
              (@ bind conv_monad
                (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH))))))
                (lambda (eight)
                (@ bind conv_monad (@ arith size32 `(Shru_op) tmp eight)
                  (lambda (tmp2) (@ cast_u size32 size8 tmp2))))))
            ((EDI)
              (@ bind conv_monad
                (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH))))))
                (lambda (eight)
                (@ bind conv_monad (@ arith size32 `(Shru_op) tmp eight)
                  (lambda (tmp2) (@ cast_u size32 size8 tmp2))))))))))
     ((Address_op a)
       (@ bind conv_monad (compute_addr a) (lambda (p1)
         (@ load_mem8 seg p1))))
     ((Offset_op off)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) off) (lambda (p1)
         (@ load_mem8 seg p1)))))))

(define set_mem_n (lambdas (t seg v addr)
  (match t
     ((O) (@ smem seg v addr))
     ((S u)
       (@ bind conv_monad
         (@ cast_u
           (@ minus
             (@ mult `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))
               (@ plus t `(S ,`(O)))) `(S ,`(O)))
           (@ minus
             (@ mult `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))
               (@ plus u `(S ,`(O)))) `(S ,`(O))) v) (lambda (p1)
         (@ bind conv_monad (@ set_mem_n u seg p1 addr) (lambda (x)
           (@ bind conv_monad
             (@ load_Z
               (@ minus
                 (@ mult `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))
                   (@ plus t `(S ,`(O)))) `(S ,`(O)))
               (of_nat1
                 (@ mult `(S ,u) `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                   ,`(O)))))))))))) (lambda (p2)
             (@ bind conv_monad
               (@ arith
                 (@ minus
                   (@ mult `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                     ,`(O))))))))) (@ plus t `(S ,`(O)))) `(S ,`(O)))
                 `(Shru_op) v p2) (lambda (p3)
               (@ bind conv_monad
                 (@ cast_u
                   (@ minus
                     (@ mult `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                       ,`(O))))))))) (@ plus t `(S ,`(O)))) `(S ,`(O))) size8
                   p3) (lambda (p4)
                 (@ bind conv_monad (@ load_Z size32 (of_nat1 `(S ,u)))
                   (lambda (p5)
                   (@ bind conv_monad (@ arith size32 `(Add_op) p5 addr)
                     (lambda (p6) (@ smem seg p4 p6)))))))))))))))))))
  
(define set_mem80 (lambdas (seg v a)
  (@ set_mem_n `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))) seg
    v a)))

(define set_mem64 (lambdas (seg v a)
  (@ set_mem_n `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))) seg v a)))

(define set_mem32 (lambdas (seg v a)
  (@ set_mem_n `(S ,`(S ,`(S ,`(O)))) seg v a)))

(define set_mem16 (lambdas (seg v a) (@ set_mem_n `(S ,`(O)) seg v a)))

(define set_mem8 (lambdas (seg v a) (@ set_mem_n `(O) seg v a)))

(define set_mem (lambdas (p w seg)
  (match (op_override p)
     ((True)
       (match w
          ((True) (set_mem16 seg))
          ((False) (set_mem8 seg))))
     ((False)
       (match w
          ((True) (set_mem32 seg))
          ((False) (set_mem8 seg)))))))

(define iset_op80 (lambdas (seg p op)
  (match op
     ((Imm_op i) raise_error)
     ((Reg_op r)
       (@ bind conv_monad (@ cast_u size80 size32 p) (lambda (tmp)
         (@ set_reg tmp r))))
     ((Address_op a)
       (@ bind conv_monad (compute_addr a) (lambda (addr)
         (@ bind conv_monad (@ cast_u size80 size32 p) (lambda (tmp)
           (@ set_mem32 seg tmp addr))))))
     ((Offset_op off)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) off) (lambda (addr)
         (@ bind conv_monad (@ cast_u size80 size32 p) (lambda (tmp)
           (@ set_mem32 seg tmp addr)))))))))

(define iset_op32 (lambdas (seg p op)
  (match op
     ((Imm_op i) raise_error)
     ((Reg_op r) (@ set_reg p r))
     ((Address_op a)
       (@ bind conv_monad (compute_addr a) (lambda (addr)
         (@ set_mem32 seg p addr))))
     ((Offset_op off)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) off) (lambda (addr)
         (@ set_mem32 seg p addr)))))))

(define iset_op16 (lambdas (seg p op)
  (match op
     ((Imm_op i) raise_error)
     ((Reg_op r)
       (@ bind conv_monad (load_reg r) (lambda (tmp)
         (@ bind conv_monad (@ load_int size32 (mone size32)) (lambda (mask)
           (@ bind conv_monad
             (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XH)))))))
             (lambda (sixteen)
             (@ bind conv_monad (@ arith size32 `(Shl_op) mask sixteen)
               (lambda (mask2)
               (@ bind conv_monad (@ arith size32 `(And_op) mask2 tmp)
                 (lambda (tmp2)
                 (@ bind conv_monad (@ cast_u size16 size32 p) (lambda (p32)
                   (@ bind conv_monad (@ arith size32 `(Or_op) tmp2 p32)
                     (lambda (tmp3) (@ set_reg tmp3 r))))))))))))))))
     ((Address_op a)
       (@ bind conv_monad (compute_addr a) (lambda (addr)
         (@ set_mem16 seg p addr))))
     ((Offset_op off)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) off) (lambda (addr)
         (@ set_mem16 seg p addr)))))))

(define iset_op8 (lambdas (seg p op)
  (match op
     ((Imm_op i) raise_error)
     ((Reg_op r)
       (@ bind conv_monad
         (load_reg
           (match r
              ((EAX) `(EAX))
              ((ECX) `(ECX))
              ((EDX) `(EDX))
              ((EBX) `(EBX))
              ((ESP) `(EAX))
              ((EBP) `(ECX))
              ((ESI) `(EDX))
              ((EDI) `(EBX)))) (lambda (tmp0)
         (@ bind conv_monad
           (@ load_Z size32
             (match r
                ((EAX) `(Z0))
                ((ECX) `(Z0))
                ((EDX) `(Z0))
                ((EBX) `(Z0))
                ((ESP) `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH))))))
                ((EBP) `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH))))))
                ((ESI) `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH))))))
                ((EDI) `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH)))))))) (lambda (shift)
           (@ bind conv_monad (@ load_int size32 (mone size32))
             (lambda (mone0)
             (@ bind conv_monad
               (@ load_Z size32 `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI
                 ,`(XI ,`(XH)))))))))) (lambda (mask0)
               (@ bind conv_monad (@ arith size32 `(Shl_op) mask0 shift)
                 (lambda (mask1)
                 (@ bind conv_monad (@ arith size32 `(Xor_op) mask1 mone0)
                   (lambda (mask2)
                   (@ bind conv_monad (@ arith size32 `(And_op) tmp0 mask2)
                     (lambda (tmp1)
                     (@ bind conv_monad (@ cast_u size8 size32 p)
                       (lambda (pext)
                       (@ bind conv_monad
                         (@ arith size32 `(Shl_op) pext shift)
                         (lambda (pext_shift)
                         (@ bind conv_monad
                           (@ arith size32 `(Or_op) tmp1 pext_shift)
                           (lambda (res)
                           (@ set_reg res
                             (match r
                                ((EAX) `(EAX))
                                ((ECX) `(ECX))
                                ((EDX) `(EDX))
                                ((EBX) `(EBX))
                                ((ESP) `(EAX))
                                ((EBP) `(ECX))
                                ((ESI) `(EDX))
                                ((EDI) `(EBX)))))))))))))))))))))))))
     ((Address_op a)
       (@ bind conv_monad (compute_addr a) (lambda (addr)
         (@ set_mem8 seg p addr))))
     ((Offset_op off)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) off) (lambda (addr)
         (@ set_mem8 seg p addr)))))))

(define load_op (lambdas (p w seg op)
  (match (op_override p)
     ((True)
       (match w
          ((True) (@ iload_op16 seg op))
          ((False) (@ iload_op8 seg op))))
     ((False)
       (match w
          ((True) (@ iload_op32 seg op))
          ((False) (@ iload_op8 seg op)))))))

(define set_op (lambdas (p w seg)
  (match (op_override p)
     ((True)
       (match w
          ((True) (iset_op16 seg))
          ((False) (iset_op8 seg))))
     ((False)
       (match w
          ((True) (iset_op32 seg))
          ((False) (iset_op8 seg)))))))

(define get_segment (lambdas (p def)
  (match (seg_override p)
     ((Some s) s)
     ((None) def))))

(define op_contains_stack (lambda (op)
  (match op
     ((Imm_op i) `(False))
     ((Reg_op r) `(False))
     ((Address_op a)
       (match (addrBase a)
          ((Some r)
            (match r
               ((EAX) `(False))
               ((ECX) `(False))
               ((EDX) `(False))
               ((EBX) `(False))
               ((ESP) `(True))
               ((EBP) `(True))
               ((ESI) `(False))
               ((EDI) `(False))))
          ((None) `(False))))
     ((Offset_op i) `(False)))))

(define get_segment_op (lambdas (p def op)
  (match (seg_override p)
     ((Some s) s)
     ((None)
       (match (op_contains_stack op)
          ((True) `(SS))
          ((False) def))))))

(define get_segment_op2 (lambdas (p def op1 op2)
  (match (seg_override p)
     ((Some s) s)
     ((None)
       (let ((b (op_contains_stack op1)))
         (let ((b0 (op_contains_stack op2)))
           (match b
              ((True) `(SS))
              ((False)
                (match b0
                   ((True) `(SS))
                   ((False) def))))))))))

(define compute_cc (lambda (ct)
  (match ct
     ((O_ct) (get_flag `(OF)))
     ((NO_ct)
       (@ bind conv_monad (get_flag `(OF)) (lambda (p) (@ not0 size1 p))))
     ((B_ct) (get_flag `(CF)))
     ((NB_ct)
       (@ bind conv_monad (get_flag `(CF)) (lambda (p) (@ not0 size1 p))))
     ((E_ct) (get_flag `(ZF)))
     ((NE_ct)
       (@ bind conv_monad (get_flag `(ZF)) (lambda (p) (@ not0 size1 p))))
     ((BE_ct)
       (@ bind conv_monad (get_flag `(CF)) (lambda (cf)
         (@ bind conv_monad (get_flag `(ZF)) (lambda (zf)
           (@ arith size1 `(Or_op) cf zf))))))
     ((NBE_ct)
       (@ bind conv_monad (get_flag `(CF)) (lambda (cf)
         (@ bind conv_monad (get_flag `(ZF)) (lambda (zf)
           (@ bind conv_monad (@ arith size1 `(Or_op) cf zf) (lambda (p)
             (@ not0 size1 p))))))))
     ((S_ct) (get_flag `(SF)))
     ((NS_ct)
       (@ bind conv_monad (get_flag `(SF)) (lambda (p) (@ not0 size1 p))))
     ((P_ct) (get_flag `(PF)))
     ((NP_ct)
       (@ bind conv_monad (get_flag `(PF)) (lambda (p) (@ not0 size1 p))))
     ((L_ct)
       (@ bind conv_monad (get_flag `(SF)) (lambda (sf)
         (@ bind conv_monad (get_flag `(OF)) (lambda (of)
           (@ arith size1 `(Xor_op) sf of))))))
     ((NL_ct)
       (@ bind conv_monad (get_flag `(SF)) (lambda (sf)
         (@ bind conv_monad (get_flag `(OF)) (lambda (of)
           (@ bind conv_monad (@ arith size1 `(Xor_op) sf of) (lambda (p)
             (@ not0 size1 p))))))))
     ((LE_ct)
       (@ bind conv_monad (get_flag `(ZF)) (lambda (zf)
         (@ bind conv_monad (get_flag `(OF)) (lambda (of)
           (@ bind conv_monad (get_flag `(SF)) (lambda (sf)
             (@ bind conv_monad (@ arith size1 `(Xor_op) of sf) (lambda (p)
               (@ arith size1 `(Or_op) zf p))))))))))
     ((NLE_ct)
       (@ bind conv_monad (get_flag `(ZF)) (lambda (zf)
         (@ bind conv_monad (get_flag `(OF)) (lambda (of)
           (@ bind conv_monad (get_flag `(SF)) (lambda (sf)
             (@ bind conv_monad (@ arith size1 `(Xor_op) of sf) (lambda (p0)
               (@ bind conv_monad (@ arith size1 `(Or_op) zf p0) (lambda (p1)
                 (@ not0 size1 p1)))))))))))))))

(define compute_parity_aux (lambdas (s op1 op2 n)
  (match n
     ((O) (@ load_Z size1 `(Z0)))
     ((S m)
       (@ bind conv_monad (@ compute_parity_aux s op1 op2 m) (lambda (op3)
         (@ bind conv_monad (@ load_Z s `(Zpos ,`(XH))) (lambda (one2)
           (@ bind conv_monad (@ arith s `(Shru_op) op1 one2) (lambda (op4)
             (@ bind conv_monad (@ cast_u s size1 op4) (lambda (r)
               (@ arith size1 `(Xor_op) r op3)))))))))))))
  
(define compute_parity (lambdas (s op)
  (@ bind conv_monad (@ load_Z size1 `(Z0)) (lambda (r2)
    (@ bind conv_monad (@ load_Z size1 `(Zpos ,`(XH))) (lambda (one2)
      (@ bind conv_monad
        (@ compute_parity_aux s op r2 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
          ,`(O)))))))))) (lambda (p) (@ arith size1 `(Xor_op) p one2)))))))))

(define conv_INC (lambdas (pre w op)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op pre `(DS) op)))
        (@ bind conv_monad (@ load seg op) (lambda (p0)
          (@ bind conv_monad
            (@ load_Z (@ opsize (op_override pre) w) `(Zpos ,`(XH)))
            (lambda (p1)
            (@ bind conv_monad
              (@ arith (@ opsize (op_override pre) w) `(Add_op) p0 p1)
              (lambda (p2)
              (@ bind conv_monad (@ set2 seg p2 op) (lambda (x)
                (@ bind conv_monad
                  (@ load_Z (@ opsize (op_override pre) w) `(Z0))
                  (lambda (zero2)
                  (@ bind conv_monad
                    (@ test (@ opsize (op_override pre) w) `(Lt_op) p2 p0)
                    (lambda (ofp)
                    (@ bind conv_monad (@ set_flag `(OF) ofp) (lambda (x0)
                      (@ bind conv_monad
                        (@ test (@ opsize (op_override pre) w) `(Eq_op) p2
                          zero2) (lambda (zfp)
                        (@ bind conv_monad (@ set_flag `(ZF) zfp)
                          (lambda (x1)
                          (@ bind conv_monad
                            (@ test (@ opsize (op_override pre) w) `(Lt_op)
                              p2 zero2) (lambda (sfp)
                            (@ bind conv_monad (@ set_flag `(SF) sfp)
                              (lambda (x2)
                              (@ bind conv_monad
                                (@ compute_parity
                                  (@ opsize (op_override pre) w) p2)
                                (lambda (pfp)
                                (@ bind conv_monad (@ set_flag `(PF) pfp)
                                  (lambda (x3)
                                  (@ bind conv_monad
                                    (@ cast_u (@ opsize (op_override pre) w)
                                      size4 p0) (lambda (n0)
                                    (@ bind conv_monad
                                      (@ load_Z size4 `(Zpos ,`(XH)))
                                      (lambda (n1)
                                      (@ bind conv_monad
                                        (@ arith size4 `(Add_op) n0 n1)
                                        (lambda (n2)
                                        (@ bind conv_monad
                                          (@ test size4 `(Ltu_op) n2 n0)
                                          (lambda (afp)
                                          (@ set_flag `(AF) afp))))))))))))))))))))))))))))))))))))))))

(define conv_DEC (lambdas (pre w op)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op pre `(DS) op)))
        (@ bind conv_monad (@ load seg op) (lambda (p0)
          (@ bind conv_monad
            (@ load_Z (@ opsize (op_override pre) w) `(Zpos ,`(XH)))
            (lambda (p1)
            (@ bind conv_monad
              (@ arith (@ opsize (op_override pre) w) `(Sub_op) p0 p1)
              (lambda (p2)
              (@ bind conv_monad (@ set2 seg p2 op) (lambda (x)
                (@ bind conv_monad
                  (@ load_Z (@ opsize (op_override pre) w) `(Z0))
                  (lambda (zero2)
                  (@ bind conv_monad
                    (@ test (@ opsize (op_override pre) w) `(Lt_op) p0 p2)
                    (lambda (ofp)
                    (@ bind conv_monad (@ set_flag `(OF) ofp) (lambda (x0)
                      (@ bind conv_monad
                        (@ test (@ opsize (op_override pre) w) `(Eq_op) p2
                          zero2) (lambda (zfp)
                        (@ bind conv_monad (@ set_flag `(ZF) zfp)
                          (lambda (x1)
                          (@ bind conv_monad
                            (@ test (@ opsize (op_override pre) w) `(Lt_op)
                              p2 zero2) (lambda (sfp)
                            (@ bind conv_monad (@ set_flag `(SF) sfp)
                              (lambda (x2)
                              (@ bind conv_monad
                                (@ compute_parity
                                  (@ opsize (op_override pre) w) p2)
                                (lambda (pfp)
                                (@ bind conv_monad (@ set_flag `(PF) pfp)
                                  (lambda (x3)
                                  (@ bind conv_monad
                                    (@ cast_u (@ opsize (op_override pre) w)
                                      size4 p0) (lambda (n0)
                                    (@ bind conv_monad
                                      (@ load_Z size4 `(Zpos ,`(XH)))
                                      (lambda (n1)
                                      (@ bind conv_monad
                                        (@ arith size4 `(Sub_op) n0 n1)
                                        (lambda (n2)
                                        (@ bind conv_monad
                                          (@ test size4 `(Ltu_op) n0 n2)
                                          (lambda (afp)
                                          (@ set_flag `(AF) afp))))))))))))))))))))))))))))))))))))))))

(define conv_ADC (lambdas (pre w op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
        (@ bind conv_monad (@ load_Z (@ opsize (op_override pre) w) `(Z0))
          (lambda (zero2)
          (@ bind conv_monad (@ load_Z size1 `(Zpos ,`(XH))) (lambda (up)
            (@ bind conv_monad (@ load seg op1) (lambda (p0)
              (@ bind conv_monad (@ load seg op2) (lambda (p1)
                (@ bind conv_monad (get_flag `(CF)) (lambda (cf1)
                  (@ bind conv_monad
                    (@ cast_u size1 (@ opsize (op_override pre) w) cf1)
                    (lambda (cfext)
                    (@ bind conv_monad
                      (@ arith (@ opsize (op_override pre) w) `(Add_op) p0
                        p1) (lambda (p2)
                      (@ bind conv_monad
                        (@ arith (@ opsize (op_override pre) w) `(Add_op) p2
                          cfext) (lambda (p3)
                        (@ bind conv_monad (@ set2 seg p3 op1) (lambda (x)
                          (@ bind conv_monad
                            (@ test (@ opsize (op_override pre) w) `(Lt_op)
                              zero2 p0) (lambda (b0)
                            (@ bind conv_monad
                              (@ test (@ opsize (op_override pre) w) `(Lt_op)
                                zero2 p1) (lambda (b1)
                              (@ bind conv_monad
                                (@ test (@ opsize (op_override pre) w)
                                  `(Lt_op) zero2 p3) (lambda (b2)
                                (@ bind conv_monad
                                  (@ arith size1 `(Xor_op) b0 b1)
                                  (lambda (b3)
                                  (@ bind conv_monad
                                    (@ arith size1 `(Xor_op) up b3)
                                    (lambda (b4)
                                    (@ bind conv_monad
                                      (@ arith size1 `(Xor_op) b0 b2)
                                      (lambda (b5)
                                      (@ bind conv_monad
                                        (@ arith size1 `(And_op) b4 b5)
                                        (lambda (b6)
                                        (@ bind conv_monad
                                          (@ set_flag `(OF) b6) (lambda (x0)
                                          (@ bind conv_monad
                                            (@ test
                                              (@ opsize (op_override pre) w)
                                              `(Ltu_op) p3 p0) (lambda (b7)
                                            (@ bind conv_monad
                                              (@ test
                                                (@ opsize (op_override pre)
                                                  w) `(Ltu_op) p3 p1)
                                              (lambda (b8)
                                              (@ bind conv_monad
                                                (@ arith size1 `(Or_op) b7
                                                  b8) (lambda (b9)
                                                (@ bind conv_monad
                                                  (@ set_flag `(CF) b9)
                                                  (lambda (x1)
                                                  (@ bind conv_monad
                                                    (@ test
                                                      (@ opsize
                                                        (op_override pre) w)
                                                      `(Eq_op) p3 zero2)
                                                    (lambda (b10)
                                                    (@ bind conv_monad
                                                      (@ set_flag `(ZF) b10)
                                                      (lambda (x2)
                                                      (@ bind conv_monad
                                                        (@ test
                                                          (@ opsize
                                                            (op_override pre)
                                                            w) `(Lt_op) p3
                                                          zero2)
                                                        (lambda (b11)
                                                        (@ bind conv_monad
                                                          (@ set_flag `(SF)
                                                            b11) (lambda (x3)
                                                          (@ bind conv_monad
                                                            (@ compute_parity
                                                              (@ opsize
                                                                (op_override
                                                                  pre) w) p3)
                                                            (lambda (b12)
                                                            (@ bind
                                                              conv_monad
                                                              (@ set_flag
                                                                `(PF) b12)
                                                              (lambda (x4)
                                                              (@ bind
                                                                conv_monad
                                                                (@ cast_u
                                                                  (@ opsize
                                                                    (op_override
                                                                    pre) w)
                                                                  size4 p0)
                                                                (lambda (n0)
                                                                (@ bind
                                                                  conv_monad
                                                                  (@ cast_u
                                                                    (@ opsize
                                                                    (op_override
                                                                    pre) w)
                                                                    size4 p1)
                                                                  (lambda (n1)
                                                                  (@ bind
                                                                    conv_monad
                                                                    (@ cast_u
                                                                    size1
                                                                    size4
                                                                    cf1)
                                                                    (lambda (cf4)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ arith
                                                                    size4
                                                                    `(Add_op)
                                                                    n0 n1)
                                                                    (lambda (n2)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ arith
                                                                    size4
                                                                    `(Add_op)
                                                                    n2 cf4)
                                                                    (lambda (n3)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ test
                                                                    size4
                                                                    `(Ltu_op)
                                                                    n3 n0)
                                                                    (lambda (b13)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ test
                                                                    size4
                                                                    `(Ltu_op)
                                                                    n3 n1)
                                                                    (lambda (b14)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ arith
                                                                    size1
                                                                    `(Or_op)
                                                                    b13 b14)
                                                                    (lambda (b15)
                                                                    (@ set_flag
                                                                    `(AF)
                                                                    b15))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_STC
  (@ bind conv_monad (@ load_Z size1 `(Zpos ,`(XH))) (lambda (one2)
    (@ set_flag `(CF) one2))))

(define conv_STD
  (@ bind conv_monad (@ load_Z size1 `(Zpos ,`(XH))) (lambda (one2)
    (@ set_flag `(DF) one2))))

(define conv_CLC
  (@ bind conv_monad (@ load_Z size1 `(Z0)) (lambda (zero2)
    (@ set_flag `(CF) zero2))))

(define conv_CLD
  (@ bind conv_monad (@ load_Z size1 `(Z0)) (lambda (zero2)
    (@ set_flag `(DF) zero2))))

(define conv_CMC
  (@ bind conv_monad (@ load_Z size1 `(Z0)) (lambda (zero2)
    (@ bind conv_monad (get_flag `(CF)) (lambda (p1)
      (@ bind conv_monad (@ test size1 `(Eq_op) zero2 p1) (lambda (p0)
        (@ set_flag `(CF) p0))))))))

(define conv_LAHF
  (@ bind conv_monad (@ load_Z size8 `(Z0)) (lambda (dst)
    (@ bind conv_monad (get_flag `(SF)) (lambda (fl)
      (@ bind conv_monad (@ load_Z size8 `(Zpos ,`(XI ,`(XI ,`(XH)))))
        (lambda (pos)
        (@ bind conv_monad (@ cast_u size1 size8 fl) (lambda (byt)
          (@ bind conv_monad (@ arith size8 `(Shl_op) byt pos) (lambda (tmp)
            (@ bind conv_monad (@ arith size8 `(Or_op) dst tmp)
              (lambda (dst0)
              (@ bind conv_monad (get_flag `(ZF)) (lambda (fl0)
                (@ bind conv_monad
                  (@ load_Z size8 `(Zpos ,`(XO ,`(XI ,`(XH)))))
                  (lambda (pos0)
                  (@ bind conv_monad (@ cast_u size1 size8 fl0)
                    (lambda (byt0)
                    (@ bind conv_monad (@ arith size8 `(Shl_op) byt0 pos0)
                      (lambda (tmp0)
                      (@ bind conv_monad (@ arith size8 `(Or_op) dst0 tmp0)
                        (lambda (dst1)
                        (@ bind conv_monad (get_flag `(AF)) (lambda (fl1)
                          (@ bind conv_monad
                            (@ load_Z size8 `(Zpos ,`(XO ,`(XO ,`(XH)))))
                            (lambda (pos2)
                            (@ bind conv_monad (@ cast_u size1 size8 fl1)
                              (lambda (byt1)
                              (@ bind conv_monad
                                (@ arith size8 `(Shl_op) byt1 pos2)
                                (lambda (tmp1)
                                (@ bind conv_monad
                                  (@ arith size8 `(Or_op) dst1 tmp1)
                                  (lambda (dst2)
                                  (@ bind conv_monad (get_flag `(PF))
                                    (lambda (fl2)
                                    (@ bind conv_monad
                                      (@ load_Z size8 `(Zpos ,`(XO ,`(XH))))
                                      (lambda (pos3)
                                      (@ bind conv_monad
                                        (@ cast_u size1 size8 fl2)
                                        (lambda (byt2)
                                        (@ bind conv_monad
                                          (@ arith size8 `(Shl_op) byt2 pos3)
                                          (lambda (tmp2)
                                          (@ bind conv_monad
                                            (@ arith size8 `(Or_op) dst2
                                              tmp2) (lambda (dst3)
                                            (@ bind conv_monad
                                              (get_flag `(CF)) (lambda (fl3)
                                              (@ bind conv_monad
                                                (@ load_Z size8 `(Z0))
                                                (lambda (pos4)
                                                (@ bind conv_monad
                                                  (@ cast_u size1 size8 fl3)
                                                  (lambda (byt3)
                                                  (@ bind conv_monad
                                                    (@ arith size8 `(Shl_op)
                                                      byt3 pos4)
                                                    (lambda (tmp3)
                                                    (@ bind conv_monad
                                                      (@ arith size8 `(Or_op)
                                                        dst3 tmp3)
                                                      (lambda (dst4)
                                                      (@ bind conv_monad
                                                        (@ load_Z size8
                                                          `(Zpos ,`(XH)))
                                                        (lambda (fl4)
                                                        (@ bind conv_monad
                                                          (@ load_Z size8
                                                            `(Zpos ,`(XH)))
                                                          (lambda (pos5)
                                                          (@ bind conv_monad
                                                            (@ cast_u size8
                                                              size8 fl4)
                                                            (lambda (byt4)
                                                            (@ bind
                                                              conv_monad
                                                              (@ arith size8
                                                                `(Shl_op)
                                                                byt4 pos5)
                                                              (lambda (tmp4)
                                                              (@ bind
                                                                conv_monad
                                                                (@ arith
                                                                  size8
                                                                  `(Or_op)
                                                                  dst4 tmp4)
                                                                (lambda (dst5)
                                                                (@ iset_op8
                                                                  `(DS) dst5
                                                                  `(Reg_op
                                                                  ,`(ESP))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_SAHF
  (@ bind conv_monad (@ load_Z size8 `(Zpos ,`(XH))) (lambda (one2)
    (@ bind conv_monad (@ iload_op8 `(DS) `(Reg_op ,`(ESP))) (lambda (ah)
      (@ bind conv_monad (@ load_Z size8 `(Zpos ,`(XI ,`(XI ,`(XH)))))
        (lambda (pos)
        (@ bind conv_monad (@ arith size8 `(Shr_op) ah pos) (lambda (tmp)
          (@ bind conv_monad (@ arith size8 `(And_op) tmp one2)
            (lambda (tmp0)
            (@ bind conv_monad (@ test size8 `(Eq_op) one2 tmp0) (lambda (b)
              (@ bind conv_monad (@ set_flag `(SF) b) (lambda (x)
                (@ bind conv_monad
                  (@ load_Z size8 `(Zpos ,`(XO ,`(XI ,`(XH)))))
                  (lambda (pos0)
                  (@ bind conv_monad (@ arith size8 `(Shr_op) ah pos0)
                    (lambda (tmp1)
                    (@ bind conv_monad (@ arith size8 `(And_op) tmp1 one2)
                      (lambda (tmp2)
                      (@ bind conv_monad (@ test size8 `(Eq_op) one2 tmp2)
                        (lambda (b0)
                        (@ bind conv_monad (@ set_flag `(ZF) b0) (lambda (x0)
                          (@ bind conv_monad
                            (@ load_Z size8 `(Zpos ,`(XO ,`(XO ,`(XH)))))
                            (lambda (pos2)
                            (@ bind conv_monad
                              (@ arith size8 `(Shr_op) ah pos2)
                              (lambda (tmp3)
                              (@ bind conv_monad
                                (@ arith size8 `(And_op) tmp3 one2)
                                (lambda (tmp4)
                                (@ bind conv_monad
                                  (@ test size8 `(Eq_op) one2 tmp4)
                                  (lambda (b1)
                                  (@ bind conv_monad (@ set_flag `(AF) b1)
                                    (lambda (x1)
                                    (@ bind conv_monad
                                      (@ load_Z size8 `(Zpos ,`(XO ,`(XH))))
                                      (lambda (pos3)
                                      (@ bind conv_monad
                                        (@ arith size8 `(Shr_op) ah pos3)
                                        (lambda (tmp5)
                                        (@ bind conv_monad
                                          (@ arith size8 `(And_op) tmp5 one2)
                                          (lambda (tmp6)
                                          (@ bind conv_monad
                                            (@ test size8 `(Eq_op) one2 tmp6)
                                            (lambda (b2)
                                            (@ bind conv_monad
                                              (@ set_flag `(PF) b2)
                                              (lambda (x2)
                                              (@ bind conv_monad
                                                (@ load_Z size8 `(Z0))
                                                (lambda (pos4)
                                                (@ bind conv_monad
                                                  (@ arith size8 `(Shr_op) ah
                                                    pos4) (lambda (tmp7)
                                                  (@ bind conv_monad
                                                    (@ arith size8 `(And_op)
                                                      tmp7 one2)
                                                    (lambda (tmp8)
                                                    (@ bind conv_monad
                                                      (@ test size8 `(Eq_op)
                                                        one2 tmp8)
                                                      (lambda (b3)
                                                      (@ set_flag `(CF) b3))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_ADD (lambdas (pre w op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
        (@ bind conv_monad (@ load_Z (@ opsize (op_override pre) w) `(Z0))
          (lambda (zero2)
          (@ bind conv_monad (@ load_Z size1 `(Zpos ,`(XH))) (lambda (up)
            (@ bind conv_monad (@ load seg op1) (lambda (p0)
              (@ bind conv_monad (@ load seg op2) (lambda (p1)
                (@ bind conv_monad
                  (@ arith (@ opsize (op_override pre) w) `(Add_op) p0 p1)
                  (lambda (p2)
                  (@ bind conv_monad (@ set2 seg p2 op1) (lambda (x)
                    (@ bind conv_monad
                      (@ test (@ opsize (op_override pre) w) `(Lt_op) zero2
                        p0) (lambda (b0)
                      (@ bind conv_monad
                        (@ test (@ opsize (op_override pre) w) `(Lt_op) zero2
                          p1) (lambda (b1)
                        (@ bind conv_monad
                          (@ test (@ opsize (op_override pre) w) `(Lt_op)
                            zero2 p2) (lambda (b2)
                          (@ bind conv_monad (@ arith size1 `(Xor_op) b0 b1)
                            (lambda (b3)
                            (@ bind conv_monad
                              (@ arith size1 `(Xor_op) up b3) (lambda (b4)
                              (@ bind conv_monad
                                (@ arith size1 `(Xor_op) b0 b2) (lambda (b5)
                                (@ bind conv_monad
                                  (@ arith size1 `(And_op) b4 b5)
                                  (lambda (b6)
                                  (@ bind conv_monad (@ set_flag `(OF) b6)
                                    (lambda (x0)
                                    (@ bind conv_monad
                                      (@ test (@ opsize (op_override pre) w)
                                        `(Ltu_op) p2 p0) (lambda (b7)
                                      (@ bind conv_monad
                                        (@ test
                                          (@ opsize (op_override pre) w)
                                          `(Ltu_op) p2 p1) (lambda (b8)
                                        (@ bind conv_monad
                                          (@ arith size1 `(Or_op) b7 b8)
                                          (lambda (b9)
                                          (@ bind conv_monad
                                            (@ set_flag `(CF) b9)
                                            (lambda (x1)
                                            (@ bind conv_monad
                                              (@ test
                                                (@ opsize (op_override pre)
                                                  w) `(Eq_op) p2 zero2)
                                              (lambda (b10)
                                              (@ bind conv_monad
                                                (@ set_flag `(ZF) b10)
                                                (lambda (x2)
                                                (@ bind conv_monad
                                                  (@ test
                                                    (@ opsize
                                                      (op_override pre) w)
                                                    `(Lt_op) p2 zero2)
                                                  (lambda (b11)
                                                  (@ bind conv_monad
                                                    (@ set_flag `(SF) b11)
                                                    (lambda (x3)
                                                    (@ bind conv_monad
                                                      (@ compute_parity
                                                        (@ opsize
                                                          (op_override pre)
                                                          w) p2)
                                                      (lambda (b12)
                                                      (@ bind conv_monad
                                                        (@ set_flag `(PF)
                                                          b12) (lambda (x4)
                                                        (@ bind conv_monad
                                                          (@ cast_u
                                                            (@ opsize
                                                              (op_override
                                                                pre) w) size4
                                                            p0) (lambda (n0)
                                                          (@ bind conv_monad
                                                            (@ cast_u
                                                              (@ opsize
                                                                (op_override
                                                                  pre) w)
                                                              size4 p1)
                                                            (lambda (n1)
                                                            (@ bind
                                                              conv_monad
                                                              (@ arith size4
                                                                `(Add_op) n0
                                                                n1)
                                                              (lambda (n2)
                                                              (@ bind
                                                                conv_monad
                                                                (@ test size4
                                                                  `(Ltu_op)
                                                                  n2 n0)
                                                                (lambda (b13)
                                                                (@ bind
                                                                  conv_monad
                                                                  (@ test
                                                                    size4
                                                                    `(Ltu_op)
                                                                    n2 n1)
                                                                  (lambda (b14)
                                                                  (@ bind
                                                                    conv_monad
                                                                    (@ arith
                                                                    size1
                                                                    `(Or_op)
                                                                    b13 b14)
                                                                    (lambda (b15)
                                                                    (@ set_flag
                                                                    `(AF)
                                                                    b15))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_SUB_CMP_generic (lambdas (e pre w dest op1 op2 segdest seg1
  seg2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (@ bind conv_monad (@ load_Z (@ opsize (op_override pre) w) `(Z0))
        (lambda (zero2)
        (@ bind conv_monad (@ load_Z size1 `(Zpos ,`(XH))) (lambda (up)
          (@ bind conv_monad (@ load seg1 op1) (lambda (p0)
            (@ bind conv_monad (@ load seg2 op2) (lambda (p1)
              (@ bind conv_monad
                (@ arith (@ opsize (op_override pre) w) `(Sub_op) p0 p1)
                (lambda (p2)
                (@ bind conv_monad
                  (@ arith (@ opsize (op_override pre) w) `(Sub_op) zero2 p1)
                  (lambda (negp1)
                  (@ bind conv_monad
                    (@ test (@ opsize (op_override pre) w) `(Lt_op) zero2 p0)
                    (lambda (b0)
                    (@ bind conv_monad
                      (@ test (@ opsize (op_override pre) w) `(Lt_op) zero2
                        negp1) (lambda (b1)
                      (@ bind conv_monad
                        (@ test (@ opsize (op_override pre) w) `(Lt_op) zero2
                          p2) (lambda (b2)
                        (@ bind conv_monad (@ arith size1 `(Xor_op) b0 b1)
                          (lambda (b3)
                          (@ bind conv_monad (@ arith size1 `(Xor_op) up b3)
                            (lambda (b4)
                            (@ bind conv_monad
                              (@ arith size1 `(Xor_op) b0 b2) (lambda (b5)
                              (@ bind conv_monad
                                (@ arith size1 `(And_op) b4 b5) (lambda (b6)
                                (@ bind conv_monad (@ set_flag `(OF) b6)
                                  (lambda (x)
                                  (@ bind conv_monad
                                    (@ test (@ opsize (op_override pre) w)
                                      `(Ltu_op) p0 p1) (lambda (b7)
                                    (@ bind conv_monad (@ set_flag `(CF) b7)
                                      (lambda (x0)
                                      (@ bind conv_monad
                                        (@ test
                                          (@ opsize (op_override pre) w)
                                          `(Eq_op) p2 zero2) (lambda (b8)
                                        (@ bind conv_monad
                                          (@ set_flag `(ZF) b8) (lambda (x1)
                                          (@ bind conv_monad
                                            (@ test
                                              (@ opsize (op_override pre) w)
                                              `(Lt_op) p2 zero2) (lambda (b9)
                                            (@ bind conv_monad
                                              (@ set_flag `(SF) b9)
                                              (lambda (x2)
                                              (@ bind conv_monad
                                                (@ compute_parity
                                                  (@ opsize (op_override pre)
                                                    w) p2) (lambda (b10)
                                                (@ bind conv_monad
                                                  (@ set_flag `(PF) b10)
                                                  (lambda (x3)
                                                  (@ bind conv_monad
                                                    (@ cast_u
                                                      (@ opsize
                                                        (op_override pre) w)
                                                      size4 p0) (lambda (n0)
                                                    (@ bind conv_monad
                                                      (@ cast_u
                                                        (@ opsize
                                                          (op_override pre)
                                                          w) size4 p1)
                                                      (lambda (n1)
                                                      (@ bind conv_monad
                                                        (@ test
                                                          (@ opsize
                                                            (op_override pre)
                                                            w) `(Ltu_op) p0
                                                          p1) (lambda (b11)
                                                        (@ bind conv_monad
                                                          (@ set_flag `(AF)
                                                            b11) (lambda (x4)
                                                          (match e
                                                             ((True)
                                                               (@ set2
                                                                 segdest p2
                                                                 dest))
                                                             ((False) no_op))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_CMP (lambdas (pre w op1 op2)
  (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
    (@ conv_SUB_CMP_generic `(False) pre w op1 op1 op2 seg seg seg))))

(define conv_SUB (lambdas (pre w op1 op2)
  (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
    (@ conv_SUB_CMP_generic `(True) pre w op1 op1 op2 seg seg seg))))

(define conv_NEG (lambdas (pre w op1)
  (let ((seg (@ get_segment_op pre `(DS) op1)))
    (@ conv_SUB_CMP_generic `(True) pre w op1 `(Imm_op
      ,(zero1 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))))))))))))))))))))) op1
      seg seg seg))))

(define conv_SBB (lambdas (pre w op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
        (@ bind conv_monad (@ load_Z (@ opsize (op_override pre) w) `(Z0))
          (lambda (zero2)
          (@ bind conv_monad (@ load_Z size1 `(Zpos ,`(XH))) (lambda (up)
            (@ bind conv_monad (get_flag `(CF)) (lambda (old_cf)
              (@ bind conv_monad
                (@ cast_u size1 (@ opsize (op_override pre) w) old_cf)
                (lambda (old_cf_ext)
                (@ bind conv_monad (@ load seg op1) (lambda (p0)
                  (@ bind conv_monad (@ load seg op2) (lambda (p1)
                    (@ bind conv_monad
                      (@ arith (@ opsize (op_override pre) w) `(Sub_op) p0
                        p1) (lambda (p2_0)
                      (@ bind conv_monad
                        (@ arith (@ opsize (op_override pre) w) `(Sub_op)
                          p2_0 old_cf_ext) (lambda (p2)
                        (@ bind conv_monad
                          (@ arith (@ opsize (op_override pre) w) `(Sub_op)
                            zero2 p1) (lambda (negp1)
                          (@ bind conv_monad
                            (@ test (@ opsize (op_override pre) w) `(Lt_op)
                              zero2 p0) (lambda (b0)
                            (@ bind conv_monad
                              (@ test (@ opsize (op_override pre) w) `(Lt_op)
                                zero2 negp1) (lambda (b1)
                              (@ bind conv_monad
                                (@ test (@ opsize (op_override pre) w)
                                  `(Lt_op) zero2 p2) (lambda (b2)
                                (@ bind conv_monad
                                  (@ arith size1 `(Xor_op) b0 b1)
                                  (lambda (b3)
                                  (@ bind conv_monad
                                    (@ arith size1 `(Xor_op) up b3)
                                    (lambda (b4)
                                    (@ bind conv_monad
                                      (@ arith size1 `(Xor_op) b0 b2)
                                      (lambda (b5)
                                      (@ bind conv_monad
                                        (@ arith size1 `(And_op) b4 b5)
                                        (lambda (b6)
                                        (@ bind conv_monad
                                          (@ set_flag `(OF) b6) (lambda (x)
                                          (@ bind conv_monad
                                            (@ test
                                              (@ opsize (op_override pre) w)
                                              `(Ltu_op) p0 p1) (lambda (b0~)
                                            (@ bind conv_monad
                                              (@ test
                                                (@ opsize (op_override pre)
                                                  w) `(Eq_op) p0 p1)
                                              (lambda (b0~~)
                                              (@ bind conv_monad
                                                (@ arith size1 `(Or_op) b0~
                                                  b0~~) (lambda (b7)
                                                (@ bind conv_monad
                                                  (@ set_flag `(CF) b7)
                                                  (lambda (x0)
                                                  (@ bind conv_monad
                                                    (@ test
                                                      (@ opsize
                                                        (op_override pre) w)
                                                      `(Eq_op) p2 zero2)
                                                    (lambda (b8)
                                                    (@ bind conv_monad
                                                      (@ set_flag `(ZF) b8)
                                                      (lambda (x1)
                                                      (@ bind conv_monad
                                                        (@ test
                                                          (@ opsize
                                                            (op_override pre)
                                                            w) `(Lt_op) p2
                                                          zero2) (lambda (b9)
                                                        (@ bind conv_monad
                                                          (@ set_flag `(SF)
                                                            b9) (lambda (x2)
                                                          (@ bind conv_monad
                                                            (@ compute_parity
                                                              (@ opsize
                                                                (op_override
                                                                  pre) w) p2)
                                                            (lambda (b10)
                                                            (@ bind
                                                              conv_monad
                                                              (@ set_flag
                                                                `(PF) b10)
                                                              (lambda (x3)
                                                              (@ bind
                                                                conv_monad
                                                                (@ cast_u
                                                                  (@ opsize
                                                                    (op_override
                                                                    pre) w)
                                                                  size4 p0)
                                                                (lambda (n0)
                                                                (@ bind
                                                                  conv_monad
                                                                  (@ cast_u
                                                                    (@ opsize
                                                                    (op_override
                                                                    pre) w)
                                                                    size4 p1)
                                                                  (lambda (n1)
                                                                  (@ bind
                                                                    conv_monad
                                                                    (@ test
                                                                    (@ opsize
                                                                    (op_override
                                                                    pre) w)
                                                                    `(Ltu_op)
                                                                    p0 p1)
                                                                    (lambda (b0~0)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ test
                                                                    (@ opsize
                                                                    (op_override
                                                                    pre) w)
                                                                    `(Eq_op)
                                                                    p0 p1)
                                                                    (lambda (b0~~0)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ arith
                                                                    size1
                                                                    `(Or_op)
                                                                    b0~0
                                                                    b0~~0)
                                                                    (lambda (b11)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ set_flag
                                                                    `(AF)
                                                                    b11)
                                                                    (lambda (x4)
                                                                    (@ set2
                                                                    seg p2
                                                                    op1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_DIV (lambdas (pre w op)
  (let ((seg (@ get_segment_op pre `(DS) op)))
    (@ bind conv_monad (undef_flag `(CF)) (lambda (x)
      (@ bind conv_monad (undef_flag `(OF)) (lambda (x0)
        (@ bind conv_monad (undef_flag `(SF)) (lambda (x1)
          (@ bind conv_monad (undef_flag `(ZF)) (lambda (x2)
            (@ bind conv_monad (undef_flag `(AF)) (lambda (x3)
              (@ bind conv_monad (undef_flag `(PF)) (lambda (x4)
                (match (op_override pre)
                   ((True)
                     (match w
                        ((True)
                          (@ bind conv_monad
                            (@ iload_op16 seg `(Reg_op ,`(EAX)))
                            (lambda (dividend_lower)
                            (@ bind conv_monad
                              (@ iload_op16 seg `(Reg_op ,`(EDX)))
                              (lambda (dividend_upper)
                              (@ bind conv_monad
                                (@ cast_u size16 size32 dividend_upper)
                                (lambda (dividend0)
                                (@ bind conv_monad
                                  (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO
                                    ,`(XO ,`(XH))))))) (lambda (sixteen)
                                  (@ bind conv_monad
                                    (@ arith size32 `(Shl_op) dividend0
                                      sixteen) (lambda (dividend1)
                                    (@ bind conv_monad
                                      (@ cast_u size16 size32 dividend_lower)
                                      (lambda (dividend_lower_ext)
                                      (@ bind conv_monad
                                        (@ arith size32 `(Or_op) dividend1
                                          dividend_lower_ext)
                                        (lambda (dividend)
                                        (@ bind conv_monad
                                          (@ iload_op16 seg op)
                                          (lambda (divisor)
                                          (@ bind conv_monad
                                            (@ load_Z size16 `(Z0))
                                            (lambda (zero2)
                                            (@ bind conv_monad
                                              (@ test size16 `(Eq_op) zero2
                                                divisor)
                                              (lambda (divide_by_zero)
                                              (@ bind conv_monad
                                                (if_trap divide_by_zero)
                                                (lambda (x5)
                                                (@ bind conv_monad
                                                  (@ cast_u size16 size32
                                                    divisor)
                                                  (lambda (divisor_ext)
                                                  (@ bind conv_monad
                                                    (@ arith size32
                                                      `(Divu_op) dividend
                                                      divisor_ext)
                                                    (lambda (quotient)
                                                    (@ bind conv_monad
                                                      (@ load_Z size32 `(Zpos
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XH))))))))))))))))))
                                                      (lambda (max_quotient)
                                                      (@ bind conv_monad
                                                        (@ test size32
                                                          `(Ltu_op)
                                                          max_quotient
                                                          quotient)
                                                        (lambda (div_error)
                                                        (@ bind conv_monad
                                                          (if_trap div_error)
                                                          (lambda (x6)
                                                          (@ bind conv_monad
                                                            (@ arith size32
                                                              `(Modu_op)
                                                              dividend
                                                              divisor_ext)
                                                            (lambda (remainder)
                                                            (@ bind
                                                              conv_monad
                                                              (@ cast_u
                                                                size32 size16
                                                                quotient)
                                                              (lambda (quotient_trunc)
                                                              (@ bind
                                                                conv_monad
                                                                (@ cast_u
                                                                  size32
                                                                  size16
                                                                  remainder)
                                                                (lambda (remainder_trunc)
                                                                (@ bind
                                                                  conv_monad
                                                                  (@ iset_op16
                                                                    seg
                                                                    quotient_trunc
                                                                    `(Reg_op
                                                                    ,`(EAX)))
                                                                  (lambda (x7)
                                                                  (@ iset_op16
                                                                    seg
                                                                    remainder_trunc
                                                                    `(Reg_op
                                                                    ,`(EDX))))))))))))))))))))))))))))))))))))))))))))
                        ((False)
                          (@ bind conv_monad
                            (@ iload_op16 seg `(Reg_op ,`(EAX)))
                            (lambda (dividend)
                            (@ bind conv_monad (@ iload_op8 seg op)
                              (lambda (divisor)
                              (@ bind conv_monad (@ load_Z size8 `(Z0))
                                (lambda (zero2)
                                (@ bind conv_monad
                                  (@ test size8 `(Eq_op) zero2 divisor)
                                  (lambda (divide_by_zero)
                                  (@ bind conv_monad (if_trap divide_by_zero)
                                    (lambda (x5)
                                    (@ bind conv_monad
                                      (@ cast_u size8 size16 divisor)
                                      (lambda (divisor_ext)
                                      (@ bind conv_monad
                                        (@ arith size16 `(Divu_op) dividend
                                          divisor_ext) (lambda (quotient)
                                        (@ bind conv_monad
                                          (@ load_Z size16 `(Zpos ,`(XI ,`(XI
                                            ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI
                                            ,`(XH))))))))))
                                          (lambda (max_quotient)
                                          (@ bind conv_monad
                                            (@ test size16 `(Ltu_op)
                                              max_quotient quotient)
                                            (lambda (div_error)
                                            (@ bind conv_monad
                                              (if_trap div_error)
                                              (lambda (x6)
                                              (@ bind conv_monad
                                                (@ arith size16 `(Modu_op)
                                                  dividend divisor_ext)
                                                (lambda (remainder)
                                                (@ bind conv_monad
                                                  (@ cast_u size16 size8
                                                    quotient)
                                                  (lambda (quotient_trunc)
                                                  (@ bind conv_monad
                                                    (@ cast_u size16 size8
                                                      remainder)
                                                    (lambda (remainder_trunc)
                                                    (@ bind conv_monad
                                                      (@ iset_op8 seg
                                                        quotient_trunc
                                                        `(Reg_op ,`(EAX)))
                                                      (lambda (x7)
                                                      (@ iset_op8 seg
                                                        remainder_trunc
                                                        `(Reg_op ,`(ESP))))))))))))))))))))))))))))))))))
                   ((False)
                     (match w
                        ((True)
                          (@ bind conv_monad
                            (@ iload_op32 seg `(Reg_op ,`(EAX)))
                            (lambda (dividend_lower)
                            (@ bind conv_monad
                              (@ iload_op32 seg `(Reg_op ,`(EDX)))
                              (lambda (dividend_upper)
                              (@ bind conv_monad
                                (@ cast_u size32 `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S
                                  ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  dividend_upper) (lambda (dividend0)
                                (@ bind conv_monad
                                  (@ load_Z `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                                    ,`(XH)))))))) (lambda (thirtytwo)
                                  (@ bind conv_monad
                                    (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S
                                      ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      `(Shl_op) dividend0 thirtytwo)
                                    (lambda (dividend1)
                                    (@ bind conv_monad
                                      (@ cast_u size32 `(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S
                                        ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        dividend_lower)
                                      (lambda (dividend_lower_ext)
                                      (@ bind conv_monad
                                        (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S
                                          ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          `(Or_op) dividend1
                                          dividend_lower_ext)
                                        (lambda (dividend)
                                        (@ bind conv_monad
                                          (@ iload_op32 seg op)
                                          (lambda (divisor)
                                          (@ bind conv_monad
                                            (@ load_Z size32 `(Z0))
                                            (lambda (zero2)
                                            (@ bind conv_monad
                                              (@ test size32 `(Eq_op) zero2
                                                divisor)
                                              (lambda (divide_by_zero)
                                              (@ bind conv_monad
                                                (if_trap divide_by_zero)
                                                (lambda (x5)
                                                (@ bind conv_monad
                                                  (@ cast_u size32 `(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S
                                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                    divisor)
                                                  (lambda (divisor_ext)
                                                  (@ bind conv_monad
                                                    (@ arith `(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                      `(Divu_op) dividend
                                                      divisor_ext)
                                                    (lambda (quotient)
                                                    (@ bind conv_monad
                                                      (@ load_Z `(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                        `(Zpos ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI
                                                        ,`(XH))))))))))))))))))))))))))))))))))
                                                      (lambda (max_quotient)
                                                      (@ bind conv_monad
                                                        (@ test `(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                          `(Ltu_op)
                                                          max_quotient
                                                          quotient)
                                                        (lambda (div_error)
                                                        (@ bind conv_monad
                                                          (if_trap div_error)
                                                          (lambda (x6)
                                                          (@ bind conv_monad
                                                            (@ arith `(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S
                                                              ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                              `(Modu_op)
                                                              dividend
                                                              divisor_ext)
                                                            (lambda (remainder)
                                                            (@ bind
                                                              conv_monad
                                                              (@ cast_u `(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(S ,`(S
                                                                ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                size32
                                                                quotient)
                                                              (lambda (quotient_trunc)
                                                              (@ bind
                                                                conv_monad
                                                                (@ cast_u `(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(S ,`(S
                                                                  ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                  size32
                                                                  remainder)
                                                                (lambda (remainder_trunc)
                                                                (@ bind
                                                                  conv_monad
                                                                  (@ iset_op32
                                                                    seg
                                                                    quotient_trunc
                                                                    `(Reg_op
                                                                    ,`(EAX)))
                                                                  (lambda (x7)
                                                                  (@ iset_op32
                                                                    seg
                                                                    remainder_trunc
                                                                    `(Reg_op
                                                                    ,`(EDX))))))))))))))))))))))))))))))))))))))))))))
                        ((False)
                          (@ bind conv_monad
                            (@ iload_op16 seg `(Reg_op ,`(EAX)))
                            (lambda (dividend)
                            (@ bind conv_monad (@ iload_op8 seg op)
                              (lambda (divisor)
                              (@ bind conv_monad (@ load_Z size8 `(Z0))
                                (lambda (zero2)
                                (@ bind conv_monad
                                  (@ test size8 `(Eq_op) zero2 divisor)
                                  (lambda (divide_by_zero)
                                  (@ bind conv_monad (if_trap divide_by_zero)
                                    (lambda (x5)
                                    (@ bind conv_monad
                                      (@ cast_u size8 size16 divisor)
                                      (lambda (divisor_ext)
                                      (@ bind conv_monad
                                        (@ arith size16 `(Divu_op) dividend
                                          divisor_ext) (lambda (quotient)
                                        (@ bind conv_monad
                                          (@ load_Z size16 `(Zpos ,`(XI ,`(XI
                                            ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI
                                            ,`(XH))))))))))
                                          (lambda (max_quotient)
                                          (@ bind conv_monad
                                            (@ test size16 `(Ltu_op)
                                              max_quotient quotient)
                                            (lambda (div_error)
                                            (@ bind conv_monad
                                              (if_trap div_error)
                                              (lambda (x6)
                                              (@ bind conv_monad
                                                (@ arith size16 `(Modu_op)
                                                  dividend divisor_ext)
                                                (lambda (remainder)
                                                (@ bind conv_monad
                                                  (@ cast_u size16 size8
                                                    quotient)
                                                  (lambda (quotient_trunc)
                                                  (@ bind conv_monad
                                                    (@ cast_u size16 size8
                                                      remainder)
                                                    (lambda (remainder_trunc)
                                                    (@ bind conv_monad
                                                      (@ iset_op8 seg
                                                        quotient_trunc
                                                        `(Reg_op ,`(EAX)))
                                                      (lambda (x7)
                                                      (@ iset_op8 seg
                                                        remainder_trunc
                                                        `(Reg_op ,`(ESP))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_IDIV (lambdas (pre w op)
  (let ((seg (@ get_segment_op pre `(DS) op)))
    (@ bind conv_monad (undef_flag `(CF)) (lambda (x)
      (@ bind conv_monad (undef_flag `(OF)) (lambda (x0)
        (@ bind conv_monad (undef_flag `(SF)) (lambda (x1)
          (@ bind conv_monad (undef_flag `(ZF)) (lambda (x2)
            (@ bind conv_monad (undef_flag `(AF)) (lambda (x3)
              (@ bind conv_monad (undef_flag `(PF)) (lambda (x4)
                (match (op_override pre)
                   ((True)
                     (match w
                        ((True)
                          (@ bind conv_monad
                            (@ iload_op16 seg `(Reg_op ,`(EAX)))
                            (lambda (dividend_lower)
                            (@ bind conv_monad
                              (@ iload_op16 seg `(Reg_op ,`(EDX)))
                              (lambda (dividend_upper)
                              (@ bind conv_monad
                                (@ cast_s size16 size32 dividend_upper)
                                (lambda (dividend0)
                                (@ bind conv_monad
                                  (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO
                                    ,`(XO ,`(XH))))))) (lambda (sixteen)
                                  (@ bind conv_monad
                                    (@ arith size32 `(Shl_op) dividend0
                                      sixteen) (lambda (dividend1)
                                    (@ bind conv_monad
                                      (@ cast_s size16 size32 dividend_lower)
                                      (lambda (dividend_lower_ext)
                                      (@ bind conv_monad
                                        (@ arith size32 `(Or_op) dividend1
                                          dividend_lower_ext)
                                        (lambda (dividend)
                                        (@ bind conv_monad
                                          (@ iload_op16 seg op)
                                          (lambda (divisor)
                                          (@ bind conv_monad
                                            (@ load_Z size16 `(Z0))
                                            (lambda (zero2)
                                            (@ bind conv_monad
                                              (@ test size16 `(Eq_op) zero2
                                                divisor)
                                              (lambda (divide_by_zero)
                                              (@ bind conv_monad
                                                (if_trap divide_by_zero)
                                                (lambda (x5)
                                                (@ bind conv_monad
                                                  (@ cast_s size16 size32
                                                    divisor)
                                                  (lambda (divisor_ext)
                                                  (@ bind conv_monad
                                                    (@ arith size32
                                                      `(Divs_op) dividend
                                                      divisor_ext)
                                                    (lambda (quotient)
                                                    (@ bind conv_monad
                                                      (@ load_Z size32 `(Zpos
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI
                                                        ,`(XH)))))))))))))))))
                                                      (lambda (max_quotient)
                                                      (@ bind conv_monad
                                                        (@ load_Z size32
                                                          `(Zneg ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO
                                                          ,`(XH))))))))))))))))))
                                                        (lambda (min_quotient)
                                                        (@ bind conv_monad
                                                          (@ test size32
                                                            `(Lt_op)
                                                            max_quotient
                                                            quotient)
                                                          (lambda (div_error0)
                                                          (@ bind conv_monad
                                                            (@ test size32
                                                              `(Lt_op)
                                                              quotient
                                                              min_quotient)
                                                            (lambda (div_error1)
                                                            (@ bind
                                                              conv_monad
                                                              (@ arith size1
                                                                `(Or_op)
                                                                div_error0
                                                                div_error1)
                                                              (lambda (div_error)
                                                              (@ bind
                                                                conv_monad
                                                                (if_trap
                                                                  div_error)
                                                                (lambda (x6)
                                                                (@ bind
                                                                  conv_monad
                                                                  (@ arith
                                                                    size32
                                                                    `(Mods_op)
                                                                    dividend
                                                                    divisor_ext)
                                                                  (lambda (remainder)
                                                                  (@ bind
                                                                    conv_monad
                                                                    (@ cast_s
                                                                    size32
                                                                    size16
                                                                    quotient)
                                                                    (lambda (quotient_trunc)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ cast_s
                                                                    size32
                                                                    size16
                                                                    remainder)
                                                                    (lambda (remainder_trunc)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ iset_op16
                                                                    seg
                                                                    quotient_trunc
                                                                    `(Reg_op
                                                                    ,`(EAX)))
                                                                    (lambda (x7)
                                                                    (@ iset_op16
                                                                    seg
                                                                    remainder_trunc
                                                                    `(Reg_op
                                                                    ,`(EDX))))))))))))))))))))))))))))))))))))))))))))))))))
                        ((False)
                          (@ bind conv_monad
                            (@ iload_op16 seg `(Reg_op ,`(EAX)))
                            (lambda (dividend)
                            (@ bind conv_monad (@ iload_op8 seg op)
                              (lambda (divisor)
                              (@ bind conv_monad (@ load_Z size8 `(Z0))
                                (lambda (zero2)
                                (@ bind conv_monad
                                  (@ test size8 `(Eq_op) zero2 divisor)
                                  (lambda (divide_by_zero)
                                  (@ bind conv_monad (if_trap divide_by_zero)
                                    (lambda (x5)
                                    (@ bind conv_monad
                                      (@ cast_s size8 size16 divisor)
                                      (lambda (divisor_ext)
                                      (@ bind conv_monad
                                        (@ arith size16 `(Divs_op) dividend
                                          divisor_ext) (lambda (quotient)
                                        (@ bind conv_monad
                                          (@ load_Z size16 `(Zpos ,`(XI ,`(XI
                                            ,`(XI ,`(XI ,`(XI ,`(XI
                                            ,`(XH)))))))))
                                          (lambda (max_quotient)
                                          (@ bind conv_monad
                                            (@ load_Z size16 `(Zneg ,`(XO
                                              ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                                              ,`(XO ,`(XH))))))))))
                                            (lambda (min_quotient)
                                            (@ bind conv_monad
                                              (@ test size16 `(Lt_op)
                                                max_quotient quotient)
                                              (lambda (div_error0)
                                              (@ bind conv_monad
                                                (@ test size16 `(Lt_op)
                                                  quotient min_quotient)
                                                (lambda (div_error1)
                                                (@ bind conv_monad
                                                  (@ arith size1 `(Or_op)
                                                    div_error0 div_error1)
                                                  (lambda (div_error)
                                                  (@ bind conv_monad
                                                    (if_trap div_error)
                                                    (lambda (x6)
                                                    (@ bind conv_monad
                                                      (@ arith size16
                                                        `(Mods_op) dividend
                                                        divisor_ext)
                                                      (lambda (remainder)
                                                      (@ bind conv_monad
                                                        (@ cast_s size16
                                                          size8 quotient)
                                                        (lambda (quotient_trunc)
                                                        (@ bind conv_monad
                                                          (@ cast_s size16
                                                            size8 remainder)
                                                          (lambda (remainder_trunc)
                                                          (@ bind conv_monad
                                                            (@ iset_op8 seg
                                                              quotient_trunc
                                                              `(Reg_op
                                                              ,`(EAX)))
                                                            (lambda (x7)
                                                            (@ iset_op8 seg
                                                              remainder_trunc
                                                              `(Reg_op
                                                              ,`(ESP))))))))))))))))))))))))))))))))))))))))
                   ((False)
                     (match w
                        ((True)
                          (@ bind conv_monad
                            (@ iload_op32 seg `(Reg_op ,`(EAX)))
                            (lambda (dividend_lower)
                            (@ bind conv_monad
                              (@ iload_op32 seg `(Reg_op ,`(EDX)))
                              (lambda (dividend_upper)
                              (@ bind conv_monad
                                (@ cast_s size32 `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S
                                  ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  dividend_upper) (lambda (dividend0)
                                (@ bind conv_monad
                                  (@ load_Z `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                                    ,`(XH)))))))) (lambda (thirtytwo)
                                  (@ bind conv_monad
                                    (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S
                                      ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      `(Shl_op) dividend0 thirtytwo)
                                    (lambda (dividend1)
                                    (@ bind conv_monad
                                      (@ cast_s size32 `(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S
                                        ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        dividend_lower)
                                      (lambda (dividend_lower_ext)
                                      (@ bind conv_monad
                                        (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S
                                          ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          `(Or_op) dividend1
                                          dividend_lower_ext)
                                        (lambda (dividend)
                                        (@ bind conv_monad
                                          (@ iload_op32 seg op)
                                          (lambda (divisor)
                                          (@ bind conv_monad
                                            (@ load_Z size32 `(Z0))
                                            (lambda (zero2)
                                            (@ bind conv_monad
                                              (@ test size32 `(Eq_op) zero2
                                                divisor)
                                              (lambda (divide_by_zero)
                                              (@ bind conv_monad
                                                (if_trap divide_by_zero)
                                                (lambda (x5)
                                                (@ bind conv_monad
                                                  (@ cast_s size32 `(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S ,`(S ,`(S ,`(S ,`(S
                                                    ,`(S
                                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                    divisor)
                                                  (lambda (divisor_ext)
                                                  (@ bind conv_monad
                                                    (@ arith `(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(S ,`(S ,`(S ,`(S
                                                      ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                      `(Divs_op) dividend
                                                      divisor_ext)
                                                    (lambda (quotient)
                                                    (@ bind conv_monad
                                                      (@ load_Z `(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(S ,`(S ,`(S ,`(S
                                                        ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                        `(Zpos ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI ,`(XI ,`(XI
                                                        ,`(XI
                                                        ,`(XH)))))))))))))))))))))))))))))))))
                                                      (lambda (max_quotient)
                                                      (@ bind conv_monad
                                                        (@ load_Z `(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S ,`(S ,`(S ,`(S
                                                          ,`(S
                                                          ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                          `(Zneg ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO ,`(XO
                                                          ,`(XO ,`(XO
                                                          ,`(XH))))))))))))))))))))))))))))))))))
                                                        (lambda (min_quotient)
                                                        (@ bind conv_monad
                                                          (@ test `(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S ,`(S ,`(S
                                                            ,`(S
                                                            ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                            `(Lt_op)
                                                            max_quotient
                                                            quotient)
                                                          (lambda (div_error0)
                                                          (@ bind conv_monad
                                                            (@ test `(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S ,`(S ,`(S
                                                              ,`(S
                                                              ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                              `(Lt_op)
                                                              quotient
                                                              min_quotient)
                                                            (lambda (div_error1)
                                                            (@ bind
                                                              conv_monad
                                                              (@ arith size1
                                                                `(Or_op)
                                                                div_error0
                                                                div_error1)
                                                              (lambda (div_error)
                                                              (@ bind
                                                                conv_monad
                                                                (if_trap
                                                                  div_error)
                                                                (lambda (x6)
                                                                (@ bind
                                                                  conv_monad
                                                                  (@ arith
                                                                    `(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S
                                                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    `(Mods_op)
                                                                    dividend
                                                                    divisor_ext)
                                                                  (lambda (remainder)
                                                                  (@ bind
                                                                    conv_monad
                                                                    (@ cast_s
                                                                    `(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S
                                                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    size32
                                                                    quotient)
                                                                    (lambda (quotient_trunc)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ cast_s
                                                                    `(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S ,`(S
                                                                    ,`(S
                                                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    size32
                                                                    remainder)
                                                                    (lambda (remainder_trunc)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ iset_op32
                                                                    seg
                                                                    quotient_trunc
                                                                    `(Reg_op
                                                                    ,`(EAX)))
                                                                    (lambda (x7)
                                                                    (@ iset_op32
                                                                    seg
                                                                    remainder_trunc
                                                                    `(Reg_op
                                                                    ,`(EDX))))))))))))))))))))))))))))))))))))))))))))))))))
                        ((False)
                          (@ bind conv_monad
                            (@ iload_op16 seg `(Reg_op ,`(EAX)))
                            (lambda (dividend)
                            (@ bind conv_monad (@ iload_op8 seg op)
                              (lambda (divisor)
                              (@ bind conv_monad (@ load_Z size8 `(Z0))
                                (lambda (zero2)
                                (@ bind conv_monad
                                  (@ test size8 `(Eq_op) zero2 divisor)
                                  (lambda (divide_by_zero)
                                  (@ bind conv_monad (if_trap divide_by_zero)
                                    (lambda (x5)
                                    (@ bind conv_monad
                                      (@ cast_s size8 size16 divisor)
                                      (lambda (divisor_ext)
                                      (@ bind conv_monad
                                        (@ arith size16 `(Divs_op) dividend
                                          divisor_ext) (lambda (quotient)
                                        (@ bind conv_monad
                                          (@ load_Z size16 `(Zpos ,`(XI ,`(XI
                                            ,`(XI ,`(XI ,`(XI ,`(XI
                                            ,`(XH)))))))))
                                          (lambda (max_quotient)
                                          (@ bind conv_monad
                                            (@ load_Z size16 `(Zneg ,`(XO
                                              ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                                              ,`(XO ,`(XH))))))))))
                                            (lambda (min_quotient)
                                            (@ bind conv_monad
                                              (@ test size16 `(Lt_op)
                                                max_quotient quotient)
                                              (lambda (div_error0)
                                              (@ bind conv_monad
                                                (@ test size16 `(Lt_op)
                                                  quotient min_quotient)
                                                (lambda (div_error1)
                                                (@ bind conv_monad
                                                  (@ arith size1 `(Or_op)
                                                    div_error0 div_error1)
                                                  (lambda (div_error)
                                                  (@ bind conv_monad
                                                    (if_trap div_error)
                                                    (lambda (x6)
                                                    (@ bind conv_monad
                                                      (@ arith size16
                                                        `(Mods_op) dividend
                                                        divisor_ext)
                                                      (lambda (remainder)
                                                      (@ bind conv_monad
                                                        (@ cast_s size16
                                                          size8 quotient)
                                                        (lambda (quotient_trunc)
                                                        (@ bind conv_monad
                                                          (@ cast_s size16
                                                            size8 remainder)
                                                          (lambda (remainder_trunc)
                                                          (@ bind conv_monad
                                                            (@ iset_op8 seg
                                                              quotient_trunc
                                                              `(Reg_op
                                                              ,`(EAX)))
                                                            (lambda (x7)
                                                            (@ iset_op8 seg
                                                              remainder_trunc
                                                              `(Reg_op
                                                              ,`(ESP))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_IMUL (lambdas (pre w op1 opopt2 iopt)
  (@ bind conv_monad (undef_flag `(SF)) (lambda (x)
    (@ bind conv_monad (undef_flag `(ZF)) (lambda (x0)
      (@ bind conv_monad (undef_flag `(AF)) (lambda (x1)
        (@ bind conv_monad (undef_flag `(PF)) (lambda (x2)
          (match opopt2
             ((Some op2)
               (match iopt
                  ((Some imm3)
                    (let ((load (@ load_op pre w)))
                      (let ((set2 (@ set_op pre w)))
                        (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
                          (@ bind conv_monad (@ load seg op2) (lambda (p1)
                            (@ bind conv_monad
                              (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(O)))))))))))))))))))))))))))))))) imm3)
                              (lambda (p2)
                              (@ bind conv_monad
                                (@ cast_s (@ opsize (op_override pre) w)
                                  (@ minus
                                    (@ mult `(S ,`(S ,`(O)))
                                      (@ plus (@ opsize (op_override pre) w)
                                        `(S ,`(O)))) `(S ,`(O))) p1)
                                (lambda (p1ext)
                                (@ bind conv_monad
                                  (@ cast_s `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(O))))))))))))))))))))))))))))))))
                                    (@ minus
                                      (@ mult `(S ,`(S ,`(O)))
                                        (@ plus
                                          (@ opsize (op_override pre) w) `(S
                                          ,`(O)))) `(S ,`(O))) p2)
                                  (lambda (p2ext)
                                  (@ bind conv_monad
                                    (@ arith
                                      (@ minus
                                        (@ mult `(S ,`(S ,`(O)))
                                          (@ plus
                                            (@ opsize (op_override pre) w)
                                            `(S ,`(O)))) `(S ,`(O)))
                                      `(Mul_op) p1ext p2ext) (lambda (res)
                                    (@ bind conv_monad
                                      (@ cast_s
                                        (@ minus
                                          (@ mult `(S ,`(S ,`(O)))
                                            (@ plus
                                              (@ opsize (op_override pre) w)
                                              `(S ,`(O)))) `(S ,`(O)))
                                        (@ opsize (op_override pre) w) res)
                                      (lambda (lowerhalf)
                                      (@ bind conv_monad
                                        (@ cast_s
                                          (@ opsize (op_override pre) w)
                                          (@ minus
                                            (@ mult `(S ,`(S ,`(O)))
                                              (@ plus
                                                (@ opsize (op_override pre)
                                                  w) `(S ,`(O)))) `(S ,`(O)))
                                          lowerhalf) (lambda (reextend)
                                        (@ bind conv_monad
                                          (@ test
                                            (@ minus
                                              (@ mult `(S ,`(S ,`(O)))
                                                (@ plus
                                                  (@ opsize (op_override pre)
                                                    w) `(S ,`(O)))) `(S
                                              ,`(O))) `(Eq_op) reextend res)
                                          (lambda (b0)
                                          (@ bind conv_monad
                                            (@ not0 size1 b0) (lambda (flag)
                                            (@ bind conv_monad
                                              (@ set_flag `(CF) flag)
                                              (lambda (x3)
                                              (@ bind conv_monad
                                                (@ set_flag `(OF) flag)
                                                (lambda (x4)
                                                (@ set2 seg lowerhalf op1)))))))))))))))))))))))))))
                  ((None)
                    (let ((load (@ load_op pre w)))
                      (let ((set2 (@ set_op pre w)))
                        (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
                          (@ bind conv_monad (@ load seg op1) (lambda (p1)
                            (@ bind conv_monad (@ load seg op2) (lambda (p2)
                              (@ bind conv_monad
                                (@ cast_s (@ opsize (op_override pre) w)
                                  (@ minus
                                    (@ mult `(S ,`(S ,`(O)))
                                      (@ plus (@ opsize (op_override pre) w)
                                        `(S ,`(O)))) `(S ,`(O))) p1)
                                (lambda (p1ext)
                                (@ bind conv_monad
                                  (@ cast_s (@ opsize (op_override pre) w)
                                    (@ minus
                                      (@ mult `(S ,`(S ,`(O)))
                                        (@ plus
                                          (@ opsize (op_override pre) w) `(S
                                          ,`(O)))) `(S ,`(O))) p2)
                                  (lambda (p2ext)
                                  (@ bind conv_monad
                                    (@ arith
                                      (@ minus
                                        (@ mult `(S ,`(S ,`(O)))
                                          (@ plus
                                            (@ opsize (op_override pre) w)
                                            `(S ,`(O)))) `(S ,`(O)))
                                      `(Mul_op) p1ext p2ext) (lambda (res)
                                    (@ bind conv_monad
                                      (@ cast_s
                                        (@ minus
                                          (@ mult `(S ,`(S ,`(O)))
                                            (@ plus
                                              (@ opsize (op_override pre) w)
                                              `(S ,`(O)))) `(S ,`(O)))
                                        (@ opsize (op_override pre) w) res)
                                      (lambda (lowerhalf)
                                      (@ bind conv_monad
                                        (@ cast_s
                                          (@ opsize (op_override pre) w)
                                          (@ minus
                                            (@ mult `(S ,`(S ,`(O)))
                                              (@ plus
                                                (@ opsize (op_override pre)
                                                  w) `(S ,`(O)))) `(S ,`(O)))
                                          lowerhalf) (lambda (reextend)
                                        (@ bind conv_monad
                                          (@ test
                                            (@ minus
                                              (@ mult `(S ,`(S ,`(O)))
                                                (@ plus
                                                  (@ opsize (op_override pre)
                                                    w) `(S ,`(O)))) `(S
                                              ,`(O))) `(Eq_op) reextend res)
                                          (lambda (b0)
                                          (@ bind conv_monad
                                            (@ not0 size1 b0) (lambda (flag)
                                            (@ bind conv_monad
                                              (@ set_flag `(CF) flag)
                                              (lambda (x3)
                                              (@ bind conv_monad
                                                (@ set_flag `(OF) flag)
                                                (lambda (x4)
                                                (@ set2 seg lowerhalf op1)))))))))))))))))))))))))))))
             ((None)
               (let ((load (@ load_op pre w)))
                 (let ((seg (@ get_segment_op pre `(DS) op1)))
                   (@ bind conv_monad (@ load seg `(Reg_op ,`(EAX)))
                     (lambda (p1)
                     (@ bind conv_monad (@ load seg op1) (lambda (p2)
                       (@ bind conv_monad
                         (@ cast_s (@ opsize (op_override pre) w)
                           (@ minus
                             (@ mult `(S ,`(S ,`(O)))
                               (@ plus (@ opsize (op_override pre) w) `(S
                                 ,`(O)))) `(S ,`(O))) p1) (lambda (p1ext)
                         (@ bind conv_monad
                           (@ cast_s (@ opsize (op_override pre) w)
                             (@ minus
                               (@ mult `(S ,`(S ,`(O)))
                                 (@ plus (@ opsize (op_override pre) w) `(S
                                   ,`(O)))) `(S ,`(O))) p2) (lambda (p2ext)
                           (@ bind conv_monad
                             (@ arith
                               (@ minus
                                 (@ mult `(S ,`(S ,`(O)))
                                   (@ plus (@ opsize (op_override pre) w) `(S
                                     ,`(O)))) `(S ,`(O))) `(Mul_op) p1ext
                               p2ext) (lambda (res)
                             (@ bind conv_monad
                               (@ cast_s
                                 (@ minus
                                   (@ mult `(S ,`(S ,`(O)))
                                     (@ plus (@ opsize (op_override pre) w)
                                       `(S ,`(O)))) `(S ,`(O)))
                                 (@ opsize (op_override pre) w) res)
                               (lambda (lowerhalf)
                               (@ bind conv_monad
                                 (@ load_Z
                                   (@ minus
                                     (@ mult `(S ,`(S ,`(O)))
                                       (@ plus (@ opsize (op_override pre) w)
                                         `(S ,`(O)))) `(S ,`(O)))
                                   (of_nat1
                                     (@ plus (@ opsize (op_override pre) w)
                                       `(S ,`(O))))) (lambda (shift)
                                 (@ bind conv_monad
                                   (@ arith
                                     (@ minus
                                       (@ mult `(S ,`(S ,`(O)))
                                         (@ plus
                                           (@ opsize (op_override pre) w) `(S
                                           ,`(O)))) `(S ,`(O))) `(Shr_op) res
                                     shift) (lambda (res_shifted)
                                   (@ bind conv_monad
                                     (@ cast_s
                                       (@ minus
                                         (@ mult `(S ,`(S ,`(O)))
                                           (@ plus
                                             (@ opsize (op_override pre) w)
                                             `(S ,`(O)))) `(S ,`(O)))
                                       (@ opsize (op_override pre) w)
                                       res_shifted) (lambda (upperhalf)
                                     (@ bind conv_monad
                                       (@ load_Z
                                         (@ opsize (op_override pre) w)
                                         `(Z0)) (lambda (zero2)
                                       (@ bind conv_monad
                                         (@ load_Z
                                           (@ opsize (op_override pre) w)
                                           (max_unsigned
                                             (@ opsize (op_override pre) w)))
                                         (lambda (max2)
                                         (@ bind conv_monad
                                           (@ test
                                             (@ opsize (op_override pre) w)
                                             `(Eq_op) upperhalf zero2)
                                           (lambda (b0)
                                           (@ bind conv_monad
                                             (@ test
                                               (@ opsize (op_override pre) w)
                                               `(Eq_op) upperhalf max2)
                                             (lambda (b1)
                                             (@ bind conv_monad
                                               (@ arith size1 `(Or_op) b0 b1)
                                               (lambda (b2)
                                               (@ bind conv_monad
                                                 (@ not0 size1 b2)
                                                 (lambda (flag)
                                                 (@ bind conv_monad
                                                   (@ set_flag `(CF) flag)
                                                   (lambda (x3)
                                                   (@ bind conv_monad
                                                     (@ set_flag `(OF) flag)
                                                     (lambda (x4)
                                                     (match w
                                                        ((True)
                                                          (let ((set2
                                                            (@ set_op pre w)))
                                                            (@ bind
                                                              conv_monad
                                                              (@ set2 seg
                                                                lowerhalf
                                                                `(Reg_op
                                                                ,`(EAX)))
                                                              (lambda (x5)
                                                              (@ set2 seg
                                                                upperhalf
                                                                `(Reg_op
                                                                ,`(EDX)))))))
                                                        ((False)
                                                          (@ iset_op16 seg
                                                            res `(Reg_op
                                                            ,`(EAX)))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_MUL (lambdas (pre w op)
  (let ((seg (@ get_segment_op pre `(DS) op)))
    (@ bind conv_monad (undef_flag `(SF)) (lambda (x)
      (@ bind conv_monad (undef_flag `(ZF)) (lambda (x0)
        (@ bind conv_monad (undef_flag `(AF)) (lambda (x1)
          (@ bind conv_monad (undef_flag `(PF)) (lambda (x2)
            (match (op_override pre)
               ((True)
                 (match w
                    ((True)
                      (@ bind conv_monad (@ iload_op16 seg op) (lambda (p1)
                        (@ bind conv_monad
                          (@ iload_op16 seg `(Reg_op ,`(EAX))) (lambda (p2)
                          (@ bind conv_monad (@ cast_u size16 size32 p1)
                            (lambda (p1ext)
                            (@ bind conv_monad (@ cast_u size16 size32 p2)
                              (lambda (p2ext)
                              (@ bind conv_monad
                                (@ arith size32 `(Mul_op) p1ext p2ext)
                                (lambda (res)
                                (@ bind conv_monad
                                  (@ cast_u size32 size16 res)
                                  (lambda (res_lower)
                                  (@ bind conv_monad
                                    (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO
                                      ,`(XO ,`(XH))))))) (lambda (sixteen)
                                    (@ bind conv_monad
                                      (@ arith size32 `(Shru_op) res sixteen)
                                      (lambda (res_shifted)
                                      (@ bind conv_monad
                                        (@ cast_u size32 size16 res_shifted)
                                        (lambda (res_upper)
                                        (@ bind conv_monad
                                          (@ iset_op16 seg res_lower `(Reg_op
                                            ,`(EAX))) (lambda (x3)
                                          (@ bind conv_monad
                                            (@ iset_op16 seg res_upper
                                              `(Reg_op ,`(EDX))) (lambda (x4)
                                            (@ bind conv_monad
                                              (@ load_Z size16 `(Z0))
                                              (lambda (zero2)
                                              (@ bind conv_monad
                                                (@ test size16 `(Ltu_op)
                                                  zero2 res_upper)
                                                (lambda (cf_test)
                                                (@ bind conv_monad
                                                  (@ set_flag `(CF) cf_test)
                                                  (lambda (x5)
                                                  (@ set_flag `(OF) cf_test))))))))))))))))))))))))))))))
                    ((False)
                      (@ bind conv_monad (@ iload_op8 seg op) (lambda (p1)
                        (@ bind conv_monad
                          (@ iload_op8 seg `(Reg_op ,`(EAX))) (lambda (p2)
                          (@ bind conv_monad (@ cast_u size8 size16 p1)
                            (lambda (p1ext)
                            (@ bind conv_monad (@ cast_u size8 size16 p2)
                              (lambda (p2ext)
                              (@ bind conv_monad
                                (@ arith size16 `(Mul_op) p1ext p2ext)
                                (lambda (res)
                                (@ bind conv_monad
                                  (@ iset_op16 seg res `(Reg_op ,`(EAX)))
                                  (lambda (x3)
                                  (@ bind conv_monad
                                    (@ load_Z size16 `(Zpos ,`(XI ,`(XI ,`(XI
                                      ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH))))))))))
                                    (lambda (max2)
                                    (@ bind conv_monad
                                      (@ test size16 `(Ltu_op) max2 res)
                                      (lambda (cf_test)
                                      (@ bind conv_monad
                                        (@ set_flag `(CF) cf_test)
                                        (lambda (x4)
                                        (@ set_flag `(OF) cf_test))))))))))))))))))))))
               ((False)
                 (match w
                    ((True)
                      (@ bind conv_monad (@ iload_op32 seg op) (lambda (p1)
                        (@ bind conv_monad
                          (@ iload_op32 seg `(Reg_op ,`(EAX))) (lambda (p2)
                          (@ bind conv_monad
                            (@ cast_u size32 `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                              ,`(S ,`(S ,`(S
                              ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                              p1) (lambda (p1ext)
                            (@ bind conv_monad
                              (@ cast_u size32 `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S
                                ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                p2) (lambda (p2ext)
                              (@ bind conv_monad
                                (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  `(Mul_op) p1ext p2ext) (lambda (res)
                                (@ bind conv_monad
                                  (@ cast_u `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    size32 res) (lambda (res_lower)
                                  (@ bind conv_monad
                                    (@ load_Z `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S
                                      ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                                      ,`(XH)))))))) (lambda (thirtytwo)
                                    (@ bind conv_monad
                                      (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S
                                        ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        `(Shru_op) res thirtytwo)
                                      (lambda (res_shifted)
                                      (@ bind conv_monad
                                        (@ cast_u `(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S
                                          ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          size32 res_shifted)
                                        (lambda (res_upper)
                                        (@ bind conv_monad
                                          (@ iset_op32 seg res_lower `(Reg_op
                                            ,`(EAX))) (lambda (x3)
                                          (@ bind conv_monad
                                            (@ iset_op32 seg res_upper
                                              `(Reg_op ,`(EDX))) (lambda (x4)
                                            (@ bind conv_monad
                                              (@ load_Z size32 `(Z0))
                                              (lambda (zero2)
                                              (@ bind conv_monad
                                                (@ test size32 `(Ltu_op)
                                                  zero2 res_upper)
                                                (lambda (cf_test)
                                                (@ bind conv_monad
                                                  (@ set_flag `(CF) cf_test)
                                                  (lambda (x5)
                                                  (@ set_flag `(OF) cf_test))))))))))))))))))))))))))))))
                    ((False)
                      (@ bind conv_monad (@ iload_op8 seg op) (lambda (p1)
                        (@ bind conv_monad
                          (@ iload_op8 seg `(Reg_op ,`(EAX))) (lambda (p2)
                          (@ bind conv_monad (@ cast_u size8 size16 p1)
                            (lambda (p1ext)
                            (@ bind conv_monad (@ cast_u size8 size16 p2)
                              (lambda (p2ext)
                              (@ bind conv_monad
                                (@ arith size16 `(Mul_op) p1ext p2ext)
                                (lambda (res)
                                (@ bind conv_monad
                                  (@ iset_op16 seg res `(Reg_op ,`(EAX)))
                                  (lambda (x3)
                                  (@ bind conv_monad
                                    (@ load_Z size16 `(Zpos ,`(XI ,`(XI ,`(XI
                                      ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH))))))))))
                                    (lambda (max2)
                                    (@ bind conv_monad
                                      (@ test size16 `(Ltu_op) max2 res)
                                      (lambda (cf_test)
                                      (@ bind conv_monad
                                        (@ set_flag `(CF) cf_test)
                                        (lambda (x4)
                                        (@ set_flag `(OF) cf_test))))))))))))))))))))))))))))))))))

(define conv_shift (lambdas (shift pre w op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op pre `(DS) op1)))
        (@ bind conv_monad (undef_flag `(OF)) (lambda (x)
          (@ bind conv_monad (undef_flag `(CF)) (lambda (x0)
            (@ bind conv_monad (undef_flag `(SF)) (lambda (x1)
              (@ bind conv_monad (undef_flag `(ZF)) (lambda (x2)
                (@ bind conv_monad (undef_flag `(PF)) (lambda (x3)
                  (@ bind conv_monad (undef_flag `(AF)) (lambda (x4)
                    (@ bind conv_monad (@ load seg op1) (lambda (p1)
                      (@ bind conv_monad
                        (match op2
                           ((Reg_ri r) (@ iload_op8 seg `(Reg_op ,r)))
                           ((Imm_ri i)
                             (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                               ,`(O)))))))) i))) (lambda (p2)
                        (@ bind conv_monad
                          (@ load_Z size8 `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI
                            ,`(XH))))))) (lambda (mask)
                          (@ bind conv_monad
                            (@ arith size8 `(And_op) p2 mask) (lambda (p3)
                            (@ bind conv_monad
                              (@ cast_u size8 (@ opsize (op_override pre) w)
                                p3) (lambda (p2cast)
                              (@ bind conv_monad
                                (@ arith (@ opsize (op_override pre) w) shift
                                  p1 p2cast) (lambda (p4)
                                (@ set2 seg p4 op1))))))))))))))))))))))))))))))

(define conv_SHL (lambdas (pre w op1 op2)
  (@ conv_shift `(Shl_op) pre w op1 op2)))

(define conv_SAR (lambdas (pre w op1 op2)
  (@ conv_shift `(Shr_op) pre w op1 op2)))

(define conv_SHR (lambdas (pre w op1 op2)
  (@ conv_shift `(Shru_op) pre w op1 op2)))

(define conv_ROR (lambdas (pre w op1 op2)
  (@ conv_shift `(Ror_op) pre w op1 op2)))

(define conv_ROL (lambdas (pre w op1 op2)
  (@ conv_shift `(Rol_op) pre w op1 op2)))

(define conv_RCL (lambdas (pre w op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op pre `(DS) op1)))
        (@ bind conv_monad (@ load seg op1) (lambda (p1)
          (@ bind conv_monad
            (match op2
               ((Reg_ri r) (@ iload_op8 seg `(Reg_op ,r)))
               ((Imm_ri i)
                 (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))
                   i))) (lambda (p2)
            (@ bind conv_monad
              (@ load_Z size8 `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH)))))))
              (lambda (mask)
              (@ bind conv_monad (@ arith size8 `(And_op) p2 mask)
                (lambda (p3)
                (@ bind conv_monad
                  (match (@ opsize (op_override pre) w)
                     ((O) no_op)
                     ((S n)
                       (match n
                          ((O) no_op)
                          ((S n0)
                            (match n0
                               ((O) no_op)
                               ((S n1)
                                 (match n1
                                    ((O) no_op)
                                    ((S n2)
                                      (match n2
                                         ((O) no_op)
                                         ((S n3)
                                           (match n3
                                              ((O) no_op)
                                              ((S n4)
                                                (match n4
                                                   ((O) no_op)
                                                   ((S n5)
                                                     (match n5
                                                        ((O)
                                                          (@ bind conv_monad
                                                            (@ load_Z size8
                                                              `(Zpos ,`(XI
                                                              ,`(XO ,`(XO
                                                              ,`(XH))))))
                                                            (lambda (modmask)
                                                            (@ bind
                                                              conv_monad
                                                              (@ arith size8
                                                                `(Modu_op) p3
                                                                modmask)
                                                              (lambda (p4)
                                                              no_op)))))
                                                        ((S n6)
                                                          (match n6
                                                             ((O) no_op)
                                                             ((S n7)
                                                               (match n7
                                                                  ((O) no_op)
                                                                  ((S n8)
                                                                    (match n8
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n9)
                                                                    (match n9
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n10)
                                                                    (match n10
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n11)
                                                                    (match n11
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n12)
                                                                    (match n12
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n13)
                                                                    (match n13
                                                                    ((O)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ load_Z
                                                                    size8
                                                                    `(Zpos
                                                                    ,`(XI
                                                                    ,`(XO
                                                                    ,`(XO
                                                                    ,`(XO
                                                                    ,`(XH)))))))
                                                                    (lambda (modmask)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ arith
                                                                    size8
                                                                    `(Modu_op)
                                                                    p3
                                                                    modmask)
                                                                    (lambda (p4)
                                                                    no_op)))))
                                                                    ((S n14)
                                                                    no_op))))))))))))))))))))))))))))))))
                  (lambda (x)
                  (@ bind conv_monad
                    (@ cast_u size8
                      (@ plus (@ opsize (op_override pre) w) `(S ,`(O))) p3)
                    (lambda (p2cast)
                    (@ bind conv_monad
                      (@ cast_u (@ opsize (op_override pre) w)
                        (@ plus (@ opsize (op_override pre) w) `(S ,`(O)))
                        p1) (lambda (tmp)
                      (@ bind conv_monad (get_flag `(CF)) (lambda (cf)
                        (@ bind conv_monad
                          (@ cast_u size1
                            (@ plus (@ opsize (op_override pre) w) `(S
                              ,`(O))) cf) (lambda (cf0)
                          (@ bind conv_monad
                            (@ load_Z
                              (@ plus (@ opsize (op_override pre) w) `(S
                                ,`(O)))
                              (of_nat1
                                (@ plus (@ opsize (op_override pre) w) `(S
                                  ,`(O))))) (lambda (tt)
                            (@ bind conv_monad
                              (@ arith
                                (@ plus (@ opsize (op_override pre) w) `(S
                                  ,`(O))) `(Shl_op) cf0 tt) (lambda (cf1)
                              (@ bind conv_monad
                                (@ arith
                                  (@ plus (@ opsize (op_override pre) w) `(S
                                    ,`(O))) `(Or_op) tmp cf1) (lambda (tmp0)
                                (@ bind conv_monad
                                  (@ arith
                                    (@ plus (@ opsize (op_override pre) w)
                                      `(S ,`(O))) `(Rol_op) tmp0 p2cast)
                                  (lambda (tmp1)
                                  (@ bind conv_monad
                                    (@ cast_u
                                      (@ plus (@ opsize (op_override pre) w)
                                        `(S ,`(O)))
                                      (@ opsize (op_override pre) w) tmp1)
                                    (lambda (p4)
                                    (@ bind conv_monad
                                      (@ arith
                                        (@ plus
                                          (@ opsize (op_override pre) w) `(S
                                          ,`(O))) `(Shr_op) tmp1 tt)
                                      (lambda (cf2)
                                      (@ bind conv_monad
                                        (@ cast_u
                                          (@ plus
                                            (@ opsize (op_override pre) w)
                                            `(S ,`(O))) size1 cf2)
                                        (lambda (cf3)
                                        (@ bind conv_monad (undef_flag `(OF))
                                          (lambda (x0)
                                          (@ bind conv_monad
                                            (@ set_flag `(CF) cf3)
                                            (lambda (x1)
                                            (@ set2 seg p4 op1))))))))))))))))))))))))))))))))))))))))))

(define conv_RCR (lambdas (pre w op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op pre `(DS) op1)))
        (@ bind conv_monad (@ load seg op1) (lambda (p1)
          (@ bind conv_monad
            (match op2
               ((Reg_ri r) (@ iload_op8 seg `(Reg_op ,r)))
               ((Imm_ri i)
                 (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))
                   i))) (lambda (p2)
            (@ bind conv_monad
              (@ load_Z size8 `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH)))))))
              (lambda (mask)
              (@ bind conv_monad (@ arith size8 `(And_op) p2 mask)
                (lambda (p3)
                (@ bind conv_monad
                  (match (@ opsize (op_override pre) w)
                     ((O) no_op)
                     ((S n)
                       (match n
                          ((O) no_op)
                          ((S n0)
                            (match n0
                               ((O) no_op)
                               ((S n1)
                                 (match n1
                                    ((O) no_op)
                                    ((S n2)
                                      (match n2
                                         ((O) no_op)
                                         ((S n3)
                                           (match n3
                                              ((O) no_op)
                                              ((S n4)
                                                (match n4
                                                   ((O) no_op)
                                                   ((S n5)
                                                     (match n5
                                                        ((O)
                                                          (@ bind conv_monad
                                                            (@ load_Z size8
                                                              `(Zpos ,`(XI
                                                              ,`(XO ,`(XO
                                                              ,`(XH))))))
                                                            (lambda (modmask)
                                                            (@ bind
                                                              conv_monad
                                                              (@ arith size8
                                                                `(Modu_op) p3
                                                                modmask)
                                                              (lambda (p4)
                                                              no_op)))))
                                                        ((S n6)
                                                          (match n6
                                                             ((O) no_op)
                                                             ((S n7)
                                                               (match n7
                                                                  ((O) no_op)
                                                                  ((S n8)
                                                                    (match n8
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n9)
                                                                    (match n9
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n10)
                                                                    (match n10
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n11)
                                                                    (match n11
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n12)
                                                                    (match n12
                                                                    ((O)
                                                                    no_op)
                                                                    ((S n13)
                                                                    (match n13
                                                                    ((O)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ load_Z
                                                                    size8
                                                                    `(Zpos
                                                                    ,`(XI
                                                                    ,`(XO
                                                                    ,`(XO
                                                                    ,`(XO
                                                                    ,`(XH)))))))
                                                                    (lambda (modmask)
                                                                    (@ bind
                                                                    conv_monad
                                                                    (@ arith
                                                                    size8
                                                                    `(Modu_op)
                                                                    p3
                                                                    modmask)
                                                                    (lambda (p4)
                                                                    no_op)))))
                                                                    ((S n14)
                                                                    no_op))))))))))))))))))))))))))))))))
                  (lambda (x)
                  (@ bind conv_monad
                    (@ cast_u size8
                      (@ plus (@ opsize (op_override pre) w) `(S ,`(O))) p3)
                    (lambda (p2cast)
                    (@ bind conv_monad
                      (@ load_Z
                        (@ plus (@ opsize (op_override pre) w) `(S ,`(O)))
                        `(Zpos ,`(XH))) (lambda (oneshift)
                      (@ bind conv_monad
                        (@ cast_u (@ opsize (op_override pre) w)
                          (@ plus (@ opsize (op_override pre) w) `(S ,`(O)))
                          p1) (lambda (tmp)
                        (@ bind conv_monad
                          (@ arith
                            (@ plus (@ opsize (op_override pre) w) `(S
                              ,`(O))) `(Shl_op) tmp oneshift) (lambda (tmp0)
                          (@ bind conv_monad (get_flag `(CF)) (lambda (cf)
                            (@ bind conv_monad
                              (@ cast_u size1
                                (@ plus (@ opsize (op_override pre) w) `(S
                                  ,`(O))) cf) (lambda (cf0)
                              (@ bind conv_monad
                                (@ arith
                                  (@ plus (@ opsize (op_override pre) w) `(S
                                    ,`(O))) `(Or_op) tmp0 cf0) (lambda (tmp1)
                                (@ bind conv_monad
                                  (@ arith
                                    (@ plus (@ opsize (op_override pre) w)
                                      `(S ,`(O))) `(Ror_op) tmp1 p2cast)
                                  (lambda (tmp2)
                                  (@ bind conv_monad
                                    (@ cast_u
                                      (@ plus (@ opsize (op_override pre) w)
                                        `(S ,`(O))) size1 tmp2) (lambda (cf1)
                                    (@ bind conv_monad
                                      (@ arith
                                        (@ plus
                                          (@ opsize (op_override pre) w) `(S
                                          ,`(O))) `(Shr_op) tmp2 oneshift)
                                      (lambda (p4)
                                      (@ bind conv_monad
                                        (@ cast_u
                                          (@ plus
                                            (@ opsize (op_override pre) w)
                                            `(S ,`(O)))
                                          (@ opsize (op_override pre) w) p4)
                                        (lambda (p5)
                                        (@ bind conv_monad (undef_flag `(OF))
                                          (lambda (x0)
                                          (@ bind conv_monad
                                            (@ set_flag `(CF) cf1)
                                            (lambda (x1)
                                            (@ set2 seg p5 op1))))))))))))))))))))))))))))))))))))))))))

(define conv_SHLD (lambdas (pre op1 r ri)
  (let ((load (@ load_op pre `(True))))
    (let ((set2 (@ set_op pre `(True))))
      (let ((seg (@ get_segment_op pre `(DS) op1)))
        (@ bind conv_monad
          (match ri
             ((Reg_ri r2) (@ iload_op8 seg `(Reg_op ,r2)))
             ((Imm_ri i)
               (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))) i)))
          (lambda (count)
          (@ bind conv_monad
            (@ load_Z size8 `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
              ,`(XH)))))))) (lambda (thirtytwo)
            (@ bind conv_monad (@ arith size8 `(Modu_op) count thirtytwo)
              (lambda (count0)
              (@ bind conv_monad (undef_flag `(CF)) (lambda (x)
                (@ bind conv_monad (undef_flag `(SF)) (lambda (x0)
                  (@ bind conv_monad (undef_flag `(ZF)) (lambda (x1)
                    (@ bind conv_monad (undef_flag `(PF)) (lambda (x2)
                      (@ bind conv_monad (undef_flag `(AF)) (lambda (x3)
                        (@ bind conv_monad (@ load seg op1) (lambda (p1)
                          (@ bind conv_monad (@ load seg `(Reg_op ,r))
                            (lambda (p2)
                            (@ bind conv_monad
                              (match (op_override pre)
                                 ((True)
                                   (@ load_Z `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S
                                     ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                     `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO
                                     ,`(XH))))))))
                                 ((False)
                                   (@ load_Z `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                     ,`(S
                                     ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                     `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                                     ,`(XH)))))))))) (lambda (shiftup)
                              (@ bind conv_monad
                                (@ cast_u
                                  (@ opsize (op_override pre) `(True)) `(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                  ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  p1) (lambda (wide_p1)
                                (@ bind conv_monad
                                  (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    `(Shl_op) wide_p1 shiftup)
                                  (lambda (wide_p2)
                                  (@ bind conv_monad
                                    (@ cast_u
                                      (@ opsize (op_override pre) `(True))
                                      `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      p2) (lambda (wide_p3)
                                    (@ bind conv_monad
                                      (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S
                                        ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        `(Or_op) wide_p2 wide_p3)
                                      (lambda (combined)
                                      (@ bind conv_monad
                                        (@ cast_u size8 `(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S
                                          ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          count0) (lambda (wide_count)
                                        (@ bind conv_monad
                                          (@ arith `(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S
                                            ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                            `(Shl_op) combined wide_count)
                                          (lambda (shifted)
                                          (@ bind conv_monad
                                            (@ arith `(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S
                                              ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                              `(Shru_op) shifted shiftup)
                                            (lambda (shifted0)
                                            (@ bind conv_monad
                                              (@ cast_u `(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(S ,`(S ,`(S ,`(S ,`(S
                                                ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                (@ opsize (op_override pre)
                                                  `(True)) shifted0)
                                              (lambda (newdest0)
                                              (@ bind conv_monad
                                                (match (op_override pre)
                                                   ((True)
                                                     (@ load_Z size8 `(Zpos
                                                       ,`(XO ,`(XO ,`(XO
                                                       ,`(XO ,`(XH))))))))
                                                   ((False)
                                                     (@ load_Z size8 `(Zpos
                                                       ,`(XO ,`(XO ,`(XO
                                                       ,`(XO ,`(XO
                                                       ,`(XH))))))))))
                                                (lambda (maxcount)
                                                (@ bind conv_monad
                                                  (@ test size8 `(Ltu_op)
                                                    maxcount count0)
                                                  (lambda (guard1)
                                                  (@ bind conv_monad
                                                    (@ test size8 `(Eq_op)
                                                      maxcount count0)
                                                    (lambda (guard2)
                                                    (@ bind conv_monad
                                                      (@ arith size1 `(Or_op)
                                                        guard1 guard2)
                                                      (lambda (guard)
                                                      (@ bind conv_monad
                                                        (choose
                                                          (@ opsize
                                                            (op_override pre)
                                                            `(True)))
                                                        (lambda (newdest1)
                                                        (@ bind conv_monad
                                                          (@ if_exp
                                                            (@ opsize
                                                              (op_override
                                                                pre) `(True))
                                                            guard newdest1
                                                            newdest0)
                                                          (lambda (newdest)
                                                          (@ set2 seg newdest
                                                            op1))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_SHRD (lambdas (pre op1 r ri)
  (let ((load (@ load_op pre `(True))))
    (let ((set2 (@ set_op pre `(True))))
      (let ((seg (@ get_segment_op pre `(DS) op1)))
        (@ bind conv_monad
          (match ri
             ((Reg_ri r2) (@ iload_op8 seg `(Reg_op ,r2)))
             ((Imm_ri i)
               (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))) i)))
          (lambda (count)
          (@ bind conv_monad
            (@ load_Z size8 `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
              ,`(XH)))))))) (lambda (thirtytwo)
            (@ bind conv_monad (@ arith size8 `(Modu_op) count thirtytwo)
              (lambda (count0)
              (@ bind conv_monad (undef_flag `(CF)) (lambda (x)
                (@ bind conv_monad (undef_flag `(SF)) (lambda (x0)
                  (@ bind conv_monad (undef_flag `(ZF)) (lambda (x1)
                    (@ bind conv_monad (undef_flag `(PF)) (lambda (x2)
                      (@ bind conv_monad (undef_flag `(AF)) (lambda (x3)
                        (@ bind conv_monad (@ load seg op1) (lambda (p1)
                          (@ bind conv_monad (@ load seg `(Reg_op ,r))
                            (lambda (p2)
                            (@ bind conv_monad
                              (@ cast_u (@ opsize (op_override pre) `(True))
                                `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                p1) (lambda (wide_p1)
                              (@ bind conv_monad
                                (match (op_override pre)
                                   ((True)
                                     (@ load_Z `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S
                                       ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO
                                       ,`(XH))))))))
                                   ((False)
                                     (@ load_Z `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                       ,`(S
                                       ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                       `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                                       ,`(XH)))))))))) (lambda (shiftup)
                                (@ bind conv_monad
                                  (@ cast_u
                                    (@ opsize (op_override pre) `(True)) `(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                    ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    p2) (lambda (wide_p2)
                                  (@ bind conv_monad
                                    (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                      ,`(S
                                      ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      `(Shl_op) wide_p2 shiftup)
                                    (lambda (wide_p3)
                                    (@ bind conv_monad
                                      (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                        ,`(S
                                        ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        `(Or_op) wide_p1 wide_p3)
                                      (lambda (combined)
                                      (@ bind conv_monad
                                        (@ cast_u size8 `(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                          ,`(S ,`(S ,`(S
                                          ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          count0) (lambda (wide_count)
                                        (@ bind conv_monad
                                          (@ arith `(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                            ,`(S ,`(S ,`(S ,`(S
                                            ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                            `(Shru_op) combined wide_count)
                                          (lambda (shifted)
                                          (@ bind conv_monad
                                            (@ cast_u `(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                              ,`(S ,`(S ,`(S ,`(S
                                              ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                              (@ opsize (op_override pre)
                                                `(True)) shifted)
                                            (lambda (newdest0)
                                            (@ bind conv_monad
                                              (match (op_override pre)
                                                 ((True)
                                                   (@ load_Z size8 `(Zpos
                                                     ,`(XO ,`(XO ,`(XO ,`(XO
                                                     ,`(XH))))))))
                                                 ((False)
                                                   (@ load_Z size8 `(Zpos
                                                     ,`(XO ,`(XO ,`(XO ,`(XO
                                                     ,`(XO ,`(XH))))))))))
                                              (lambda (maxcount)
                                              (@ bind conv_monad
                                                (@ test size8 `(Ltu_op)
                                                  maxcount count0)
                                                (lambda (guard1)
                                                (@ bind conv_monad
                                                  (@ test size8 `(Eq_op)
                                                    maxcount count0)
                                                  (lambda (guard2)
                                                  (@ bind conv_monad
                                                    (@ arith size1 `(Or_op)
                                                      guard1 guard2)
                                                    (lambda (guard)
                                                    (@ bind conv_monad
                                                      (choose
                                                        (@ opsize
                                                          (op_override pre)
                                                          `(True)))
                                                      (lambda (newdest1)
                                                      (@ bind conv_monad
                                                        (@ if_exp
                                                          (@ opsize
                                                            (op_override pre)
                                                            `(True)) guard
                                                          newdest1 newdest0)
                                                        (lambda (newdest)
                                                        (@ set2 seg newdest
                                                          op1))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define get_AH (@ iload_op8 `(DS) `(Reg_op ,`(ESP))))

(define set_AH (lambda (v) (@ iset_op8 `(DS) v `(Reg_op ,`(ESP)))))

(define get_AL (@ iload_op8 `(DS) `(Reg_op ,`(EAX))))

(define set_AL (lambda (v) (@ iset_op8 `(DS) v `(Reg_op ,`(EAX)))))

(define conv_AAA_AAS (lambda (op1)
  (@ bind conv_monad (@ load_Z size8 `(Zpos ,`(XI ,`(XO ,`(XO ,`(XH))))))
    (lambda (pnine)
    (@ bind conv_monad (@ load_Z size8 `(Zpos ,`(XI ,`(XI ,`(XI ,`(XH))))))
      (lambda (p0Fmask)
      (@ bind conv_monad (get_flag `(AF)) (lambda (paf)
        (@ bind conv_monad get_AL (lambda (pal)
          (@ bind conv_monad (@ arith size8 `(And_op) pal p0Fmask)
            (lambda (digit1)
            (@ bind conv_monad (@ test size8 `(Lt_op) pnine digit1)
              (lambda (cond1)
              (@ bind conv_monad (@ arith size1 `(Or_op) cond1 paf)
                (lambda (cond)
                (@ bind conv_monad get_AH (lambda (pah)
                  (@ bind conv_monad (@ load_Z size1 `(Z0)) (lambda (pfalse)
                    (@ bind conv_monad (@ copy_ps size8 pah) (lambda (v_ah0)
                      (@ bind conv_monad (@ copy_ps size1 pfalse)
                        (lambda (v_af0)
                        (@ bind conv_monad (@ copy_ps size1 pfalse)
                          (lambda (v_cf0)
                          (@ bind conv_monad
                            (@ arith size8 `(And_op) pal p0Fmask)
                            (lambda (v_al0)
                            (@ bind conv_monad
                              (@ load_Z size8 `(Zpos ,`(XO ,`(XI ,`(XH)))))
                              (lambda (psix)
                              (@ bind conv_monad
                                (@ load_Z size8 `(Zpos ,`(XH)))
                                (lambda (pone)
                                (@ bind conv_monad
                                  (@ load_Z size1 `(Zpos ,`(XH)))
                                  (lambda (ptrue)
                                  (@ bind conv_monad
                                    (@ arith size8 op1 pal psix)
                                    (lambda (pal_c)
                                    (@ bind conv_monad
                                      (@ arith size8 `(And_op) pal_c p0Fmask)
                                      (lambda (pal_cmask)
                                      (@ bind conv_monad
                                        (@ if_exp size8 cond pal_cmask v_al0)
                                        (lambda (v_al)
                                        (@ bind conv_monad get_AH
                                          (lambda (pah0)
                                          (@ bind conv_monad
                                            (@ arith size8 op1 pah0 pone)
                                            (lambda (pah_c)
                                            (@ bind conv_monad
                                              (@ if_exp size8 cond pah_c
                                                v_ah0) (lambda (v_ah)
                                              (@ bind conv_monad
                                                (@ if_exp size1 cond ptrue
                                                  v_af0) (lambda (v_af)
                                                (@ bind conv_monad
                                                  (@ if_exp size1 cond ptrue
                                                    v_cf0) (lambda (v_cf)
                                                  (@ bind conv_monad
                                                    (set_AL v_al) (lambda (x)
                                                    (@ bind conv_monad
                                                      (set_AH v_ah)
                                                      (lambda (x0)
                                                      (@ bind conv_monad
                                                        (@ set_flag `(AF)
                                                          v_af) (lambda (x1)
                                                        (@ bind conv_monad
                                                          (@ set_flag `(CF)
                                                            v_cf)
                                                          (lambda (x2)
                                                          (@ bind conv_monad
                                                            (undef_flag
                                                              `(OF))
                                                            (lambda (x3)
                                                            (@ bind
                                                              conv_monad
                                                              (undef_flag
                                                                `(SF))
                                                              (lambda (x4)
                                                              (@ bind
                                                                conv_monad
                                                                (undef_flag
                                                                  `(ZF))
                                                                (lambda (x5)
                                                                (undef_flag
                                                                  `(PF))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define conv_AAD
  (@ bind conv_monad get_AL (lambda (pal)
    (@ bind conv_monad get_AH (lambda (pah)
      (@ bind conv_monad (@ load_Z size8 `(Zpos ,`(XO ,`(XI ,`(XO ,`(XH))))))
        (lambda (pten)
        (@ bind conv_monad
          (@ load_Z size8 `(Zpos ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI ,`(XI
            ,`(XH)))))))))) (lambda (pFF)
          (@ bind conv_monad (@ load_Z size8 `(Z0)) (lambda (pzero)
            (@ bind conv_monad (@ arith size8 `(Mul_op) pah pten)
              (lambda (tensval)
              (@ bind conv_monad (@ arith size8 `(Add_op) pal tensval)
                (lambda (pal_c)
                (@ bind conv_monad (@ arith size8 `(And_op) pal_c pFF)
                  (lambda (pal_cmask)
                  (@ bind conv_monad (set_AL pal_cmask) (lambda (x)
                    (@ bind conv_monad (set_AH pzero) (lambda (x0)
                      (@ bind conv_monad
                        (@ test size8 `(Eq_op) pal_cmask pzero) (lambda (b0)
                        (@ bind conv_monad (@ set_flag `(ZF) b0) (lambda (x1)
                          (@ bind conv_monad
                            (@ test size8 `(Lt_op) pal_cmask pzero)
                            (lambda (b1)
                            (@ bind conv_monad (@ set_flag `(SF) b1)
                              (lambda (x2)
                              (@ bind conv_monad
                                (@ compute_parity size8 pal_cmask)
                                (lambda (b2)
                                (@ bind conv_monad (@ set_flag `(PF) b2)
                                  (lambda (x3)
                                  (@ bind conv_monad (undef_flag `(OF))
                                    (lambda (x4)
                                    (@ bind conv_monad (undef_flag `(AF))
                                      (lambda (x5) (undef_flag `(CF)))))))))))))))))))))))))))))))))))))))

(define conv_AAM
  (@ bind conv_monad get_AL (lambda (pal)
    (@ bind conv_monad (@ load_Z size8 `(Zpos ,`(XO ,`(XI ,`(XO ,`(XH))))))
      (lambda (pten)
      (@ bind conv_monad (@ arith size8 `(Divu_op) pal pten) (lambda (digit1)
        (@ bind conv_monad (@ arith size8 `(Modu_op) pal pten)
          (lambda (digit2)
          (@ bind conv_monad (set_AH digit1) (lambda (x)
            (@ bind conv_monad (set_AL digit2) (lambda (x0)
              (@ bind conv_monad (@ load_Z size8 `(Z0)) (lambda (pzero)
                (@ bind conv_monad (@ test size8 `(Eq_op) digit2 pzero)
                  (lambda (b0)
                  (@ bind conv_monad (@ set_flag `(ZF) b0) (lambda (x1)
                    (@ bind conv_monad (@ test size8 `(Lt_op) digit2 pzero)
                      (lambda (b1)
                      (@ bind conv_monad (@ set_flag `(SF) b1) (lambda (x2)
                        (@ bind conv_monad (@ compute_parity size8 digit2)
                          (lambda (b2)
                          (@ bind conv_monad (@ set_flag `(PF) b2)
                            (lambda (x3)
                            (@ bind conv_monad (undef_flag `(OF))
                              (lambda (x4)
                              (@ bind conv_monad (undef_flag `(AF))
                                (lambda (x5) (undef_flag `(CF)))))))))))))))))))))))))))))))))

(define testcarryAdd (lambdas (s p1 p2 p3)
  (@ bind conv_monad (@ test s `(Ltu_op) p3 p1) (lambda (b0)
    (@ bind conv_monad (@ test s `(Ltu_op) p3 p2) (lambda (b1)
      (@ arith size1 `(Or_op) b0 b1)))))))

(define testcarrySub (lambdas (s p1 p2 p3) (@ test s `(Ltu_op) p1 p2)))

(define conv_DAA_DAS (lambdas (op1 tester)
  (@ bind conv_monad (choose size8) (lambda (pal)
    (@ bind conv_monad (set_AL pal) (lambda (x)
      (@ bind conv_monad (undef_flag `(CF)) (lambda (x0)
        (@ bind conv_monad (undef_flag `(AF)) (lambda (x1)
          (@ bind conv_monad (undef_flag `(SF)) (lambda (x2)
            (@ bind conv_monad (undef_flag `(ZF)) (lambda (x3)
              (@ bind conv_monad (undef_flag `(PF)) (lambda (x4)
                (undef_flag `(OF))))))))))))))))))

(define conv_logical_op (lambdas (do_effect b pre w op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
        (@ bind conv_monad (@ load seg op1) (lambda (p0)
          (@ bind conv_monad (@ load seg op2) (lambda (p1)
            (@ bind conv_monad
              (@ arith (@ opsize (op_override pre) w) b p0 p1) (lambda (p2)
              (@ bind conv_monad
                (@ load_Z (@ opsize (op_override pre) w) `(Z0))
                (lambda (zero2)
                (@ bind conv_monad
                  (@ test (@ opsize (op_override pre) w) `(Eq_op) zero2 p2)
                  (lambda (zfp)
                  (@ bind conv_monad
                    (@ test (@ opsize (op_override pre) w) `(Lt_op) p2 zero2)
                    (lambda (sfp)
                    (@ bind conv_monad
                      (@ compute_parity (@ opsize (op_override pre) w) p2)
                      (lambda (pfp)
                      (@ bind conv_monad (@ load_Z size1 `(Z0))
                        (lambda (zero3)
                        (@ bind conv_monad (@ set_flag `(OF) zero3)
                          (lambda (x)
                          (@ bind conv_monad (@ set_flag `(CF) zero3)
                            (lambda (x0)
                            (@ bind conv_monad (@ set_flag `(ZF) zfp)
                              (lambda (x1)
                              (@ bind conv_monad (@ set_flag `(SF) sfp)
                                (lambda (x2)
                                (@ bind conv_monad (@ set_flag `(PF) pfp)
                                  (lambda (x3)
                                  (@ bind conv_monad (undef_flag `(AF))
                                    (lambda (x4)
                                    (match do_effect
                                       ((True) (@ set2 seg p2 op1))
                                       ((False) no_op)))))))))))))))))))))))))))))))))))

(define conv_AND (lambdas (p w op1 op2)
  (@ conv_logical_op `(True) `(And_op) p w op1 op2)))

(define conv_OR (lambdas (p w op1 op2)
  (@ conv_logical_op `(True) `(Or_op) p w op1 op2)))

(define conv_XOR (lambdas (p w op1 op2)
  (@ conv_logical_op `(True) `(Xor_op) p w op1 op2)))

(define conv_TEST (lambdas (p w op1 op2)
  (@ conv_logical_op `(False) `(And_op) p w op1 op2)))

(define conv_NOT (lambdas (pre w op)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op pre `(DS) op)))
        (@ bind conv_monad (@ load seg op) (lambda (p0)
          (@ bind conv_monad
            (@ load_Z (@ opsize (op_override pre) w) (max_unsigned size32))
            (lambda (max_unsigned0)
            (@ bind conv_monad
              (@ arith (@ opsize (op_override pre) w) `(Xor_op) p0
                max_unsigned0) (lambda (p1) (@ set2 seg p1 op))))))))))))

(define conv_POP (lambdas (pre op)
  (let ((seg `(SS)))
    (let ((set2 (@ set_op pre `(True) seg)))
      (let ((loadmem (@ load_mem pre `(True) seg)))
        (let ((espoffset
          (match (op_override pre)
             ((True) `(Zpos ,`(XO ,`(XH))))
             ((False) `(Zpos ,`(XO ,`(XO ,`(XH))))))))
          (@ bind conv_monad (load_reg `(ESP)) (lambda (oldesp)
            (@ bind conv_monad (loadmem oldesp) (lambda (value)
              (@ bind conv_monad (@ load_Z size32 espoffset) (lambda (offset)
                (@ bind conv_monad (@ arith size32 `(Add_op) oldesp offset)
                  (lambda (newesp)
                  (@ bind conv_monad (@ set_reg newesp `(ESP)) (lambda (x)
                    (@ set2 value op)))))))))))))))))

(define conv_POPA (lambda (pre)
  (let ((espoffset
    (match (op_override pre)
       ((True) `(Zpos ,`(XO ,`(XH))))
       ((False) `(Zpos ,`(XO ,`(XO ,`(XH))))))))
    (let ((poprtl (lambda (r) (@ conv_POP pre `(Reg_op ,r)))))
      (@ bind conv_monad (poprtl `(EDI)) (lambda (x)
        (@ bind conv_monad (poprtl `(ESI)) (lambda (x0)
          (@ bind conv_monad (poprtl `(EBP)) (lambda (x1)
            (@ bind conv_monad (load_reg `(ESP)) (lambda (oldesp)
              (@ bind conv_monad (@ load_Z size32 espoffset) (lambda (offset)
                (@ bind conv_monad (@ arith size32 `(Add_op) oldesp offset)
                  (lambda (newesp)
                  (@ bind conv_monad (@ set_reg newesp `(ESP)) (lambda (x2)
                    (@ bind conv_monad (poprtl `(EBX)) (lambda (x3)
                      (@ bind conv_monad (poprtl `(EDX)) (lambda (x4)
                        (@ bind conv_monad (poprtl `(ECX)) (lambda (x5)
                          (poprtl `(EAX))))))))))))))))))))))))))

(define conv_PUSH (lambdas (pre w op)
  (let ((seg `(SS)))
    (let ((load (@ load_op pre `(True) seg)))
      (let ((setmem (@ set_mem pre `(True) seg)))
        (let ((espoffset
          (match (op_override pre)
             ((True) `(Zpos ,`(XO ,`(XH))))
             ((False) `(Zpos ,`(XO ,`(XO ,`(XH))))))))
          (@ bind conv_monad (load op) (lambda (p0)
            (@ bind conv_monad (load_reg `(ESP)) (lambda (oldesp)
              (@ bind conv_monad (@ load_Z size32 espoffset) (lambda (offset)
                (@ bind conv_monad (@ arith size32 `(Sub_op) oldesp offset)
                  (lambda (newesp)
                  (@ bind conv_monad (@ setmem p0 newesp) (lambda (x)
                    (@ set_reg newesp `(ESP))))))))))))))))))

(define conv_PUSH_pseudo (lambdas (pre w pr)
  (let ((seg `(SS)))
    (let ((setmem (@ set_mem pre w seg)))
      (let ((espoffset
        (match (op_override pre)
           ((True)
             (match w
                ((True) `(Zpos ,`(XO ,`(XH))))
                ((False) `(Zpos ,`(XH)))))
           ((False)
             (match w
                ((True) `(Zpos ,`(XO ,`(XO ,`(XH)))))
                ((False) `(Zpos ,`(XH))))))))
        (@ bind conv_monad (load_reg `(ESP)) (lambda (oldesp)
          (@ bind conv_monad (@ load_Z size32 espoffset) (lambda (offset)
            (@ bind conv_monad (@ arith size32 `(Sub_op) oldesp offset)
              (lambda (newesp)
              (@ bind conv_monad (@ setmem pr newesp) (lambda (x)
                (@ set_reg newesp `(ESP)))))))))))))))

(define conv_PUSHA (lambda (pre)
  (let ((load (@ load_op pre `(True) `(SS))))
    (let ((pushrtl (lambda (r) (@ conv_PUSH pre `(True) `(Reg_op ,r)))))
      (@ bind conv_monad (load `(Reg_op ,`(ESP))) (lambda (oldesp)
        (@ bind conv_monad (pushrtl `(EAX)) (lambda (x)
          (@ bind conv_monad (pushrtl `(ECX)) (lambda (x0)
            (@ bind conv_monad (pushrtl `(EDX)) (lambda (x1)
              (@ bind conv_monad (pushrtl `(EBX)) (lambda (x2)
                (@ bind conv_monad (@ conv_PUSH_pseudo pre `(True) oldesp)
                  (lambda (x3)
                  (@ bind conv_monad (pushrtl `(EBP)) (lambda (x4)
                    (@ bind conv_monad (pushrtl `(ESI)) (lambda (x5)
                      (pushrtl `(EDI))))))))))))))))))))))

(define get_and_place (lambdas (t dst pos fl)
  (@ bind conv_monad (get_flag fl) (lambda (fl0)
    (@ bind conv_monad (@ load_Z t pos) (lambda (pos0)
      (@ bind conv_monad (@ cast_u size1 t fl0) (lambda (byt)
        (@ bind conv_monad (@ arith t `(Shl_op) byt pos0) (lambda (tmp)
          (@ arith t `(Or_op) dst tmp)))))))))))

(define conv_POP_pseudo (lambda (pre)
  (let ((seg `(SS)))
    (let ((loadmem (@ load_mem pre `(True) seg)))
      (let ((espoffset
        (match (op_override pre)
           ((True) `(Zpos ,`(XO ,`(XH))))
           ((False) `(Zpos ,`(XO ,`(XO ,`(XH))))))))
        (@ bind conv_monad (load_reg `(ESP)) (lambda (oldesp)
          (@ bind conv_monad (@ load_Z size32 espoffset) (lambda (offset)
            (@ bind conv_monad (@ arith size32 `(Add_op) oldesp offset)
              (lambda (newesp)
              (@ bind conv_monad (@ set_reg newesp `(ESP)) (lambda (x)
                (loadmem oldesp))))))))))))))

(define extract_and_set (lambdas (t value pos fl)
  (@ bind conv_monad (@ load_Z t `(Zpos ,`(XH))) (lambda (one2)
    (@ bind conv_monad (@ load_Z t pos) (lambda (pos0)
      (@ bind conv_monad (@ arith t `(Shr_op) value pos0) (lambda (tmp)
        (@ bind conv_monad (@ arith t `(And_op) tmp one2) (lambda (tmp0)
          (@ bind conv_monad (@ test t `(Eq_op) one2 tmp0) (lambda (b)
            (@ set_flag fl b)))))))))))))

(define conv_JMP (lambdas (pre near absolute op sel)
  (let ((seg (@ get_segment_op pre `(DS) op)))
    (match near
       ((True)
         (@ bind conv_monad (@ iload_op32 seg op) (lambda (disp)
           (@ bind conv_monad
             (match absolute
                ((True) (@ load_Z size32 `(Z0)))
                ((False) get_pc)) (lambda (base)
             (@ bind conv_monad (@ arith size32 `(Add_op) base disp)
               (lambda (newpc) (set_pc0 newpc))))))))
       ((False) raise_error)))))

(define conv_Jcc (lambdas (pre ct disp)
  (@ bind conv_monad (compute_cc ct) (lambda (guard)
    (@ bind conv_monad get_pc (lambda (oldpc)
      (@ bind conv_monad
        (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
          ,`(O)))))))))))))))))))))))))))))))) disp) (lambda (pdisp)
        (@ bind conv_monad (@ arith size32 `(Add_op) oldpc pdisp)
          (lambda (newpc) (@ if_set_loc guard size32 newpc `(Pc_loc))))))))))))

(define conv_CALL (lambdas (pre near absolute op sel)
  (@ bind conv_monad get_pc (lambda (oldpc)
    (@ bind conv_monad (load_reg `(ESP)) (lambda (oldesp)
      (@ bind conv_monad (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XH)))))
        (lambda (four0)
        (@ bind conv_monad (@ arith size32 `(Sub_op) oldesp four0)
          (lambda (newesp)
          (@ bind conv_monad (@ set_mem32 `(SS) oldpc newesp) (lambda (x)
            (@ bind conv_monad (@ set_reg newesp `(ESP)) (lambda (x0)
              (@ conv_JMP pre near absolute op sel)))))))))))))))

(define conv_RET (lambdas (pre same_segment disp)
  (match same_segment
     ((True)
       (@ bind conv_monad (load_reg `(ESP)) (lambda (oldesp)
         (@ bind conv_monad (@ load_mem32 `(SS) oldesp) (lambda (value)
           (@ bind conv_monad (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XH)))))
             (lambda (four0)
             (@ bind conv_monad (@ arith size32 `(Add_op) oldesp four0)
               (lambda (newesp)
               (@ bind conv_monad
                 (match disp
                    ((Some imm)
                      (@ bind conv_monad
                        (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                          ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                          ,`(O)))))))))))))))) imm) (lambda (imm0)
                        (@ bind conv_monad
                          (@ cast_u `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                            ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                            ,`(O)))))))))))))))) size32 imm0) (lambda (imm1)
                          (@ bind conv_monad
                            (@ arith size32 `(Add_op) newesp imm1)
                            (lambda (newesp2) (@ set_reg newesp2 `(ESP)))))))))
                    ((None) (@ set_reg newesp `(ESP)))) (lambda (x)
                 (set_pc0 value))))))))))))
     ((False) raise_error))))

(define conv_LEAVE (lambda (pre)
  (@ bind conv_monad (load_reg `(EBP)) (lambda (ebp_val)
    (@ bind conv_monad (@ set_reg ebp_val `(ESP)) (lambda (x)
      (@ conv_POP pre `(Reg_op ,`(EBP)))))))))

(define conv_LOOP (lambdas (pre flagged testz disp)
  (@ bind conv_monad (@ load_Z size1 `(Zpos ,`(XH))) (lambda (ptrue)
    (@ bind conv_monad (load_reg `(ECX)) (lambda (p0)
      (@ bind conv_monad (@ load_Z size32 `(Zpos ,`(XH))) (lambda (p1)
        (@ bind conv_monad (@ arith size32 `(Sub_op) p0 p1) (lambda (p2)
          (@ bind conv_monad (@ set_reg p2 `(ECX)) (lambda (x)
            (@ bind conv_monad (@ load_Z size32 `(Z0)) (lambda (pzero)
              (@ bind conv_monad (@ test size32 `(Eq_op) p2 pzero)
                (lambda (pcz)
                (@ bind conv_monad (@ arith size1 `(Xor_op) pcz ptrue)
                  (lambda (pcnz)
                  (@ bind conv_monad (get_flag `(ZF)) (lambda (pzf)
                    (@ bind conv_monad (@ arith size1 `(Xor_op) pzf ptrue)
                      (lambda (pnzf)
                      (@ bind conv_monad
                        (match flagged
                           ((True)
                             (match testz
                                ((True) (@ arith size1 `(And_op) pzf pcnz))
                                ((False) (@ arith size1 `(And_op) pnzf pcnz))))
                           ((False) (@ arith size1 `(Or_op) pcnz pcnz)))
                        (lambda (bcond)
                        (@ bind conv_monad get_pc (lambda (eip0)
                          (@ bind conv_monad
                            (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                              ,`(O)))))))) disp) (lambda (doffset0)
                            (@ bind conv_monad
                              (@ cast_s `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                ,`(O)))))))) size32 doffset0)
                              (lambda (doffset1)
                              (@ bind conv_monad
                                (@ arith size32 `(Add_op) eip0 doffset1)
                                (lambda (eip1)
                                (@ bind conv_monad
                                  (match (op_override pre)
                                     ((True)
                                       (@ load_Z size32 `(Zpos ,`(XO ,`(XO
                                         ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                                         ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                                         ,`(XO ,`(XO ,`(XH))))))))))))))))))))
                                     ((False)
                                       (@ load_Z size32 (opp `(Zpos ,`(XH))))))
                                  (lambda (eipmask)
                                  (@ bind conv_monad
                                    (@ arith size32 `(And_op) eip1 eipmask)
                                    (lambda (eip2)
                                    (@ if_set_loc bcond size32 eip2
                                      `(Pc_loc))))))))))))))))))))))))))))))))))))))

(define conv_BS_aux (lambdas (s d n op)
  (let ((curr_int
    (match d
       ((True) (@ repr s (of_nat1 (@ minus s n))))
       ((False) (@ repr s (of_nat1 n))))))
    (match n
       ((O) (@ load_int s curr_int))
       ((S n~)
         (@ bind conv_monad (@ load_int s curr_int) (lambda (bcount)
           (@ bind conv_monad (@ conv_BS_aux s d n~ op) (lambda (rec0)
             (@ bind conv_monad (@ arith s `(Shru_op) op bcount) (lambda (ps)
               (@ bind conv_monad (@ cast_u s size1 ps) (lambda (curr_bit)
                 (@ bind conv_monad (@ load_int s curr_int) (lambda (rec1)
                   (@ if_exp s curr_bit rec1 rec0))))))))))))))))
  
(define conv_BS (lambdas (d pre op1 op2)
  (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
    (@ bind conv_monad (undef_flag `(AF)) (lambda (x)
      (@ bind conv_monad (undef_flag `(CF)) (lambda (x0)
        (@ bind conv_monad (undef_flag `(SF)) (lambda (x1)
          (@ bind conv_monad (undef_flag `(OF)) (lambda (x2)
            (@ bind conv_monad (undef_flag `(PF)) (lambda (x3)
              (@ bind conv_monad (@ iload_op32 seg op1) (lambda (des)
                (@ bind conv_monad (@ iload_op32 seg op2) (lambda (src)
                  (@ bind conv_monad (@ load_Z size32 `(Z0)) (lambda (zero2)
                    (@ bind conv_monad (@ test size32 `(Eq_op) src zero2)
                      (lambda (zf)
                      (@ bind conv_monad (@ set_flag `(ZF) zf) (lambda (x4)
                        (@ bind conv_monad
                          (@ conv_BS_aux size32 d size32 src) (lambda (res0)
                          (@ bind conv_monad (choose size32) (lambda (res1)
                            (@ bind conv_monad (@ if_exp size32 zf res1 res0)
                              (lambda (res) (@ iset_op32 seg res op1))))))))))))))))))))))))))))))

(define conv_BSF (lambdas (p op1 op2) (@ conv_BS `(True) p op1 op2)))

(define conv_BSR (lambdas (p op1 op2) (@ conv_BS `(False) p op1 op2)))

(define get_Bit (lambdas (s pb poff)
  (@ bind conv_monad (@ load_Z s `(Zpos ,`(XH))) (lambda (omask)
    (@ bind conv_monad (@ arith s `(Shr_op) pb poff) (lambda (shr_pb)
      (@ bind conv_monad (@ arith s `(And_op) shr_pb omask) (lambda (mask_pb)
        (@ cast_u s size1 mask_pb)))))))))

(define modify_Bit (lambdas (s value poff bitval)
  (@ bind conv_monad (@ load_Z s `(Zpos ,`(XH))) (lambda (obit)
    (@ bind conv_monad (@ arith s `(Shl_op) obit poff) (lambda (one_shifted)
      (@ bind conv_monad (@ not0 s one_shifted) (lambda (inv_one_shifted)
        (@ bind conv_monad (@ cast_u size1 s bitval) (lambda (bitvalword)
          (@ bind conv_monad (@ arith s `(Shl_op) bitvalword poff)
            (lambda (bit_shifted)
            (@ bind conv_monad (@ arith s `(And_op) value inv_one_shifted)
              (lambda (newval) (@ arith s `(Or_op) newval bit_shifted)))))))))))))))

(define set_Bit (lambdas (pre w op poff bitval)
  (let ((seg (@ get_segment_op pre `(DS) op)))
    (let ((load (@ load_op pre w seg)))
      (let ((set2 (@ set_op pre w seg)))
        (@ bind conv_monad (load op) (lambda (value)
          (@ bind conv_monad
            (@ modify_Bit (@ opsize (op_override pre) w) value poff bitval)
            (lambda (newvalue) (@ set2 newvalue op))))))))))

(define set_Bit_mem (lambdas (pre w op addr poff bitval)
  (let ((seg (@ get_segment_op pre `(DS) op)))
    (let ((load (@ load_mem pre w seg)))
      (let ((set2 (@ set_mem pre w seg)))
        (@ bind conv_monad (load addr) (lambda (value)
          (@ bind conv_monad
            (@ modify_Bit (@ opsize (op_override pre) w) value poff bitval)
            (lambda (newvalue)
            (@ bind conv_monad (@ copy_ps size32 addr) (lambda (newaddr)
              (@ set2 newvalue newaddr))))))))))))

(define fbit (lambdas (param1 param2 v)
  (match param1
     ((True)
       (match param2
          ((True) (@ load_Z size1 `(Zpos ,`(XH))))
          ((False) (@ load_Z size1 `(Z0)))))
     ((False)
       (match param2
          ((True) (@ copy_ps size1 v))
          ((False) (@ not0 size1 v)))))))

(define conv_BT (lambdas (param1 param2 pre op1 regimm)
  (let ((seg (@ get_segment_op pre `(DS) op1)))
    (let ((load (@ load_op pre `(True) seg)))
      (let ((lmem0 (@ load_mem pre `(True) seg)))
        (let ((opsz (@ opsize (op_override pre) `(True))))
          (@ bind conv_monad (undef_flag `(OF)) (lambda (x)
            (@ bind conv_monad (undef_flag `(SF)) (lambda (x0)
              (@ bind conv_monad (undef_flag `(AF)) (lambda (x1)
                (@ bind conv_monad (undef_flag `(PF)) (lambda (x2)
                  (@ bind conv_monad (load regimm) (lambda (pi0)
                    (@ bind conv_monad
                      (@ load_Z opsz (@ add1 (of_nat1 opsz) `(Zpos ,`(XH))))
                      (lambda (popsz)
                      (@ bind conv_monad
                        (match regimm
                           ((Imm_op i)
                             (@ arith (@ opsize (op_override pre) `(True))
                               `(Modu_op) pi0 popsz))
                           ((Reg_op r)
                             (@ copy_ps (@ opsize (op_override pre) `(True))
                               pi0))
                           ((Address_op a)
                             (@ copy_ps (@ opsize (op_override pre) `(True))
                               pi0))
                           ((Offset_op i)
                             (@ copy_ps (@ opsize (op_override pre) `(True))
                               pi0))) (lambda (rawoffset)
                        (@ bind conv_monad
                          (@ load_Z size32
                            (@ div1 (of_nat1 (@ plus opsz `(S ,`(O)))) `(Zpos
                              ,`(XO ,`(XO ,`(XO ,`(XH)))))))
                          (lambda (popsz_bytes)
                          (@ bind conv_monad (@ load_Z opsz `(Z0))
                            (lambda (pzero)
                            (@ bind conv_monad
                              (@ load_Z size32 `(Zneg ,`(XH)))
                              (lambda (pneg1)
                              (let ((btmem (lambda (psaddr)
                                (@ bind conv_monad
                                  (@ arith
                                    (@ opsize (op_override pre) `(True))
                                    `(Mods_op) rawoffset popsz)
                                  (lambda (bitoffset)
                                  (@ bind conv_monad
                                    (@ arith
                                      (@ opsize (op_override pre) `(True))
                                      `(Divs_op) rawoffset popsz)
                                    (lambda (wordoffset~)
                                    (@ bind conv_monad
                                      (@ cast_s
                                        (@ opsize (op_override pre) `(True))
                                        size32 wordoffset~)
                                      (lambda (wordoffset)
                                      (@ bind conv_monad
                                        (@ test
                                          (@ opsize (op_override pre)
                                            `(True)) `(Lt_op) bitoffset
                                          pzero) (lambda (isneg)
                                        (@ bind conv_monad
                                          (@ copy_ps
                                            (@ opsize (op_override pre)
                                              `(True)) bitoffset)
                                          (lambda (nbitoffset0)
                                          (@ bind conv_monad
                                            (@ copy_ps size32 wordoffset)
                                            (lambda (nwordoffset0)
                                            (@ bind conv_monad
                                              (@ arith opsz `(Add_op) popsz
                                                bitoffset)
                                              (lambda (negbitoffset)
                                              (@ bind conv_monad
                                                (@ arith size32 `(Add_op)
                                                  pneg1 wordoffset)
                                                (lambda (negwordoffset)
                                                (@ bind conv_monad
                                                  (@ cast_u opsz
                                                    (@ opsize
                                                      (op_override pre)
                                                      `(True)) negbitoffset)
                                                  (lambda (nbitoffset1)
                                                  (@ bind conv_monad
                                                    (@ if_exp
                                                      (@ opsize
                                                        (op_override pre)
                                                        `(True)) isneg
                                                      nbitoffset1
                                                      nbitoffset0)
                                                    (lambda (nbitoffset)
                                                    (@ bind conv_monad
                                                      (@ cast_u size32 size32
                                                        negwordoffset)
                                                      (lambda (nwordoffset1)
                                                      (@ bind conv_monad
                                                        (@ if_exp size32
                                                          isneg nwordoffset1
                                                          nwordoffset0)
                                                        (lambda (nwordoffset)
                                                        (@ bind conv_monad
                                                          (@ arith size32
                                                            `(Mul_op)
                                                            nwordoffset
                                                            popsz_bytes)
                                                          (lambda (newaddrdelta)
                                                          (@ bind conv_monad
                                                            (@ arith size32
                                                              `(Add_op)
                                                              newaddrdelta
                                                              psaddr)
                                                            (lambda (newaddr)
                                                            (@ bind
                                                              conv_monad
                                                              (lmem0 newaddr)
                                                              (lambda (value)
                                                              (@ bind
                                                                conv_monad
                                                                (@ get_Bit
                                                                  (@ opsize
                                                                    (op_override
                                                                    pre)
                                                                    `(True))
                                                                  value
                                                                  nbitoffset)
                                                                (lambda (bt)
                                                                (@ bind
                                                                  conv_monad
                                                                  (@ set_flag
                                                                    `(CF) bt)
                                                                  (lambda (x3)
                                                                  (@ bind
                                                                    conv_monad
                                                                    (@ fbit
                                                                    param1
                                                                    param2
                                                                    bt)
                                                                    (lambda (newbt)
                                                                    (@ set_Bit_mem
                                                                    pre
                                                                    `(True)
                                                                    op1
                                                                    newaddr
                                                                    nbitoffset
                                                                    newbt))))))))))))))))))))))))))))))))))))))))
                                (match op1
                                   ((Imm_op i) raise_error)
                                   ((Reg_op r2)
                                     (@ bind conv_monad (load `(Reg_op ,r2))
                                       (lambda (value)
                                       (@ bind conv_monad
                                         (@ arith
                                           (@ opsize (op_override pre)
                                             `(True)) `(Modu_op) rawoffset
                                           popsz) (lambda (bitoffset)
                                         (@ bind conv_monad
                                           (@ get_Bit
                                             (@ opsize (op_override pre)
                                               `(True)) value bitoffset)
                                           (lambda (bt)
                                           (@ bind conv_monad
                                             (@ set_flag `(CF) bt)
                                             (lambda (x3)
                                             (@ bind conv_monad
                                               (@ fbit param1 param2 bt)
                                               (lambda (newbt)
                                               (@ set_Bit pre `(True) op1
                                                 bitoffset newbt))))))))))))
                                   ((Address_op a)
                                     (@ bind conv_monad (compute_addr a)
                                       (lambda (psaddr) (btmem psaddr))))
                                   ((Offset_op ioff)
                                     (@ bind conv_monad
                                       (@ load_int `(S ,`(S ,`(S ,`(S ,`(S
                                         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                                         ,`(S ,`(S ,`(S ,`(S ,`(S
                                         ,`(O))))))))))))))))))))))))))))))))
                                         ioff) (lambda (psaddr)
                                       (btmem psaddr))))))))))))))))))))))))))))))))

(define conv_BSWAP (lambdas (pre r)
  (@ bind conv_monad (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO ,`(XH))))))
    (lambda (eight)
    (@ bind conv_monad (load_reg r) (lambda (ps0)
      (@ bind conv_monad (@ cast_u size32 size8 ps0) (lambda (b0)
        (@ bind conv_monad (@ arith size32 `(Shru_op) ps0 eight)
          (lambda (ps1)
          (@ bind conv_monad (@ cast_u size32 size8 ps1) (lambda (b1)
            (@ bind conv_monad (@ cast_u size8 size32 b1) (lambda (w1)
              (@ bind conv_monad (@ arith size32 `(Shru_op) ps1 eight)
                (lambda (ps2)
                (@ bind conv_monad (@ cast_u size32 size8 ps2) (lambda (b2)
                  (@ bind conv_monad (@ cast_u size8 size32 b2) (lambda (w2)
                    (@ bind conv_monad (@ arith size32 `(Shru_op) ps2 eight)
                      (lambda (ps3)
                      (@ bind conv_monad (@ cast_u size32 size8 ps3)
                        (lambda (b3)
                        (@ bind conv_monad (@ cast_u size8 size32 b3)
                          (lambda (w3)
                          (@ bind conv_monad (@ cast_u size8 size32 b0)
                            (lambda (res0)
                            (@ bind conv_monad
                              (@ arith size32 `(Shl_op) res0 eight)
                              (lambda (res1)
                              (@ bind conv_monad
                                (@ arith size32 `(Add_op) res1 w1)
                                (lambda (res2)
                                (@ bind conv_monad
                                  (@ arith size32 `(Shl_op) res2 eight)
                                  (lambda (res3)
                                  (@ bind conv_monad
                                    (@ arith size32 `(Add_op) res3 w2)
                                    (lambda (res4)
                                    (@ bind conv_monad
                                      (@ arith size32 `(Shl_op) res4 eight)
                                      (lambda (res5)
                                      (@ bind conv_monad
                                        (@ arith size32 `(Add_op) res5 w3)
                                        (lambda (res6) (@ set_reg res6 r)))))))))))))))))))))))))))))))))))))))))

(define conv_CWDE (lambda (pre)
  (let ((seg (@ get_segment pre `(DS))))
    (match (op_override pre)
       ((True)
         (@ bind conv_monad (@ iload_op8 seg `(Reg_op ,`(EAX))) (lambda (p1)
           (@ bind conv_monad (@ cast_s size8 size16 p1) (lambda (p2)
             (@ iset_op16 seg p2 `(Reg_op ,`(EAX))))))))
       ((False)
         (@ bind conv_monad (@ iload_op16 seg `(Reg_op ,`(EAX))) (lambda (p1)
           (@ bind conv_monad (@ cast_s size16 size32 p1) (lambda (p2)
             (@ iset_op32 seg p2 `(Reg_op ,`(EAX))))))))))))

(define conv_CDQ (lambda (pre)
  (let ((seg (@ get_segment pre `(DS))))
    (match (op_override pre)
       ((True)
         (@ bind conv_monad (@ iload_op16 seg `(Reg_op ,`(EAX))) (lambda (p1)
           (@ bind conv_monad (@ cast_s size16 size32 p1) (lambda (p2)
             (@ bind conv_monad (@ cast_s size32 size16 p2)
               (lambda (p2_bottom)
               (@ bind conv_monad
                 (@ load_Z size32 `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XH)))))))
                 (lambda (sixteen)
                 (@ bind conv_monad (@ arith size32 `(Shr_op) p2 sixteen)
                   (lambda (p2_top0)
                   (@ bind conv_monad (@ cast_s size32 size16 p2_top0)
                     (lambda (p2_top)
                     (@ bind conv_monad
                       (@ iset_op16 seg p2_bottom `(Reg_op ,`(EAX)))
                       (lambda (x)
                       (@ iset_op16 seg p2_top `(Reg_op ,`(EDX))))))))))))))))))
       ((False)
         (@ bind conv_monad (@ iload_op32 seg `(Reg_op ,`(EAX))) (lambda (p1)
           (@ bind conv_monad
             (@ cast_s size32 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
               p1) (lambda (p2)
             (@ bind conv_monad
               (@ cast_s `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                 ,`(S ,`(S ,`(S ,`(S ,`(S
                 ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 size32 p2) (lambda (p2_bottom)
               (@ bind conv_monad
                 (@ load_Z `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                   ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                   ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                   ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                   ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                   ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                   ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XH))))))))
                 (lambda (thirtytwo)
                 (@ bind conv_monad
                   (@ arith `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                     ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                     ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                     `(Shr_op) p2 thirtytwo) (lambda (p2_top0)
                   (@ bind conv_monad
                     (@ cast_s `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                       ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                       ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       size32 p2_top0) (lambda (p2_top)
                     (@ bind conv_monad
                       (@ iset_op32 seg p2_bottom `(Reg_op ,`(EAX)))
                       (lambda (x)
                       (@ iset_op32 seg p2_top `(Reg_op ,`(EDX))))))))))))))))))))))

(define conv_MOV (lambdas (pre w op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
        (@ bind conv_monad (@ load seg op2) (lambda (res)
          (@ set2 seg res op1))))))))

(define conv_CMOV (lambdas (pre w cc op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
        (@ bind conv_monad (@ load seg op1) (lambda (tmp0)
          (@ bind conv_monad (@ load seg op2) (lambda (src)
            (@ bind conv_monad (compute_cc cc) (lambda (cc0)
              (@ bind conv_monad
                (@ cast_u (@ opsize (op_override pre) w)
                  (@ opsize (op_override pre) w) src) (lambda (tmp1)
                (@ bind conv_monad
                  (@ if_exp (@ opsize (op_override pre) w) cc0 tmp1 tmp0)
                  (lambda (tmp) (@ set2 seg tmp op1))))))))))))))))

(define conv_MOV_extend (lambdas (extend_op pre w op1 op2)
  (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
    (match (op_override pre)
       ((True)
         (match w
            ((True)
              (@ bind conv_monad (@ iload_op16 seg op2) (lambda (p1)
                (@ iset_op16 seg p1 op1))))
            ((False)
              (@ bind conv_monad (@ iload_op8 seg op2) (lambda (p1)
                (@ bind conv_monad (@ extend_op size8 size16 p1) (lambda (p2)
                  (@ iset_op16 seg p2 op1))))))))
       ((False)
         (match w
            ((True)
              (@ bind conv_monad (@ iload_op16 seg op2) (lambda (p1)
                (@ bind conv_monad (@ extend_op size16 size32 p1)
                  (lambda (p2) (@ iset_op32 seg p2 op1))))))
            ((False)
              (@ bind conv_monad (@ iload_op8 seg op2) (lambda (p1)
                (@ bind conv_monad (@ extend_op size8 size32 p1) (lambda (p2)
                  (@ iset_op32 seg p2 op1))))))))))))

(define conv_MOVZX (lambdas (pre w op1 op2)
  (@ conv_MOV_extend cast_u pre w op1 op2)))

(define conv_MOVSX (lambdas (pre w op1 op2)
  (@ conv_MOV_extend cast_s pre w op1 op2)))

(define conv_XCHG (lambdas (pre w op1 op2)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg (@ get_segment_op2 pre `(DS) op1 op2)))
        (@ bind conv_monad (@ load seg op1) (lambda (p1)
          (@ bind conv_monad (@ load seg op2) (lambda (p2)
            (@ bind conv_monad (@ set2 seg p2 op1) (lambda (x)
              (@ set2 seg p1 op2))))))))))))

(define conv_XADD (lambdas (pre w op1 op2)
  (@ bind conv_monad (@ conv_XCHG pre w op1 op2) (lambda (x)
    (@ conv_ADD pre w op1 op2)))))

(define conv_CMPXCHG (lambdas (pre w op1 op2)
  (@ bind conv_monad (@ conv_CMP pre w `(Reg_op ,`(EAX)) op1) (lambda (x)
    (@ bind conv_monad (@ conv_CMOV pre w `(E_ct) op1 op2) (lambda (x0)
      (@ conv_CMOV pre w `(NE_ct) `(Reg_op ,`(EAX)) op1)))))))

(define string_op_reg_shift (lambdas (reg pre w)
  (@ bind conv_monad
    (@ load_Z size32
      (match (op_override pre)
         ((True)
           (match w
              ((True) `(Zpos ,`(XO ,`(XH))))
              ((False) `(Zpos ,`(XH)))))
         ((False)
           (match w
              ((True) `(Zpos ,`(XO ,`(XO ,`(XH)))))
              ((False) `(Zpos ,`(XH))))))) (lambda (offset)
    (@ bind conv_monad (get_flag `(DF)) (lambda (df)
      (@ bind conv_monad (@ iload_op32 `(DS) `(Reg_op ,reg))
        (lambda (old_reg)
        (@ bind conv_monad (@ arith size32 `(Add_op) old_reg offset)
          (lambda (new_reg1)
          (@ bind conv_monad (@ arith size32 `(Sub_op) old_reg offset)
            (lambda (new_reg2)
            (@ bind conv_monad (@ set_reg new_reg1 reg) (lambda (x)
              (@ if_set_loc df size32 new_reg2 `(Reg_loc ,reg))))))))))))))))

(define conv_MOVS (lambdas (pre w)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (let ((seg_load (@ get_segment pre `(DS))))
        (@ bind conv_monad
          (@ load seg_load `(Address_op ,`(MkAddress
            ,(zero1 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(O))))))))))))))))))))))))))))))))) ,`(Some ,`(ESI))
            ,`(None)))) (lambda (p1)
          (@ bind conv_monad
            (@ set2 `(ES) p1 `(Address_op ,`(MkAddress
              ,(zero1 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                 ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                 ,`(O))))))))))))))))))))))))))))))))) ,`(Some ,`(EDI))
              ,`(None)))) (lambda (x)
            (@ bind conv_monad (@ string_op_reg_shift `(EDI) pre w)
              (lambda (x0) (@ string_op_reg_shift `(ESI) pre w))))))))))))

(define conv_STOS (lambdas (pre w)
  (let ((load (@ load_op pre w)))
    (let ((set2 (@ set_op pre w)))
      (@ bind conv_monad (@ load `(DS) `(Reg_op ,`(EAX))) (lambda (p1)
        (@ bind conv_monad
          (@ set2 `(ES) p1 `(Address_op ,`(MkAddress
            ,(zero1 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
               ,`(O))))))))))))))))))))))))))))))))) ,`(Some ,`(EDI))
            ,`(None)))) (lambda (x) (@ string_op_reg_shift `(EDI) pre w)))))))))

(define conv_CMPS (lambdas (pre w)
  (let ((seg1 (@ get_segment pre `(DS))))
    (let ((op1 `(Address_op ,`(MkAddress
      ,(zero1 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))))))))))))))))))))))))))))
      ,`(Some ,`(ESI)) ,`(None)))))
      (let ((op2 `(Address_op ,`(MkAddress
        ,(zero1 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O))))))))))))))))))))))))))))))))) ,`(Some ,`(EDI))
        ,`(None)))))
        (@ bind conv_monad
          (@ conv_SUB_CMP_generic `(False) pre w op1 op2 op2 seg1 seg1 `(ES))
          (lambda (x)
          (@ bind conv_monad (@ string_op_reg_shift `(EDI) pre w)
            (lambda (x0) (@ string_op_reg_shift `(ESI) pre w))))))))))

(define conv_LEA (lambdas (pre op1 op2)
  (let ((seg (@ get_segment_op pre `(DS) op1)))
    (match op2
       ((Imm_op i) raise_error)
       ((Reg_op r) raise_error)
       ((Address_op a)
         (@ bind conv_monad (compute_addr a) (lambda (r)
           (@ iset_op32 seg r op1))))
       ((Offset_op i) raise_error)))))

(define conv_HLT (lambda (pre) raise_trap))

(define conv_SETcc (lambdas (pre ct op)
  (let ((seg (@ get_segment_op pre `(DS) op)))
    (@ bind conv_monad (compute_cc ct) (lambda (ccval)
      (@ bind conv_monad (@ cast_u size1 size8 ccval) (lambda (ccext)
        (@ iset_op8 seg ccext op))))))))

(define check_prefix (lambda (p)
  (match (addr_override p)
     ((True) raise_error)
     ((False) no_op))))

(define int_to_bin32 (lambda (i) (b32_of_bits (@ intval size32 i))))

(define bin32_to_int (lambda (b) (@ repr size32 (bits_of_b32 b))))

(define int_to_bin64 (lambda (i) (b64_of_bits (@ intval size64 i))))

(define bin64_to_int (lambda (b) (@ repr size64 (bits_of_b64 b))))

(define int_to_de_float (lambda (i) (de_float_of_bits (@ intval size80 i))))

(define de_float_to_int (lambda (b) (@ repr size80 (bits_of_de_float b))))

(define string_to_de_float (lambda (s)
  (let ((intval0 (@ string_to_int size80 s))) (int_to_de_float intval0))))

(define s2bf (lambda (s) (string_to_de_float s)))

(define s2int80 (lambda (s) (@ string_to_int size80 s)))

(define integer_to_de_float (lambda (i)
  (let ((bin (int_to_de_float i)))
    (match bin
       ((B754_zero s) `(B754_zero ,s))
       ((B754_infinity s) `(B754_infinity ,s))
       ((B754_nan) `(B754_nan))
       ((B754_finite s m e)
         (let ((mant_val (@ intval size80 i)))
           (match (@ shr0 `(Build_shr_record ,mant_val ,`(False) ,`(False))
                    mant_val `(Zpos ,`(XH)))
              ((Pair rec shifted_m)
                (let ((exp_val (of_nat1 size80)))
                  (let ((joined
                    (@ join_bits `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                      ,`(XH)))))))) `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                      ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
                      ,`(XH)))))))))))))))) s
                      (@ sub1 shifted_m `(Zpos ,`(XH))) exp_val)))
                    (de_float_of_bits joined)))))))))))

(define enc_rounding_mode (lambda (rm)
  (match rm
     ((Mode_NE) `(Z0))
     ((Mode_ZR) `(Zpos ,`(XI ,`(XH))))
     ((Mode_DN) `(Zpos ,`(XH)))
     ((Mode_UP) `(Zpos ,`(XO ,`(XH))))
     ((Mode_NA) `(Z0)))))

(define fpu_precision_control_rect (lambdas (f f0 f1 f2 f3)
  (match f3
     ((PC_single) f)
     ((PC_reserved) f0)
     ((PC_double) f1)
     ((PC_double_extended) f2))))

(define fpu_precision_control_rec (lambdas (f f0 f1 f2 f3)
  (match f3
     ((PC_single) f)
     ((PC_reserved) f0)
     ((PC_double) f1)
     ((PC_double_extended) f2))))

(define enc_fpu_precision_control (lambda (pc0)
  (match pc0
     ((PC_single) `(Z0))
     ((PC_reserved) `(Zpos ,`(XH)))
     ((PC_double) `(Zpos ,`(XO ,`(XH))))
     ((PC_double_extended) `(Zpos ,`(XI ,`(XH)))))))

(define fpu_tag_mode_rect (lambdas (f f0 f1 f2 f3)
  (match f3
     ((TM_valid) f)
     ((TM_zero) f0)
     ((TM_special) f1)
     ((TM_empty) f2))))

(define fpu_tag_mode_rec (lambdas (f f0 f1 f2 f3)
  (match f3
     ((TM_valid) f)
     ((TM_zero) f0)
     ((TM_special) f1)
     ((TM_empty) f2))))

(define enc_fpu_tag_mode (lambda (tm)
  (match tm
     ((TM_valid) `(Z0))
     ((TM_zero) `(Zpos ,`(XH)))
     ((TM_special) `(Zpos ,`(XO ,`(XH))))
     ((TM_empty) `(Zpos ,`(XI ,`(XH)))))))

(define get_stktop (@ read_loc size3 `(Fpu_stktop_loc)))

(define get_fpu_rctrl (@ read_loc size2 `(Fpu_rctrl_loc)))

(define get_fpu_reg (lambda (i)
  (@ read_array size3 size80 `(Fpu_datareg) i)))

(define get_fpu_tag (lambda (i) (@ read_array size3 size2 `(Fpu_tag) i)))

(define set_stktop (lambda (t) (@ write_loc size3 t `(Fpu_stktop_loc))))

(define set_stktop_const (lambda (t)
  (@ bind conv_monad (@ load_Z size3 t) (lambda (r) (set_stktop r)))))

(define set_fpu_flag (lambdas (fl r)
  (@ write_loc size1 r `(Fpu_flag_loc ,fl))))

(define set_fpu_flag_const (lambdas (fl bit)
  (@ bind conv_monad (@ load_Z size1 bit) (lambda (r) (@ set_fpu_flag fl r)))))

(define set_fpu_ctrl (lambdas (cf r)
  (@ write_loc size1 r `(Fpu_ctrl_flag_loc ,cf))))

(define set_fpu_ctrl_const (lambdas (cf bit)
  (@ bind conv_monad (@ load_Z size1 bit) (lambda (r) (@ set_fpu_ctrl cf r)))))

(define set_fpu_rctrl (lambda (r) (@ write_loc size2 r `(Fpu_rctrl_loc))))

(define set_fpu_rctrl_const (lambda (rm)
  (@ bind conv_monad (@ load_Z size2 (enc_rounding_mode rm)) (lambda (r)
    (set_fpu_rctrl r)))))

(define set_fpu_pctrl (lambda (r) (@ write_loc size2 r `(Fpu_pctrl_loc))))

(define set_fpu_pctrl_const (lambda (pc0)
  (@ bind conv_monad (@ load_Z size2 (enc_fpu_precision_control pc0))
    (lambda (r) (set_fpu_pctrl r)))))

(define set_fpu_lastInstrPtr (lambda (r)
  (@ write_loc size48 r `(Fpu_lastInstrPtr_loc))))

(define set_fpu_lastInstrPtr_const (lambda (v)
  (@ bind conv_monad (@ load_Z size48 v) (lambda (r)
    (set_fpu_lastInstrPtr r)))))

(define set_fpu_lastDataPtr (lambda (r)
  (@ write_loc size48 r `(Fpu_lastDataPtr_loc))))

(define set_fpu_lastDataPtr_const (lambda (v)
  (@ bind conv_monad (@ load_Z size48 v) (lambda (r)
    (set_fpu_lastDataPtr r)))))

(define set_fpu_lastOpcode (lambda (r)
  (@ write_loc size11 r `(Fpu_lastOpcode_loc))))

(define set_fpu_lastOpcode_const (lambda (v)
  (@ bind conv_monad (@ load_Z size11 v) (lambda (r) (set_fpu_lastOpcode r)))))

(define set_fpu_reg (lambdas (i v)
  (@ write_array size3 size80 `(Fpu_datareg) i v)))

(define set_fpu_tag (lambdas (i v)
  (@ write_array size3 size2 `(Fpu_tag) i v)))

(define set_fpu_tag_const (lambdas (loc tm)
  (@ bind conv_monad (@ load_Z size3 loc) (lambda (i)
    (@ bind conv_monad (@ load_Z size2 (enc_fpu_tag_mode tm)) (lambda (v)
      (@ set_fpu_tag i v)))))))

(define inc_stktop
  (@ bind conv_monad get_stktop (lambda (st)
    (@ bind conv_monad (@ load_Z size3 `(Zpos ,`(XH))) (lambda (one2)
      (@ bind conv_monad (@ arith size3 `(Add_op) st one2) (lambda (newst)
        (set_stktop newst))))))))

(define dec_stktop
  (@ bind conv_monad get_stktop (lambda (st)
    (@ bind conv_monad (@ load_Z size3 `(Zpos ,`(XH))) (lambda (one2)
      (@ bind conv_monad (@ arith size3 `(Sub_op) st one2) (lambda (newst)
        (set_stktop newst))))))))

(define stk_push (lambda (f)
  (@ bind conv_monad dec_stktop (lambda (x)
    (@ bind conv_monad get_stktop (lambda (topp) (@ set_fpu_reg topp f)))))))

(define freg_of_offset (lambda (offset)
  (@ bind conv_monad get_stktop (lambda (topp)
    (@ bind conv_monad (@ load_Z size3 (@ unsigned `(S ,`(S ,`(O))) offset))
      (lambda (ri) (@ arith size3 `(Add_op) topp ri)))))))

(define undef_fpu_flag (lambda (f)
  (@ bind conv_monad (choose size1) (lambda (v) (@ set_fpu_flag f v)))))

(define is_empty_tag (lambda (i)
  (@ bind conv_monad (get_fpu_tag i) (lambda (tag)
    (@ bind conv_monad (@ load_Z size2 `(Zpos ,`(XI ,`(XH))))
      (lambda (empty_tag) (@ test size2 `(Eq_op) tag empty_tag)))))))

(define is_nonempty_tag (lambda (i)
  (@ bind conv_monad (is_empty_tag i) (lambda (isempty)
    (@ not0 size1 isempty)))))

(define test_pos_zero (lambdas (ew mw f)
  (@ bind conv_monad (@ load_Z (@ plus (to_nat ew) (to_nat mw)) `(Z0))
    (lambda (poszero)
    (@ test (@ plus (to_nat ew) (to_nat mw)) `(Eq_op) f poszero)))))

(define test_neg_zero (lambdas (ew mw f)
  (@ bind conv_monad
    (@ load_Z (@ plus (to_nat ew) (to_nat mw))
      (two_power_nat (@ plus (to_nat mw) (to_nat ew)))) (lambda (negzero)
    (@ test (@ plus (to_nat ew) (to_nat mw)) `(Eq_op) f negzero)))))

(define test_zero (lambdas (ew mw f)
  (@ bind conv_monad (@ test_pos_zero ew mw f) (lambda (isposzero)
    (@ bind conv_monad (@ test_neg_zero ew mw f) (lambda (isnegzero)
      (@ arith size1 `(Or_op) isposzero isnegzero)))))))

(define test_pos_inf (lambdas (ew mw f)
  (@ bind conv_monad
    (@ load_Z (@ plus (to_nat ew) (to_nat mw))
      (@ mul1 (two_power_nat (to_nat mw))
        (@ sub1 (two_power_nat (to_nat ew)) `(Zpos ,`(XH)))))
    (lambda (posinf)
    (@ test (@ plus (to_nat ew) (to_nat mw)) `(Eq_op) f posinf)))))

(define test_neg_inf (lambdas (ew mw f)
  (@ bind conv_monad
    (@ load_Z (@ plus (to_nat ew) (to_nat mw))
      (@ mul1 (two_power_nat (to_nat mw))
        (@ sub1 (two_power_nat (@ plus (to_nat ew) `(S ,`(O)))) `(Zpos
          ,`(XH))))) (lambda (neginf)
    (@ test (@ plus (to_nat ew) (to_nat mw)) `(Eq_op) f neginf)))))

(define test_inf (lambdas (ew mw f)
  (@ bind conv_monad (@ test_pos_inf ew mw f) (lambda (isposinf)
    (@ bind conv_monad (@ test_neg_inf ew mw f) (lambda (isneginf)
      (@ arith size1 `(Or_op) isposinf isneginf)))))))

(define test_qnan (lambdas (ew mw f)
  (@ bind conv_monad
    (@ load_Z (@ plus (to_nat ew) (to_nat mw))
      (@ mul1 (two_power_nat (@ minus (to_nat mw) `(S ,`(O))))
        (@ sub1 (two_power_nat (@ plus (to_nat ew) `(S ,`(O)))) `(Zpos
          ,`(XH))))) (lambda (mask)
    (@ bind conv_monad
      (@ arith (@ plus (to_nat ew) (to_nat mw)) `(And_op) f mask)
      (lambda (maskRes)
      (@ test (@ plus (to_nat ew) (to_nat mw)) `(Eq_op) maskRes mask)))))))

(define test_snan (lambdas (ew mw f)
  (@ bind conv_monad (@ test_inf ew mw f) (lambda (isinf)
    (@ bind conv_monad (@ not0 size1 isinf) (lambda (isnotinf)
      (@ bind conv_monad
        (@ load_Z (@ plus (to_nat ew) (to_nat mw))
          (@ mul1 (two_power_nat (@ minus (to_nat mw) `(S ,`(O))))
            (@ sub1 (two_power_nat (@ plus (to_nat ew) `(S ,`(O)))) `(Zpos
              ,`(XH))))) (lambda (mask)
        (@ bind conv_monad
          (@ arith (@ plus (to_nat ew) (to_nat mw)) `(And_op) f mask)
          (lambda (maskRes)
          (@ bind conv_monad
            (@ load_Z (@ plus (to_nat ew) (to_nat mw))
              (@ mul1 (two_power_nat (to_nat mw))
                (@ sub1 (two_power_nat (to_nat ew)) `(Zpos ,`(XH)))))
            (lambda (expected)
            (@ bind conv_monad
              (@ test (@ plus (to_nat ew) (to_nat mw)) `(Eq_op) maskRes
                expected) (lambda (is_snan)
              (@ arith size1 `(And_op) isnotinf is_snan)))))))))))))))

(define test_nan (lambdas (ew mw f)
  (@ bind conv_monad (@ test_qnan ew mw f) (lambda (isqnan)
    (@ bind conv_monad (@ test_snan ew mw f) (lambda (issnan)
      (@ arith size1 `(Or_op) isqnan issnan)))))))

(define test_denormal (lambdas (ew mw f)
  (@ bind conv_monad (@ test_zero ew mw f) (lambda (iszero)
    (@ bind conv_monad (@ not0 size1 iszero) (lambda (isnotzero)
      (@ bind conv_monad
        (@ load_Z (@ plus (to_nat ew) (to_nat mw))
          (@ mul1 (two_power_nat (to_nat mw))
            (@ sub1 (two_power_nat (to_nat ew)) `(Zpos ,`(XH)))))
        (lambda (mask)
        (@ bind conv_monad
          (@ arith (@ plus (to_nat ew) (to_nat mw)) `(And_op) f mask)
          (lambda (maskRes)
          (@ bind conv_monad
            (@ load_Z (@ plus (to_nat ew) (to_nat mw)) `(Z0)) (lambda (zero2)
            (@ bind conv_monad
              (@ test (@ plus (to_nat ew) (to_nat mw)) `(Eq_op) maskRes
                zero2) (lambda (expZero)
              (@ arith size1 `(And_op) isnotzero expZero)))))))))))))))

(define test_normal_fin (lambdas (ew mw f)
  (@ bind conv_monad
    (@ load_Z (@ plus (to_nat ew) (to_nat mw))
      (@ mul1 (two_power_nat (to_nat mw))
        (@ sub1 (two_power_nat (to_nat ew)) `(Zpos ,`(XH))))) (lambda (mask)
    (@ bind conv_monad
      (@ arith (@ plus (to_nat ew) (to_nat mw)) `(And_op) f mask)
      (lambda (maskRes)
      (@ bind conv_monad (@ load_Z (@ plus (to_nat ew) (to_nat mw)) `(Z0))
        (lambda (zero2)
        (@ bind conv_monad
          (@ test (@ plus (to_nat ew) (to_nat mw)) `(Eq_op) maskRes zero2)
          (lambda (iszero)
          (@ bind conv_monad (@ not0 size1 iszero) (lambda (notzero)
            (@ bind conv_monad
              (@ test (@ plus (to_nat ew) (to_nat mw)) `(Eq_op) maskRes mask)
              (lambda (maxexpo)
              (@ bind conv_monad (@ not0 size1 maxexpo) (lambda (notmaxexpo)
                (@ arith size1 `(And_op) notzero notmaxexpo)))))))))))))))))

(define test_fin (lambdas (ew mw f)
  (@ bind conv_monad (@ test_denormal ew mw f) (lambda (isdefin)
    (@ bind conv_monad (@ test_normal_fin ew mw f) (lambda (isnorfin)
      (@ arith size1 `(Or_op) isdefin isnorfin)))))))

(define size63 `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(S ,`(S ,`(S ,`(S ,`(S
  ,`(O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(define de_float_of_float79 (lambda (f)
  (@ bind conv_monad (@ first_bits size16 size79 f) (lambda (signAndExpo)
    (@ bind conv_monad (@ last_bits size63 size79 f) (lambda (mantissa)
      (@ bind conv_monad
        (@ test_inf `(XI ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH)))))) `(XI ,`(XI ,`(XI
          ,`(XH)))) f) (lambda (isInf)
        (@ bind conv_monad
          (@ test_normal_fin `(XI ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH)))))) `(XI
            ,`(XI ,`(XI ,`(XH)))) f) (lambda (isNorFin)
          (@ bind conv_monad (@ arith size1 `(Or_op) isInf isNorFin)
            (lambda (intSig)
            (@ bind conv_monad (@ concat_bits size1 size63 intSig mantissa)
              (lambda (r)
              (@ concat_bits size16 (@ plus (@ plus size1 size63) `(S ,`(O)))
                signAndExpo r)))))))))))))))

(define float79_of_de_float (lambda (f)
  (@ bind conv_monad (@ first_bits size16 size80 f) (lambda (signAndExpo)
    (@ bind conv_monad (@ last_bits size63 size80 f) (lambda (mantissa)
      (@ concat_bits size16 size63 signAndExpo mantissa)))))))

(define de_float_of_float32 (lambdas (f rm)
  (@ bind conv_monad
    (@ fcast `(XO ,`(XO ,`(XO ,`(XH)))) `(XI ,`(XI ,`(XI ,`(XO ,`(XH)))))
      `(XI ,`(XI ,`(XI ,`(XH)))) `(XI ,`(XI ,`(XI ,`(XI ,`(XI ,`(XH)))))) rm
      f) (lambda (f~) (de_float_of_float79 f~)))))

(define de_float_of_float64 (lambdas (f rm)
  (@ bind conv_monad
    (@ fcast `(XI ,`(XI ,`(XO ,`(XH)))) `(XO ,`(XO ,`(XI ,`(XO ,`(XI
      ,`(XH)))))) `(XI ,`(XI ,`(XI ,`(XH)))) `(XI ,`(XI ,`(XI ,`(XI ,`(XI
      ,`(XH)))))) rm f) (lambda (f~) (de_float_of_float79 f~)))))

(define float32_of_de_float (lambdas (f rm)
  (@ bind conv_monad (float79_of_de_float f) (lambda (f~)
    (@ fcast `(XI ,`(XI ,`(XI ,`(XH)))) `(XI ,`(XI ,`(XI ,`(XI ,`(XI
      ,`(XH)))))) `(XO ,`(XO ,`(XO ,`(XH)))) `(XI ,`(XI ,`(XI ,`(XO
      ,`(XH))))) rm f~)))))

(define float64_of_de_float (lambdas (f rm)
  (@ bind conv_monad (float79_of_de_float f) (lambda (f~)
    (@ fcast `(XI ,`(XI ,`(XI ,`(XH)))) `(XI ,`(XI ,`(XI ,`(XI ,`(XI
      ,`(XH)))))) `(XI ,`(XI ,`(XO ,`(XH)))) `(XO ,`(XO ,`(XI ,`(XO ,`(XI
      ,`(XH)))))) rm f~)))))

(define enc_tag (lambda (f)
  (@ bind conv_monad (float79_of_de_float f) (lambda (nf)
    (@ bind conv_monad
      (@ test_zero `(XI ,`(XI ,`(XI ,`(XH)))) `(XI ,`(XI ,`(XI ,`(XI ,`(XI
        ,`(XH)))))) nf) (lambda (iszero)
      (@ bind conv_monad
        (@ test_normal_fin `(XI ,`(XI ,`(XI ,`(XH)))) `(XI ,`(XI ,`(XI ,`(XI
          ,`(XI ,`(XH)))))) nf) (lambda (isnorfin)
        (@ bind conv_monad (@ load_Z size2 (enc_fpu_tag_mode `(TM_valid)))
          (lambda (enc_valid)
          (@ bind conv_monad (@ load_Z size2 (enc_fpu_tag_mode `(TM_zero)))
            (lambda (enc_zero)
            (@ bind conv_monad
              (@ load_Z size2 (enc_fpu_tag_mode `(TM_special)))
              (lambda (enc_special)
              (@ bind conv_monad (@ if_exp size2 iszero enc_zero enc_special)
                (lambda (z_or_s) (@ if_exp size2 isnorfin enc_valid z_or_s)))))))))))))))))

(define load_ifp_op (lambdas (pre seg op)
  (match op
     ((Imm_op i)
       (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
         ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))))))))))))))))))))))))))))
         i))
     ((Reg_op r) (load_reg r))
     ((Address_op a)
       (@ bind conv_monad (compute_addr a) (lambda (p1)
         (@ load_mem32 seg p1))))
     ((Offset_op off)
       (@ bind conv_monad
         (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
           ,`(O)))))))))))))))))))))))))))))))) off) (lambda (p1)
         (@ load_mem32 seg p1)))))))

(define load_fp_op (lambdas (pre seg op)
  (let ((sr (@ get_segment pre seg)))
    (@ bind conv_monad get_fpu_rctrl (lambda (rm)
      (match op
         ((FPS_op i)
           (@ bind conv_monad (freg_of_offset i) (lambda (fi)
             (get_fpu_reg fi))))
         ((FPM16_op a)
           (@ bind conv_monad raise_error (lambda (x) (choose size80))))
         ((FPM32_op a)
           (@ bind conv_monad (compute_addr a) (lambda (addr)
             (@ bind conv_monad (@ load_mem32 sr addr) (lambda (val)
               (@ de_float_of_float32 val rm))))))
         ((FPM64_op a)
           (@ bind conv_monad (compute_addr a) (lambda (addr)
             (@ bind conv_monad (@ load_mem64 sr addr) (lambda (val)
               (@ de_float_of_float64 val rm))))))
         ((FPM80_op a)
           (@ bind conv_monad (compute_addr a) (lambda (addr)
             (@ load_mem80 sr addr))))))))))

(define conv_FNCLEX
  (@ bind conv_monad (@ set_fpu_flag_const `(F_PE) `(Z0)) (lambda (x)
    (@ bind conv_monad (@ set_fpu_flag_const `(F_UE) `(Z0)) (lambda (x0)
      (@ bind conv_monad (@ set_fpu_flag_const `(F_OE) `(Z0)) (lambda (x1)
        (@ bind conv_monad (@ set_fpu_flag_const `(F_ZE) `(Z0)) (lambda (x2)
          (@ bind conv_monad (@ set_fpu_flag_const `(F_DE) `(Z0))
            (lambda (x3)
            (@ bind conv_monad (@ set_fpu_flag_const `(F_IE) `(Z0))
              (lambda (x4)
              (@ bind conv_monad (@ set_fpu_flag_const `(F_ES) `(Z0))
                (lambda (x5) (@ set_fpu_flag_const `(F_Busy) `(Z0)))))))))))))))))

(define init_control_word
  (@ bind conv_monad (@ set_fpu_ctrl_const `(F_Res15) `(Z0)) (lambda (x)
    (@ bind conv_monad (@ set_fpu_ctrl_const `(F_Res14) `(Z0)) (lambda (x0)
      (@ bind conv_monad (@ set_fpu_ctrl_const `(F_Res13) `(Z0)) (lambda (x1)
        (@ bind conv_monad (@ set_fpu_ctrl_const `(F_IC) `(Z0)) (lambda (x2)
          (@ bind conv_monad (set_fpu_rctrl_const `(Mode_NE)) (lambda (x3)
            (@ bind conv_monad (set_fpu_pctrl_const `(PC_double_extended))
              (lambda (x4)
              (@ bind conv_monad (@ set_fpu_ctrl_const `(F_Res6) `(Z0))
                (lambda (x5)
                (@ bind conv_monad
                  (@ set_fpu_ctrl_const `(F_Res7) `(Zpos ,`(XH)))
                  (lambda (x6)
                  (@ bind conv_monad
                    (@ set_fpu_ctrl_const `(F_PM) `(Zpos ,`(XH)))
                    (lambda (x7)
                    (@ bind conv_monad
                      (@ set_fpu_ctrl_const `(F_UM) `(Zpos ,`(XH)))
                      (lambda (x8)
                      (@ bind conv_monad
                        (@ set_fpu_ctrl_const `(F_OM) `(Zpos ,`(XH)))
                        (lambda (x9)
                        (@ bind conv_monad
                          (@ set_fpu_ctrl_const `(F_ZM) `(Zpos ,`(XH)))
                          (lambda (x10)
                          (@ bind conv_monad
                            (@ set_fpu_ctrl_const `(F_DM) `(Zpos ,`(XH)))
                            (lambda (x11)
                            (@ set_fpu_ctrl_const `(F_IM) `(Zpos ,`(XH))))))))))))))))))))))))))))))

(define init_status_word
  (@ bind conv_monad (@ set_fpu_flag_const `(F_Busy) `(Z0)) (lambda (x)
    (@ bind conv_monad (@ set_fpu_flag_const `(F_C3) `(Z0)) (lambda (x0)
      (@ bind conv_monad (set_stktop_const `(Z0)) (lambda (x1)
        (@ bind conv_monad (@ set_fpu_flag_const `(F_C2) `(Z0)) (lambda (x2)
          (@ bind conv_monad (@ set_fpu_flag_const `(F_C1) `(Z0))
            (lambda (x3)
            (@ bind conv_monad (@ set_fpu_flag_const `(F_C0) `(Z0))
              (lambda (x4)
              (@ bind conv_monad (@ set_fpu_flag_const `(F_ES) `(Z0))
                (lambda (x5)
                (@ bind conv_monad (@ set_fpu_flag_const `(F_SF) `(Z0))
                  (lambda (x6)
                  (@ bind conv_monad (@ set_fpu_flag_const `(F_PE) `(Z0))
                    (lambda (x7)
                    (@ bind conv_monad (@ set_fpu_flag_const `(F_UE) `(Z0))
                      (lambda (x8)
                      (@ bind conv_monad (@ set_fpu_flag_const `(F_OE) `(Z0))
                        (lambda (x9)
                        (@ bind conv_monad
                          (@ set_fpu_flag_const `(F_ZE) `(Z0)) (lambda (x10)
                          (@ bind conv_monad
                            (@ set_fpu_flag_const `(F_DE) `(Z0))
                            (lambda (x11)
                            (@ set_fpu_flag_const `(F_IE) `(Z0)))))))))))))))))))))))))))))

(define init_tag_word
  (@ bind conv_monad (@ set_fpu_tag_const `(Z0) `(TM_empty)) (lambda (x)
    (@ bind conv_monad (@ set_fpu_tag_const `(Zpos ,`(XH)) `(TM_empty))
      (lambda (x0)
      (@ bind conv_monad
        (@ set_fpu_tag_const `(Zpos ,`(XO ,`(XH))) `(TM_empty)) (lambda (x1)
        (@ bind conv_monad
          (@ set_fpu_tag_const `(Zpos ,`(XI ,`(XH))) `(TM_empty))
          (lambda (x2)
          (@ bind conv_monad
            (@ set_fpu_tag_const `(Zpos ,`(XO ,`(XO ,`(XH)))) `(TM_empty))
            (lambda (x3)
            (@ bind conv_monad
              (@ set_fpu_tag_const `(Zpos ,`(XI ,`(XO ,`(XH)))) `(TM_empty))
              (lambda (x4)
              (@ bind conv_monad
                (@ set_fpu_tag_const `(Zpos ,`(XO ,`(XI ,`(XH))))
                  `(TM_empty)) (lambda (x5)
                (@ set_fpu_tag_const `(Zpos ,`(XI ,`(XI ,`(XH))))
                  `(TM_empty)))))))))))))))))

(define init_last_ptrs
  (@ bind conv_monad (set_fpu_lastInstrPtr_const `(Z0)) (lambda (x)
    (@ bind conv_monad (set_fpu_lastDataPtr_const `(Z0)) (lambda (x0)
      (set_fpu_lastOpcode_const `(Z0)))))))

(define conv_FNINIT
  (@ bind conv_monad init_control_word (lambda (x)
    (@ bind conv_monad init_status_word (lambda (x0)
      (@ bind conv_monad init_tag_word (lambda (x1) init_last_ptrs)))))))

(define conv_FINCSTP
  (@ bind conv_monad inc_stktop (lambda (x)
    (@ bind conv_monad (@ set_fpu_flag_const `(F_C1) `(Z0)) (lambda (x0)
      (@ bind conv_monad (undef_fpu_flag `(F_C0)) (lambda (x1)
        (@ bind conv_monad (undef_fpu_flag `(F_C2)) (lambda (x2)
          (undef_fpu_flag `(F_C3)))))))))))

(define conv_FDECSTP
  (@ bind conv_monad dec_stktop (lambda (x)
    (@ bind conv_monad (@ set_fpu_flag_const `(F_C1) `(Z0)) (lambda (x0)
      (@ bind conv_monad (undef_fpu_flag `(F_C0)) (lambda (x1)
        (@ bind conv_monad (undef_fpu_flag `(F_C2)) (lambda (x2)
          (undef_fpu_flag `(F_C3)))))))))))

(define stk_push_and_set_tag (lambda (f)
  (@ bind conv_monad (stk_push f) (lambda (x)
    (@ bind conv_monad get_stktop (lambda (topp)
      (@ bind conv_monad (enc_tag f) (lambda (tag)
        (@ bind conv_monad (@ set_fpu_tag topp tag) (lambda (x0)
          (is_nonempty_tag topp)))))))))))

(define conv_FLD (lambdas (pre op)
  (@ bind conv_monad (@ load_fp_op pre `(DS) op) (lambda (v)
    (@ bind conv_monad (stk_push_and_set_tag v) (lambda (overflow)
      (@ bind conv_monad (@ set_fpu_flag `(F_C1) overflow) (lambda (x)
        (@ bind conv_monad (undef_fpu_flag `(F_C0)) (lambda (x0)
          (@ bind conv_monad (undef_fpu_flag `(F_C2)) (lambda (x1)
            (undef_fpu_flag `(F_C3))))))))))))))

(define conv_FILD (lambdas (pre op)
  (@ bind conv_monad (@ load_fp_op pre `(DS) op) (lambda (v)
    (@ bind conv_monad (stk_push_and_set_tag v) (lambda (overflow)
      (@ bind conv_monad (@ set_fpu_flag `(F_C1) overflow) (lambda (x)
        (@ bind conv_monad (undef_fpu_flag `(F_C0)) (lambda (x0)
          (@ bind conv_monad (undef_fpu_flag `(F_C2)) (lambda (x1)
            (undef_fpu_flag `(F_C3))))))))))))))

(define load_stktop
  (@ bind conv_monad get_stktop (lambda (topp) (get_fpu_reg topp))))

(define conv_FST (lambdas (pre op)
  (@ bind conv_monad get_stktop (lambda (topp)
    (@ bind conv_monad (get_fpu_reg topp) (lambda (v)
      (@ bind conv_monad (is_empty_tag topp) (lambda (underflow)
        (@ bind conv_monad get_fpu_rctrl (lambda (rm)
          (let ((sr (@ get_segment pre `(DS))))
            (@ bind conv_monad
              (match op
                 ((FPS_op i)
                   (@ bind conv_monad (freg_of_offset i) (lambda (fi)
                     (@ set_fpu_reg fi v))))
                 ((FPM16_op a) raise_error)
                 ((FPM32_op a)
                   (@ bind conv_monad (compute_addr a) (lambda (addr)
                     (@ bind conv_monad (@ float32_of_de_float v rm)
                       (lambda (f32) (@ set_mem32 sr f32 addr))))))
                 ((FPM64_op a)
                   (@ bind conv_monad (compute_addr a) (lambda (addr)
                     (@ bind conv_monad (@ float64_of_de_float v rm)
                       (lambda (f64) (@ set_mem64 sr f64 addr))))))
                 ((FPM80_op a)
                   (@ bind conv_monad (compute_addr a) (lambda (addr)
                     (@ set_mem80 sr v addr))))) (lambda (x)
              (@ bind conv_monad (choose size1) (lambda (v0)
                (@ bind conv_monad (@ load_Z size1 `(Z0)) (lambda (zero2)
                  (@ bind conv_monad (@ if_exp size1 underflow zero2 v0)
                    (lambda (c1)
                    (@ bind conv_monad (@ set_fpu_flag `(F_C1) c1)
                      (lambda (x0)
                      (@ bind conv_monad (undef_fpu_flag `(F_C0))
                        (lambda (x1)
                        (@ bind conv_monad (undef_fpu_flag `(F_C2))
                          (lambda (x2) (undef_fpu_flag `(F_C3)))))))))))))))))))))))))))

(define conv_FIST (lambdas (pre op)
  (@ bind conv_monad get_stktop (lambda (topp)
    (@ bind conv_monad (get_fpu_reg topp) (lambda (v)
      (@ bind conv_monad (is_empty_tag topp) (lambda (underflow)
        (@ bind conv_monad get_fpu_rctrl (lambda (rm)
          (let ((sr (@ get_segment pre `(DS))))
            (@ bind conv_monad
              (match op
                 ((FPS_op i)
                   (@ bind conv_monad (freg_of_offset i) (lambda (fi)
                     (@ set_fpu_reg fi v))))
                 ((FPM16_op a) raise_error)
                 ((FPM32_op a)
                   (@ bind conv_monad (compute_addr a) (lambda (addr)
                     (@ bind conv_monad (@ float32_of_de_float v rm)
                       (lambda (f32) (@ set_mem32 sr f32 addr))))))
                 ((FPM64_op a)
                   (@ bind conv_monad (compute_addr a) (lambda (addr)
                     (@ bind conv_monad (@ float64_of_de_float v rm)
                       (lambda (f64) (@ set_mem64 sr f64 addr))))))
                 ((FPM80_op a)
                   (@ bind conv_monad (compute_addr a) (lambda (addr)
                     (@ set_mem80 sr v addr))))) (lambda (x)
              (@ bind conv_monad (choose size1) (lambda (v0)
                (@ bind conv_monad (@ load_Z size1 `(Z0)) (lambda (zero2)
                  (@ bind conv_monad (@ if_exp size1 underflow zero2 v0)
                    (lambda (c1)
                    (@ bind conv_monad (@ set_fpu_flag `(F_C1) c1)
                      (lambda (x0)
                      (@ bind conv_monad (undef_fpu_flag `(F_C0))
                        (lambda (x1)
                        (@ bind conv_monad (undef_fpu_flag `(F_C2))
                          (lambda (x2) (undef_fpu_flag `(F_C3)))))))))))))))))))))))))))

(define stk_pop_and_set_tag
  (@ bind conv_monad get_stktop (lambda (topp)
    (@ bind conv_monad (@ load_Z size2 (enc_fpu_tag_mode `(TM_empty)))
      (lambda (tag_emp)
      (@ bind conv_monad (@ set_fpu_tag topp tag_emp) (lambda (x)
        inc_stktop)))))))

(define conv_FSTP (lambdas (pre op)
  (@ bind conv_monad (@ conv_FST pre op) (lambda (x) stk_pop_and_set_tag))))

(define conv_FISTP (lambdas (pre op)
  (@ bind conv_monad (@ conv_FIST pre op) (lambda (x) stk_pop_and_set_tag))))

(define pos1 (void))

(define log2_10 (void))

(define log2_e (void))

(define pi (void))

(define log10_2 (void))

(define loge_2 (void))

(define conv_load_fpconstant (lambda (c)
  (@ bind conv_monad (@ load_int size80 c) (lambda (r)
    (@ bind conv_monad (stk_push_and_set_tag r) (lambda (overflow)
      (@ bind conv_monad (@ set_fpu_flag `(F_C1) overflow) (lambda (x)
        (@ bind conv_monad (undef_fpu_flag `(F_C0)) (lambda (x0)
          (@ bind conv_monad (undef_fpu_flag `(F_C2)) (lambda (x1)
            (undef_fpu_flag `(F_C3))))))))))))))

(define conv_FLDZ (conv_load_fpconstant (@ repr size80 `(Z0))))

(define conv_FLD1 (conv_load_fpconstant pos1))

(define conv_FLDPI (conv_load_fpconstant pi))

(define conv_FLDL2T (conv_load_fpconstant log2_10))

(define conv_FLDL2E (conv_load_fpconstant log2_e))

(define conv_FLDLG2 (conv_load_fpconstant log10_2))

(define conv_FLDLN2 (conv_load_fpconstant loge_2))

(define farith_de (lambdas (op rm e1 e2)
  (@ bind conv_monad (float79_of_de_float e1) (lambda (e1~)
    (@ bind conv_monad (float79_of_de_float e2) (lambda (e2~)
      (@ bind conv_monad (@ farith_float79 op rm e1~ e2~) (lambda (res)
        (de_float_of_float79 res)))))))))

(define conv_ifarith (lambdas (fop noreverse pre zerod op)
  (@ bind conv_monad (@ load_ifp_op pre `(DS) op) (lambda (iopv)
    (@ bind conv_monad get_fpu_rctrl (lambda (rm)
      (@ bind conv_monad (@ de_float_of_float32 iopv rm) (lambda (opv)
        (@ bind conv_monad get_stktop (lambda (topp)
          (@ bind conv_monad (get_fpu_reg topp) (lambda (st0)
            (@ bind conv_monad (is_empty_tag topp) (lambda (underflow)
              (@ bind conv_monad
                (match zerod
                   ((True)
                     (match noreverse
                        ((True) (@ farith_de fop rm st0 opv))
                        ((False) (@ farith_de fop rm opv st0))))
                   ((False)
                     (match noreverse
                        ((True) (@ farith_de fop rm opv st0))
                        ((False) (@ farith_de fop rm st0 opv)))))
                (lambda (res)
                (@ bind conv_monad (@ float32_of_de_float res rm)
                  (lambda (ires)
                  (@ bind conv_monad
                    (match op
                       ((Imm_op i) raise_error)
                       ((Reg_op r) (@ set_reg ires r))
                       ((Address_op a)
                         (@ bind conv_monad (compute_addr a) (lambda (addr)
                           (@ set_mem32 `(DS) ires addr))))
                       ((Offset_op off)
                         (@ bind conv_monad
                           (@ load_int `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                             ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                             ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
                             ,`(S ,`(S ,`(S ,`(S ,`(S
                             ,`(O)))))))))))))))))))))))))))))))) off)
                           (lambda (addr) (@ set_mem32 `(DS) ires addr)))))
                    (lambda (x)
                    (@ bind conv_monad (choose size1) (lambda (v)
                      (@ bind conv_monad (@ load_Z size1 `(Z0))
                        (lambda (zero2)
                        (@ bind conv_monad (@ if_exp size1 underflow zero2 v)
                          (lambda (c1)
                          (@ bind conv_monad (@ set_fpu_flag `(F_C1) c1)
                            (lambda (x0)
                            (@ bind conv_monad (undef_fpu_flag `(F_C0))
                              (lambda (x1)
                              (@ bind conv_monad (undef_fpu_flag `(F_C2))
                                (lambda (x2) (undef_fpu_flag `(F_C3))))))))))))))))))))))))))))))))))

(define conv_farith (lambdas (fop noreverse pre zerod op)
  (@ bind conv_monad (@ load_fp_op pre `(DS) op) (lambda (opv)
    (@ bind conv_monad get_stktop (lambda (topp)
      (@ bind conv_monad (get_fpu_reg topp) (lambda (st0)
        (@ bind conv_monad (is_empty_tag topp) (lambda (underflow)
          (@ bind conv_monad get_fpu_rctrl (lambda (rm)
            (@ bind conv_monad
              (match zerod
                 ((True)
                   (match noreverse
                      ((True) (@ farith_de fop rm st0 opv))
                      ((False) (@ farith_de fop rm opv st0))))
                 ((False)
                   (match noreverse
                      ((True) (@ farith_de fop rm opv st0))
                      ((False) (@ farith_de fop rm st0 opv))))) (lambda (res)
              (@ bind conv_monad
                (match zerod
                   ((True)
                     (match op
                        ((FPS_op i) (@ set_fpu_reg topp res))
                        ((FPM16_op a) raise_error)
                        ((FPM32_op a) (@ set_fpu_reg topp res))
                        ((FPM64_op a) (@ set_fpu_reg topp res))
                        ((FPM80_op a) raise_error)))
                   ((False)
                     (match op
                        ((FPS_op i)
                          (@ bind conv_monad (freg_of_offset i) (lambda (fi)
                            (@ set_fpu_reg fi res))))
                        ((FPM16_op a) raise_error)
                        ((FPM32_op a) raise_error)
                        ((FPM64_op a) raise_error)
                        ((FPM80_op a) raise_error)))) (lambda (x)
                (@ bind conv_monad (choose size1) (lambda (v)
                  (@ bind conv_monad (@ load_Z size1 `(Z0)) (lambda (zero2)
                    (@ bind conv_monad (@ if_exp size1 underflow zero2 v)
                      (lambda (c1)
                      (@ bind conv_monad (@ set_fpu_flag `(F_C1) c1)
                        (lambda (x0)
                        (@ bind conv_monad (undef_fpu_flag `(F_C0))
                          (lambda (x1)
                          (@ bind conv_monad (undef_fpu_flag `(F_C2))
                            (lambda (x2) (undef_fpu_flag `(F_C3))))))))))))))))))))))))))))))

(define conv_farith_and_pop (lambdas (fop noreverse pre op)
  (match op
     ((FPS_op i)
       (@ bind conv_monad (@ conv_farith fop noreverse pre `(False) op)
         (lambda (x) stk_pop_and_set_tag)))
     ((FPM16_op a) raise_error)
     ((FPM32_op a) raise_error)
     ((FPM64_op a) raise_error)
     ((FPM80_op a) raise_error))))

(define conv_FADD (@ conv_farith `(Fadd_op) `(True)))

(define conv_FSUB (@ conv_farith `(Fsub_op) `(True)))

(define conv_FMUL (@ conv_farith `(Fmul_op) `(True)))

(define conv_FDIV (@ conv_farith `(Fdiv_op) `(True)))

(define conv_FIADD (@ conv_ifarith `(Fadd_op) `(True)))

(define conv_FISUB (@ conv_ifarith `(Fsub_op) `(True)))

(define conv_FIMUL (@ conv_ifarith `(Fmul_op) `(True)))

(define conv_FIDIV (@ conv_ifarith `(Fdiv_op) `(True)))

(define conv_FADDP (@ conv_farith_and_pop `(Fadd_op) `(True)))

(define conv_FSUBP (@ conv_farith_and_pop `(Fsub_op) `(True)))

(define conv_FMULP (@ conv_farith_and_pop `(Fmul_op) `(True)))

(define conv_FDIVP (@ conv_farith_and_pop `(Fdiv_op) `(True)))

(define conv_FSUBR (@ conv_farith `(Fsub_op) `(False)))

(define conv_FDIVR (@ conv_farith `(Fdiv_op) `(False)))

(define conv_FISUBR (@ conv_ifarith `(Fsub_op) `(False)))

(define conv_FIDIVR (@ conv_ifarith `(Fdiv_op) `(False)))

(define conv_FSUBRP (@ conv_farith_and_pop `(Fsub_op) `(False)))

(define conv_FDIVRP (@ conv_farith_and_pop `(Fdiv_op) `(False)))

(define float_compare (lambdas (a b)
  (let ((aR
    (@ b2R `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XH)))))))) `(Zpos
      ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
      ,`(XO ,`(XO ,`(XH)))))))))))))))) a)))
    (let ((bR
      (@ b2R `(Zpos ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XH)))))))) `(Zpos
        ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO ,`(XO
        ,`(XO ,`(XO ,`(XO ,`(XH)))))))))))))))) b))) (@ rcompare aR bR)))))

(define set_CC_flags (lambda (comp)
  (match comp
     ((Eq)
       (@ bind conv_monad (@ set_fpu_flag_const `(F_C3) `(Zpos ,`(XH)))
         (lambda (x)
         (@ bind conv_monad (@ set_fpu_flag_const `(F_C2) `(Z0)) (lambda (x0)
           (@ set_fpu_flag_const `(F_C0) `(Z0)))))))
     ((Lt)
       (@ bind conv_monad (@ set_fpu_flag_const `(F_C3) `(Z0)) (lambda (x)
         (@ bind conv_monad (@ set_fpu_flag_const `(F_C2) `(Z0)) (lambda (x0)
           (@ set_fpu_flag_const `(F_C0) `(Zpos ,`(XH))))))))
     ((Gt)
       (@ bind conv_monad (@ set_fpu_flag_const `(F_C3) `(Z0)) (lambda (x)
         (@ bind conv_monad (@ set_fpu_flag_const `(F_C2) `(Z0)) (lambda (x0)
           (@ set_fpu_flag_const `(F_C0) `(Z0))))))))))

(define conv_FCOM (lambda (op1)
  (@ bind conv_monad get_stktop (lambda (topp)
    (@ bind conv_monad (get_fpu_reg topp) (lambda (st0)
      (@ bind conv_monad get_fpu_rctrl (lambda (rm)
        (match op1
           ((Some op)
             (match op
                ((FPS_op i) (undef_fpu_flag `(F_C3)))
                ((FPM16_op a) (undef_fpu_flag `(F_C3)))
                ((FPM32_op adr)
                  (@ bind conv_monad (compute_addr adr) (lambda (addr)
                    (@ bind conv_monad (@ load_mem32 `(DS) addr)
                      (lambda (val)
                      (@ bind conv_monad (@ de_float_of_float32 val rm)
                        (lambda (d_val) (undef_fpu_flag `(F_C3)))))))))
                ((FPM64_op adr)
                  (@ bind conv_monad (compute_addr adr) (lambda (addr)
                    (@ bind conv_monad (@ load_mem64 `(DS) addr)
                      (lambda (val)
                      (@ bind conv_monad (@ de_float_of_float64 val rm)
                        (lambda (d_val) (undef_fpu_flag `(F_C3)))))))))
                ((FPM80_op a) (undef_fpu_flag `(F_C3)))))
           ((None) (undef_fpu_flag `(F_C3))))))))))))

(define conv_FICOM (lambda (op1)
  (@ bind conv_monad get_stktop (lambda (topp)
    (@ bind conv_monad (get_fpu_reg topp) (lambda (st0)
      (@ bind conv_monad get_fpu_rctrl (lambda (rm)
        (match op1
           ((Some op)
             (match op
                ((FPS_op i) (undef_fpu_flag `(F_C3)))
                ((FPM16_op a) (undef_fpu_flag `(F_C3)))
                ((FPM32_op adr)
                  (@ bind conv_monad (compute_addr adr) (lambda (addr)
                    (@ bind conv_monad (@ load_mem32 `(DS) addr)
                      (lambda (val)
                      (@ bind conv_monad (@ de_float_of_float32 val rm)
                        (lambda (d_val) (undef_fpu_flag `(F_C3)))))))))
                ((FPM64_op adr)
                  (@ bind conv_monad (compute_addr adr) (lambda (addr)
                    (@ bind conv_monad (@ load_mem64 `(DS) addr)
                      (lambda (val)
                      (@ bind conv_monad (@ de_float_of_float64 val rm)
                        (lambda (d_val) (undef_fpu_flag `(F_C3)))))))))
                ((FPM80_op a) (undef_fpu_flag `(F_C3)))))
           ((None) (undef_fpu_flag `(F_C3))))))))))))

(define conv_FCOMP (lambda (op1)
  (@ bind conv_monad (conv_FCOM op1) (lambda (x) stk_pop_and_set_tag))))

(define conv_FCOMPP
  (@ bind conv_monad (conv_FCOMP `(None)) (lambda (x) stk_pop_and_set_tag)))

(define conv_FICOMP (lambda (op1)
  (@ bind conv_monad (conv_FICOM op1) (lambda (x) stk_pop_and_set_tag))))

(define conv_FICOMPP
  (@ bind conv_monad (conv_FICOMP `(None)) (lambda (x) stk_pop_and_set_tag)))

(define instr_to_rtl (lambdas (pre i)
  (runConv
    (@ bind conv_monad (check_prefix pre) (lambda (x)
      (match i
         ((AAA) (conv_AAA_AAS `(Add_op)))
         ((AAD) conv_AAD)
         ((AAM) conv_AAM)
         ((AAS) (conv_AAA_AAS `(Sub_op)))
         ((ADC w op1 op2) (@ conv_ADC pre w op1 op2))
         ((ADD w op1 op2) (@ conv_ADD pre w op1 op2))
         ((AND w op1 op2) (@ conv_AND pre w op1 op2))
         ((ARPL op1 op2) raise_error)
         ((BOUND op1 op2) raise_trap)
         ((BSF op1 op2) (@ conv_BSF pre op1 op2))
         ((BSR op1 op2) (@ conv_BSR pre op1 op2))
         ((BSWAP r) (@ conv_BSWAP pre r))
         ((BT op1 op2) (@ conv_BT `(False) `(True) pre op1 op2))
         ((BTC op1 op2) (@ conv_BT `(False) `(False) pre op1 op2))
         ((BTR op1 op2) (@ conv_BT `(True) `(False) pre op1 op2))
         ((BTS op1 op2) (@ conv_BT `(True) `(True) pre op1 op2))
         ((CALL near abs0 op1 sel) (@ conv_CALL pre near abs0 op1 sel))
         ((CDQ) (conv_CDQ pre))
         ((CLC) conv_CLC)
         ((CLD) conv_CLD)
         ((CLI) raise_trap)
         ((CLTS) raise_trap)
         ((CMC) conv_CMC)
         ((CMOVcc ct op1 op2) (@ conv_CMOV pre `(True) ct op1 op2))
         ((CMP w op1 op2) (@ conv_CMP pre w op1 op2))
         ((CMPS w) (@ conv_CMPS pre w))
         ((CMPXCHG w op1 op2) (@ conv_CMPXCHG pre w op1 op2))
         ((CPUID) raise_trap)
         ((CWDE) (conv_CWDE pre))
         ((DAA) (@ conv_DAA_DAS `(Add_op) (testcarryAdd size8)))
         ((DAS) (@ conv_DAA_DAS `(Sub_op) (testcarrySub size8)))
         ((DEC w op1) (@ conv_DEC pre w op1))
         ((DIV w op) (@ conv_DIV pre w op))
         ((F2XM1) raise_error)
         ((FABS) raise_error)
         ((FADD zerod op1) raise_error)
         ((FADDP op1) raise_error)
         ((FBLD op1) raise_error)
         ((FBSTP op1) raise_error)
         ((FCHS) raise_error)
         ((FCMOVcc ct op1) raise_error)
         ((FCOM op1) raise_error)
         ((FCOMP op1) raise_error)
         ((FCOMPP) raise_error)
         ((FCOMIP op1) raise_error)
         ((FCOS) raise_error)
         ((FDECSTP) raise_error)
         ((FDIV zerod op) raise_error)
         ((FDIVP op1) raise_error)
         ((FDIVR zerod op) raise_error)
         ((FDIVRP op1) raise_error)
         ((FFREE op1) raise_error)
         ((FIADD op1) raise_error)
         ((FICOM op1) raise_error)
         ((FICOMP op1) raise_error)
         ((FIDIV op1) raise_error)
         ((FIDIVR op1) raise_error)
         ((FILD op1) raise_error)
         ((FIMUL op1) raise_error)
         ((FINCSTP) raise_error)
         ((FIST op1) raise_error)
         ((FISTP op1) raise_error)
         ((FISUB op1) raise_error)
         ((FISUBR op1) raise_error)
         ((FLD op1) raise_error)
         ((FLD1) raise_error)
         ((FLDCW op1) raise_error)
         ((FLDENV op1) raise_error)
         ((FLDL2E) raise_error)
         ((FLDL2T) raise_error)
         ((FLDLG2) raise_error)
         ((FLDLN2) raise_error)
         ((FLDPI) raise_error)
         ((FLDZ) raise_error)
         ((FMUL zerod op1) raise_error)
         ((FMULP op1) raise_error)
         ((FNCLEX) raise_error)
         ((FNINIT) raise_error)
         ((FNOP) raise_error)
         ((FNSAVE op1) raise_error)
         ((FNSTCW op1) raise_error)
         ((FNSTSW op1) raise_error)
         ((FPATAN) raise_error)
         ((FPREM) raise_error)
         ((FPREM1) raise_error)
         ((FPTAN) raise_error)
         ((FRNDINT) raise_error)
         ((FRSTOR op1) raise_error)
         ((FSCALE) raise_error)
         ((FSIN) raise_error)
         ((FSINCOS) raise_error)
         ((FSQRT) raise_error)
         ((FST op1) raise_error)
         ((FSTENV op1) raise_error)
         ((FSTP op1) raise_error)
         ((FSUB zerod op) raise_error)
         ((FSUBP op1) raise_error)
         ((FSUBR zerod op) raise_error)
         ((FSUBRP op1) raise_error)
         ((FTST) raise_error)
         ((FUCOM op1) raise_error)
         ((FUCOMP op1) raise_error)
         ((FUCOMPP) raise_error)
         ((FUCOMI op1) raise_error)
         ((FUCOMIP op1) raise_error)
         ((FXAM) raise_error)
         ((FXCH op1) raise_error)
         ((FXTRACT) raise_error)
         ((FYL2X) raise_error)
         ((FYL2XP1) raise_error)
         ((FWAIT) raise_error)
         ((EMMS) raise_error)
         ((MOVD op1 op2) raise_error)
         ((MOVQ op1 op2) raise_error)
         ((PACKSSDW op1 op2) raise_error)
         ((PACKSSWB op1 op2) raise_error)
         ((PACKUSWB op1 op2) raise_error)
         ((PADD gg op1 op2) raise_error)
         ((PADDS gg op1 op2) raise_error)
         ((PADDUS gg op1 op2) raise_error)
         ((PAND op1 op2) raise_error)
         ((PANDN op1 op2) raise_error)
         ((PCMPEQ gg op1 op2) raise_error)
         ((PCMPGT gg op1 op2) raise_error)
         ((PMADDWD op1 op2) raise_error)
         ((PMULHUW op1 op2) raise_error)
         ((PMULHW op1 op2) raise_error)
         ((PMULLW op1 op2) raise_error)
         ((POR op1 op2) raise_error)
         ((PSLL gg op1 op2) raise_error)
         ((PSRA gg op1 op2) raise_error)
         ((PSRL gg op1 op2) raise_error)
         ((PSUB gg op1 op2) raise_error)
         ((PSUBS gg op1 op2) raise_error)
         ((PSUBUS gg op1 op2) raise_error)
         ((PUNPCKH gg op1 op2) raise_error)
         ((PUNPCKL gg op1 op2) raise_error)
         ((PXOR op1 op2) raise_error)
         ((ADDPS op1 op2) raise_error)
         ((ADDSS op1 op2) raise_error)
         ((ANDNPS op1 op2) raise_error)
         ((ANDPS op1 op2) raise_error)
         ((CMPPS op1 op2 imm) raise_error)
         ((CMPSS op1 op2 imm) raise_error)
         ((COMISS op1 op2) raise_error)
         ((CVTPI2PS op1 op2) raise_error)
         ((CVTPS2PI op1 op2) raise_error)
         ((CVTSI2SS op1 op2) raise_error)
         ((CVTSS2SI op1 op2) raise_error)
         ((CVTTPS2PI op1 op2) raise_error)
         ((CVTTSS2SI op1 op2) raise_error)
         ((DIVPS op1 op2) raise_error)
         ((DIVSS op1 op2) raise_error)
         ((LDMXCSR op1) raise_error)
         ((MAXPS op1 op2) raise_error)
         ((MAXSS op1 op2) raise_error)
         ((MINPS op1 op2) raise_error)
         ((MINSS op1 op2) raise_error)
         ((MOVAPS op1 op2) raise_error)
         ((MOVHLPS op1 op2) raise_error)
         ((MOVHPS op1 op2) raise_error)
         ((MOVLHPS op1 op2) raise_error)
         ((MOVLPS op1 op2) raise_error)
         ((MOVMSKPS op1 op2) raise_error)
         ((MOVSS op1 op2) raise_error)
         ((MOVUPS op1 op2) raise_error)
         ((MULPS op1 op2) raise_error)
         ((MULSS op1 op2) raise_error)
         ((ORPS op1 op2) raise_error)
         ((RCPPS op1 op2) raise_error)
         ((RCPSS op1 op2) raise_error)
         ((RSQRTPS op1 op2) raise_error)
         ((RSQRTSS op1 op2) raise_error)
         ((SHUFPS op1 op2 imm) raise_error)
         ((SQRTPS op1 op2) raise_error)
         ((SQRTSS op1 op2) raise_error)
         ((STMXCSR op1) raise_error)
         ((SUBPS op1 op2) raise_error)
         ((SUBSS op1 op2) raise_error)
         ((UCOMISS op1 op2) raise_error)
         ((UNPCKHPS op1 op2) raise_error)
         ((UNPCKLPS op1 op2) raise_error)
         ((XORPS op1 op2) raise_error)
         ((PAVGB op1 op2) raise_error)
         ((PEXTRW op1 op2 imm) raise_error)
         ((PINSRW op1 op2 imm) raise_error)
         ((PMAXSW op1 op2) raise_error)
         ((PMAXUB op1 op2) raise_error)
         ((PMINSW op1 op2) raise_error)
         ((PMINUB op1 op2) raise_error)
         ((PMOVMSKB op1 op2) raise_error)
         ((PSADBW op1 op2) raise_error)
         ((PSHUFW op1 op2 imm) raise_error)
         ((MASKMOVQ op1 op2) raise_error)
         ((MOVNTPS op1 op2) raise_error)
         ((MOVNTQ op1 op2) raise_error)
         ((PREFETCHT0 op1) raise_error)
         ((PREFETCHT1 op1) raise_error)
         ((PREFETCHT2 op1) raise_error)
         ((PREFETCHNTA op1) raise_error)
         ((SFENCE) raise_error)
         ((HLT) (conv_HLT pre))
         ((IDIV w op) (@ conv_IDIV pre w op))
         ((IMUL w op1 op2 i0) (@ conv_IMUL pre w op1 op2 i0))
         ((IN w p) raise_error)
         ((INC w op1) (@ conv_INC pre w op1))
         ((INS w) raise_error)
         ((INTn it) raise_error)
         ((INT) raise_error)
         ((INTO) raise_error)
         ((INVD) raise_error)
         ((INVLPG op1) raise_error)
         ((IRET) raise_error)
         ((Jcc ct disp) (@ conv_Jcc pre ct disp))
         ((JCXZ b) raise_error)
         ((JMP near abs0 op1 sel) (@ conv_JMP pre near abs0 op1 sel))
         ((LAHF) conv_LAHF)
         ((LAR op1 op2) raise_trap)
         ((LDS op1 op2) raise_error)
         ((LEA op1 op2) (@ conv_LEA pre op1 op2))
         ((LEAVE) (conv_LEAVE pre))
         ((LES op1 op2) raise_error)
         ((LFS op1 op2) raise_error)
         ((LGDT op1) raise_error)
         ((LGS op1 op2) raise_trap)
         ((LIDT op1) raise_error)
         ((LLDT op1) raise_error)
         ((LMSW op1) raise_error)
         ((LODS w) raise_error)
         ((LOOP disp) (@ conv_LOOP pre `(False) `(False) disp))
         ((LOOPZ disp) (@ conv_LOOP pre `(True) `(True) disp))
         ((LOOPNZ disp) (@ conv_LOOP pre `(True) `(False) disp))
         ((LSL op1 op2) raise_error)
         ((LSS op1 op2) raise_error)
         ((LTR op1) raise_error)
         ((MOV w op1 op2) (@ conv_MOV pre w op1 op2))
         ((MOVCR direction cr r) raise_trap)
         ((MOVDR direction dr r) raise_trap)
         ((MOVSR direction sr op1) raise_trap)
         ((MOVBE op1 op2) raise_trap)
         ((MOVS w) (@ conv_MOVS pre w))
         ((MOVSX w op1 op2) (@ conv_MOVSX pre w op1 op2))
         ((MOVZX w op1 op2) (@ conv_MOVZX pre w op1 op2))
         ((MUL w op) (@ conv_MUL pre w op))
         ((NEG w op1) (@ conv_NEG pre w op1))
         ((NOP op) (@ return conv_monad `(Tt)))
         ((NOT w op1) (@ conv_NOT pre w op1))
         ((OR w op1 op2) (@ conv_OR pre w op1 op2))
         ((OUT w p) raise_error)
         ((OUTS w) raise_error)
         ((POP op) (@ conv_POP pre op))
         ((POPSR sr) raise_error)
         ((POPA) (conv_POPA pre))
         ((POPF) raise_trap)
         ((PUSH w op) (@ conv_PUSH pre w op))
         ((PUSHSR sr) raise_trap)
         ((PUSHA) (conv_PUSHA pre))
         ((PUSHF) raise_trap)
         ((RCL w op1 op2) (@ conv_RCL pre w op1 op2))
         ((RCR w op1 op2) (@ conv_RCR pre w op1 op2))
         ((RDMSR) raise_trap)
         ((RDPMC) raise_trap)
         ((RDTSC) raise_trap)
         ((RDTSCP) raise_trap)
         ((RET ss disp) (@ conv_RET pre ss disp))
         ((ROL w op1 op2) (@ conv_ROL pre w op1 op2))
         ((ROR w op1 op2) (@ conv_ROR pre w op1 op2))
         ((RSM) raise_trap)
         ((SAHF) conv_SAHF)
         ((SAR w op1 op2) (@ conv_SAR pre w op1 op2))
         ((SBB w op1 op2) (@ conv_SBB pre w op1 op2))
         ((SCAS w) raise_trap)
         ((SETcc ct op) (@ conv_SETcc pre ct op))
         ((SGDT op1) raise_trap)
         ((SHL w op1 op2) (@ conv_SHL pre w op1 op2))
         ((SHLD op1 op2 ri) (@ conv_SHLD pre op1 op2 ri))
         ((SHR w op1 op2) (@ conv_SHR pre w op1 op2))
         ((SHRD op1 op2 ri) (@ conv_SHRD pre op1 op2 ri))
         ((SIDT op1) raise_trap)
         ((SLDT op1) raise_trap)
         ((SMSW op1) raise_trap)
         ((STC) conv_STC)
         ((STD) conv_STD)
         ((STI) raise_trap)
         ((STOS w) (@ conv_STOS pre w))
         ((STR op1) raise_trap)
         ((SUB w op1 op2) (@ conv_SUB pre w op1 op2))
         ((TEST w op1 op2) (@ conv_TEST pre w op1 op2))
         ((UD2) raise_error)
         ((VERR op1) raise_error)
         ((VERW op1) raise_error)
         ((WBINVD) raise_trap)
         ((WRMSR) raise_error)
         ((XADD w op1 op2) (@ conv_XADD pre w op1 op2))
         ((XCHG w op1 op2) (@ conv_XCHG pre w op1 op2))
         ((XLAT) raise_error)
         ((XOR w op1 op2) (@ conv_XOR pre w op1 op2))))))))

(define rTL_step_list (lambda (l)
  (match l
     ((Nil) (@ return rTL_monad `(Tt)))
     ((Cons i l~)
       (@ bind rTL_monad (interp_rtl i) (lambda (x) (rTL_step_list l~)))))))
  
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

(define no_prefix `(MkPrefix ,`(None) ,`(None) ,`(False) ,`(False)))

(define four `(Zpos ,`(XO ,`(XO ,`(XH)))))

(define six `(Zpos ,`(XO ,`(XI ,`(XH)))))

(define eax_plus (lambda (n)
  (@ instr_to_rtl no_prefix `(ADD ,`(False) ,`(Reg_op ,`(EAX)) ,`(Imm_op
    ,n)))))

(define add3 (lambdas (n m) (@ app (eax_plus n) (eax_plus m))))

(define run (lambda (p) (@ rTL_step_list p init_rtl_state)))

(define (four_plus_six)
  (let ((s (run (@ add3 four six))))
    `(Pair ,(fst s) ,(@ gp_regs (core (rtl_mach_state (snd s))) `(EAX)))))

(write-string "starting\n")
(flush-output)
(displayln (profile (four_plus_six)))
