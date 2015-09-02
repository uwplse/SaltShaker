{-# OPTIONS_GHC -cpp -XConstrainedClassMethods -XDeriveDataTypeable
-XDeriveFoldable -XDeriveFunctor -XDeriveGeneric -XDeriveTraversable
-XEmptyDataDecls -XExistentialQuantification -XExplicitNamespaces
-XFlexibleContexts -XFlexibleInstances -XForeignFunctionInterface
-XFunctionalDependencies -XGeneralizedNewtypeDeriving -XImplicitParams
-XKindSignatures -XLiberalTypeSynonyms -XMagicHash -XMultiParamTypeClasses
-XParallelListComp -XPatternGuards -XPostfixOperators -XRankNTypes
-XScopedTypeVariables -XStandaloneDeriving -XTypeOperators
-XTypeSynonymInstances -XUnboxedTuples -XUnicodeSyntax -XUnliftedFFITypes #-}

module X86sem where

import qualified Prelude

import qualified GHC.Base

unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f y =
  eq_rect x f y

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x h y =
  eq_rec x h y

data Unit =
   Tt
   deriving (Prelude.Show) 

data Bool =
   True
 | False

bool_rect :: a1 -> a1 -> Bool -> a1
bool_rect f f0 b =
  case b of {
   True -> f;
   False -> f0}

bool_rec :: a1 -> a1 -> Bool -> a1
bool_rec =
  bool_rect

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

xorb :: Bool -> Bool -> Bool
xorb b1 b2 =
  case b1 of {
   True ->
    case b2 of {
     True -> False;
     False -> True};
   False -> b2}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

option_rect :: (a1 -> a2) -> a2 -> (Option a1) -> a2
option_rect f f0 o =
  case o of {
   Some x -> f x;
   None -> f0}

data Prod a b =
   Pair a b
   deriving (Prelude.Show) 

prod_rect :: (a1 -> a2 -> a3) -> (Prod a1 a2) -> a3
prod_rect f p =
  case p of {
   Pair x x0 -> f x x0}

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x y -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair x y -> y}

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

compareSpec2Type :: Comparison -> CompareSpecT
compareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Comparison -> CompSpecT a1
compSpec2Type x y c =
  compareSpec2Type c

id :: a1 -> a1
id x =
  x

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Sumor a =
   Inleft a
 | Inright

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

mult :: Nat -> Nat -> Nat
mult n m =
  case n of {
   O -> O;
   S p -> plus m (mult p m)}

minus :: Nat -> Nat -> Nat
minus n m =
  case n of {
   O -> n;
   S k ->
    case m of {
     O -> n;
     S l -> minus k l}}

nat_iter :: Nat -> (a1 -> a1) -> a1 -> a1
nat_iter n f x =
  case n of {
   O -> x;
   S n' -> f (nat_iter n' f x)}

bool_dec :: Bool -> Bool -> Sumbool
bool_dec b1 b2 =
  bool_rec (\b0 ->
    case b0 of {
     True -> Left;
     False -> Right}) (\b0 ->
    case b0 of {
     True -> Right;
     False -> Left}) b1 b2

eqb :: Bool -> Bool -> Bool
eqb b1 b2 =
  case b1 of {
   True -> b2;
   False ->
    case b2 of {
     True -> False;
     False -> True}}

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Bool -> Reflect
iff_reflect b =
  case b of {
   True -> and_rec (\_ _ -> ReflectT);
   False -> and_rec (\_ _ -> ReflectF)}

rev :: (List a1) -> List a1
rev l =
  case l of {
   Nil -> Nil;
   Cons x l' -> app (rev l') (Cons x Nil)}

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

data Positive =
   XI Positive
 | XO Positive
 | XH
 deriving (Prelude.Show) 

positive_rect :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                 Positive -> a1
positive_rect f f0 f1 p =
  case p of {
   XI p0 -> f p0 (positive_rect f f0 f1 p0);
   XO p0 -> f0 p0 (positive_rect f f0 f1 p0);
   XH -> f1}

positive_rec :: (Positive -> a1 -> a1) -> (Positive -> a1 -> a1) -> a1 ->
                Positive -> a1
positive_rec =
  positive_rect

data N =
   N0
 | Npos Positive

n_rect :: a1 -> (Positive -> a1) -> N -> a1
n_rect f f0 n =
  case n of {
   N0 -> f;
   Npos x -> f0 x}

n_rec :: a1 -> (Positive -> a1) -> N -> a1
n_rec =
  n_rect

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive
 deriving (Prelude.Show) 

z_rect :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rect f f0 f1 z =
  case z of {
   Z0 -> f;
   Zpos x -> f0 x;
   Zneg x -> f1 x}

z_rec :: a1 -> (Positive -> a1) -> (Positive -> a1) -> Z -> a1
z_rec =
  z_rect

type T = Positive

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add :: Positive -> Positive -> Positive
add x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
     XH -> XI p};
   XH ->
    case y of {
     XI q -> XO (succ q);
     XO q -> XI q;
     XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XH ->
    case y of {
     XI q -> XI (succ q);
     XO q -> XO (succ q);
     XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

pred :: Positive -> Positive
pred x =
  case x of {
   XI p -> XO p;
   XO p -> pred_double p;
   XH -> XH}

pred_N :: Positive -> N
pred_N x =
  case x of {
   XI p -> Npos (XO p);
   XO p -> Npos (pred_double p);
   XH -> N0}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

mask_rect :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rect f f0 f1 m =
  case m of {
   IsNul -> f;
   IsPos x -> f0 x;
   IsNeg -> f1}

mask_rec :: a1 -> (Positive -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double p));
   XH -> IsNul}

pred_mask :: Mask -> Mask
pred_mask p =
  case p of {
   IsPos q ->
    case q of {
     XH -> IsNul;
     _ -> IsPos (pred q)};
   _ -> IsNeg}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH ->
    case y of {
     XH -> IsNul;
     _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

iter :: Positive -> (a1 -> a1) -> a1 -> a1
iter n f x =
  case n of {
   XI n' -> f (iter n' f (iter n' f x));
   XO n' -> iter n' f (iter n' f x);
   XH -> f x}

pow :: Positive -> Positive -> Positive
pow x y =
  iter y (mul x) XH

square :: Positive -> Positive
square p =
  case p of {
   XI p0 -> XI (XO (add (square p0) p0));
   XO p0 -> XO (XO (square p0));
   XH -> XH}

div2 :: Positive -> Positive
div2 p =
  case p of {
   XI p0 -> p0;
   XO p0 -> p0;
   XH -> XH}

div2_up :: Positive -> Positive
div2_up p =
  case p of {
   XI p0 -> succ p0;
   XO p0 -> p0;
   XH -> XH}

size_nat :: Positive -> Nat
size_nat p =
  case p of {
   XI p0 -> S (size_nat p0);
   XO p0 -> S (size_nat p0);
   XH -> S O}

size :: Positive -> Positive
size p =
  case p of {
   XI p0 -> succ (size p0);
   XO p0 -> succ (size p0);
   XH -> XH}

compare_cont :: Positive -> Positive -> Comparison -> Comparison
compare_cont x y r =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont p q r;
     XO q -> compare_cont p q Gt;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont p q Lt;
     XO q -> compare_cont p q r;
     XH -> Gt};
   XH ->
    case y of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare x y =
  compare_cont x y Eq

min :: Positive -> Positive -> Positive
min p p' =
  case compare p p' of {
   Gt -> p';
   _ -> p}

max :: Positive -> Positive -> Positive
max p p' =
  case compare p p' of {
   Gt -> p;
   _ -> p'}

eqb0 :: Positive -> Positive -> Bool
eqb0 p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> eqb0 p0 q0;
     _ -> False};
   XO p0 ->
    case q of {
     XO q0 -> eqb0 p0 q0;
     _ -> False};
   XH ->
    case q of {
     XH -> True;
     _ -> False}}

leb :: Positive -> Positive -> Bool
leb x y =
  case compare x y of {
   Gt -> False;
   _ -> True}

ltb :: Positive -> Positive -> Bool
ltb x y =
  case compare x y of {
   Lt -> True;
   _ -> False}

sqrtrem_step :: (Positive -> Positive) -> (Positive -> Positive) -> (Prod
                Positive Mask) -> Prod Positive Mask
sqrtrem_step f g p =
  case p of {
   Pair s y ->
    case y of {
     IsPos r ->
      let {s' = XI (XO s)} in
      let {r' = g (f r)} in
      case leb s' r' of {
       True -> Pair (XI s) (sub_mask r' s');
       False -> Pair (XO s) (IsPos r')};
     _ -> Pair (XO s) (sub_mask (g (f XH)) (XO (XO XH)))}}

sqrtrem :: Positive -> Prod Positive Mask
sqrtrem p =
  case p of {
   XI p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XI x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XI x) (sqrtrem p1);
     XH -> Pair XH (IsPos (XO XH))};
   XO p0 ->
    case p0 of {
     XI p1 -> sqrtrem_step (\x -> XI x) (\x -> XO x) (sqrtrem p1);
     XO p1 -> sqrtrem_step (\x -> XO x) (\x -> XO x) (sqrtrem p1);
     XH -> Pair XH (IsPos XH)};
   XH -> Pair XH IsNul}

sqrt :: Positive -> Positive
sqrt p =
  fst (sqrtrem p)

gcdn :: Nat -> Positive -> Positive -> Positive
gcdn n a b =
  case n of {
   O -> XH;
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> a;
         Lt -> gcdn n0 (sub b' a') a;
         Gt -> gcdn n0 (sub a' b') b};
       XO b0 -> gcdn n0 a b0;
       XH -> XH};
     XO a0 ->
      case b of {
       XI p -> gcdn n0 a0 b;
       XO b0 -> XO (gcdn n0 a0 b0);
       XH -> XH};
     XH -> XH}}

gcd :: Positive -> Positive -> Positive
gcd a b =
  gcdn (plus (size_nat a) (size_nat b)) a b

ggcdn :: Nat -> Positive -> Positive -> Prod Positive
         (Prod Positive Positive)
ggcdn n a b =
  case n of {
   O -> Pair XH (Pair a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> Pair a (Pair XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           Pair g p ->
            case p of {
             Pair ba aa -> Pair g (Pair aa (add aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           Pair g p ->
            case p of {
             Pair ab bb -> Pair g (Pair (add bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         Pair g p ->
          case p of {
           Pair aa bb -> Pair g (Pair aa (XO bb))}};
       XH -> Pair XH (Pair a XH)};
     XO a0 ->
      case b of {
       XI p ->
        case ggcdn n0 a0 b of {
         Pair g p0 ->
          case p0 of {
           Pair aa bb -> Pair g (Pair (XO aa) bb)}};
       XO b0 ->
        case ggcdn n0 a0 b0 of {
         Pair g p -> Pair (XO g) p};
       XH -> Pair XH (Pair a XH)};
     XH -> Pair XH (Pair XH b)}}

ggcd :: Positive -> Positive -> Prod Positive (Prod Positive Positive)
ggcd a b =
  ggcdn (plus (size_nat a) (size_nat b)) a b

nsucc_double :: N -> N
nsucc_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

ndouble :: N -> N
ndouble n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

lor :: Positive -> Positive -> Positive
lor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XI (lor p0 q0);
     XH -> p};
   XO p0 ->
    case q of {
     XI q0 -> XI (lor p0 q0);
     XO q0 -> XO (lor p0 q0);
     XH -> XI p0};
   XH ->
    case q of {
     XO q0 -> XI q0;
     _ -> q}}

land :: Positive -> Positive -> N
land p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> nsucc_double (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> Npos XH};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (land p0 q0);
     XO q0 -> ndouble (land p0 q0);
     XH -> N0};
   XH ->
    case q of {
     XO q0 -> N0;
     _ -> Npos XH}}

ldiff :: Positive -> Positive -> N
ldiff p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> nsucc_double (ldiff p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> ndouble (ldiff p0 q0);
     XO q0 -> ndouble (ldiff p0 q0);
     XH -> Npos p};
   XH ->
    case q of {
     XO q0 -> Npos XH;
     _ -> N0}}

lxor :: Positive -> Positive -> N
lxor p q =
  case p of {
   XI p0 ->
    case q of {
     XI q0 -> ndouble (lxor p0 q0);
     XO q0 -> nsucc_double (lxor p0 q0);
     XH -> Npos (XO p0)};
   XO p0 ->
    case q of {
     XI q0 -> nsucc_double (lxor p0 q0);
     XO q0 -> ndouble (lxor p0 q0);
     XH -> Npos (XI p0)};
   XH ->
    case q of {
     XI q0 -> Npos (XO q0);
     XO q0 -> Npos (XI q0);
     XH -> N0}}

shiftl_nat :: Positive -> Nat -> Positive
shiftl_nat p n =
  nat_iter n (\x -> XO x) p

shiftr_nat :: Positive -> Nat -> Positive
shiftr_nat p n =
  nat_iter n div2 p

shiftl :: Positive -> N -> Positive
shiftl p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 (\x -> XO x) p}

shiftr :: Positive -> N -> Positive
shiftr p n =
  case n of {
   N0 -> p;
   Npos n0 -> iter n0 div2 p}

testbit_nat :: Positive -> Nat -> Bool
testbit_nat p n =
  case p of {
   XI p0 ->
    case n of {
     O -> True;
     S n' -> testbit_nat p0 n'};
   XO p0 ->
    case n of {
     O -> False;
     S n' -> testbit_nat p0 n'};
   XH ->
    case n of {
     O -> True;
     S n0 -> False}}

testbit :: Positive -> N -> Bool
testbit p n =
  case p of {
   XI p0 ->
    case n of {
     N0 -> True;
     Npos n0 -> testbit p0 (pred_N n0)};
   XO p0 ->
    case n of {
     N0 -> False;
     Npos n0 -> testbit p0 (pred_N n0)};
   XH ->
    case n of {
     N0 -> True;
     Npos p0 -> False}}

iter_op :: (a1 -> a1 -> a1) -> Positive -> a1 -> a1
iter_op op p a =
  case p of {
   XI p0 -> op a (iter_op op p0 (op a a));
   XO p0 -> iter_op op p0 (op a a);
   XH -> a}

to_nat :: Positive -> Nat
to_nat x =
  iter_op plus x (S O)

of_nat :: Nat -> Positive
of_nat n =
  case n of {
   O -> XH;
   S x ->
    case x of {
     O -> XH;
     S n0 -> succ (of_nat x)}}

of_succ_nat :: Nat -> Positive
of_succ_nat n =
  case n of {
   O -> XH;
   S x -> succ (of_succ_nat x)}

eq_dec :: Positive -> Positive -> Sumbool
eq_dec x y =
  positive_rec (\p h y0 ->
    case y0 of {
     XI p0 -> sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0);
     _ -> Right}) (\p h y0 ->
    case y0 of {
     XO p0 -> sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0);
     _ -> Right}) (\y0 ->
    case y0 of {
     XH -> Left;
     _ -> Right}) x y

peano_rect :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rect a f p =
  let {f2 = peano_rect (f XH a) (\p0 x -> f (succ (XO p0)) (f (XO p0) x))} in
  case p of {
   XI q -> f (XO q) (f2 q);
   XO q -> f2 q;
   XH -> a}

peano_rec :: a1 -> (Positive -> a1 -> a1) -> Positive -> a1
peano_rec =
  peano_rect

data PeanoView =
   PeanoOne
 | PeanoSucc Positive PeanoView

peanoView_rect :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                  PeanoView -> a1
peanoView_rect f f0 p p0 =
  case p0 of {
   PeanoOne -> f;
   PeanoSucc p1 p2 -> f0 p1 p2 (peanoView_rect f f0 p1 p2)}

peanoView_rec :: a1 -> (Positive -> PeanoView -> a1 -> a1) -> Positive ->
                 PeanoView -> a1
peanoView_rec =
  peanoView_rect

peanoView_xO :: Positive -> PeanoView -> PeanoView
peanoView_xO p q =
  case q of {
   PeanoOne -> PeanoSucc XH PeanoOne;
   PeanoSucc p0 q0 -> PeanoSucc (succ (XO p0)) (PeanoSucc (XO p0)
    (peanoView_xO p0 q0))}

peanoView_xI :: Positive -> PeanoView -> PeanoView
peanoView_xI p q =
  case q of {
   PeanoOne -> PeanoSucc (succ XH) (PeanoSucc XH PeanoOne);
   PeanoSucc p0 q0 -> PeanoSucc (succ (XI p0)) (PeanoSucc (XI p0)
    (peanoView_xI p0 q0))}

peanoView :: Positive -> PeanoView
peanoView p =
  case p of {
   XI p0 -> peanoView_xI p0 (peanoView p0);
   XO p0 -> peanoView_xO p0 (peanoView p0);
   XH -> PeanoOne}

peanoView_iter :: a1 -> (Positive -> a1 -> a1) -> Positive -> PeanoView -> a1
peanoView_iter a f p q =
  case q of {
   PeanoOne -> a;
   PeanoSucc p0 q0 -> f p0 (peanoView_iter a f p0 q0)}

eqb_spec :: Positive -> Positive -> Reflect
eqb_spec x y =
  iff_reflect (eqb0 x y)

switch_Eq :: Comparison -> Comparison -> Comparison
switch_Eq c c' =
  case c' of {
   Eq -> c;
   x -> x}

mask2cmp :: Mask -> Comparison
mask2cmp p =
  case p of {
   IsNul -> Eq;
   IsPos p0 -> Gt;
   IsNeg -> Lt}

leb_spec0 :: Positive -> Positive -> Reflect
leb_spec0 x y =
  iff_reflect (leb x y)

ltb_spec0 :: Positive -> Positive -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb x y)

max_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max n m) __ (hl __);
   _ -> compat m (max n m) __ (hr __)}

max_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
max_case n m x x0 x1 =
  max_case_strong n m x (\_ -> x0) (\_ -> x1)

max_dec :: Positive -> Positive -> Sumbool
max_dec n m =
  max_case n m (\x y _ h0 -> h0) Left Right

min_case_strong :: Positive -> Positive -> (Positive -> Positive -> () -> a1
                   -> a1) -> (() -> a1) -> (() -> a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min n m) __ (hr __);
   _ -> compat n (min n m) __ (hl __)}

min_case :: Positive -> Positive -> (Positive -> Positive -> () -> a1 -> a1)
            -> a1 -> a1 -> a1
min_case n m x x0 x1 =
  min_case_strong n m x (\_ -> x0) (\_ -> x1)

min_dec :: Positive -> Positive -> Sumbool
min_dec n m =
  min_case n m (\x y _ h0 -> h0) Left Right

max_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
max_case_strong0 n m x x0 =
  max_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case0 :: Positive -> Positive -> a1 -> a1 -> a1
max_case0 n m x x0 =
  max_case_strong0 n m (\_ -> x) (\_ -> x0)

max_dec0 :: Positive -> Positive -> Sumbool
max_dec0 =
  max_dec

min_case_strong0 :: Positive -> Positive -> (() -> a1) -> (() -> a1) -> a1
min_case_strong0 n m x x0 =
  min_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case0 :: Positive -> Positive -> a1 -> a1 -> a1
min_case0 n m x x0 =
  min_case_strong0 n m (\_ -> x) (\_ -> x0)

min_dec0 :: Positive -> Positive -> Sumbool
min_dec0 =
  min_dec

type T0 = N

zero :: N
zero =
  N0

one :: N
one =
  Npos XH

two :: N
two =
  Npos (XO XH)

succ_double :: N -> N
succ_double x =
  case x of {
   N0 -> Npos XH;
   Npos p -> Npos (XI p)}

double :: N -> N
double n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (XO p)}

succ0 :: N -> N
succ0 n =
  case n of {
   N0 -> Npos XH;
   Npos p -> Npos (succ p)}

pred0 :: N -> N
pred0 n =
  case n of {
   N0 -> N0;
   Npos p -> pred_N p}

succ_pos :: N -> Positive
succ_pos n =
  case n of {
   N0 -> XH;
   Npos p -> succ p}

add0 :: N -> N -> N
add0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (add p q)}}

sub0 :: N -> N -> N
sub0 n m =
  case n of {
   N0 -> N0;
   Npos n' ->
    case m of {
     N0 -> n;
     Npos m' ->
      case sub_mask n' m' of {
       IsPos p -> Npos p;
       _ -> N0}}}

mul0 :: N -> N -> N
mul0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> Npos (mul p q)}}

compare0 :: N -> N -> Comparison
compare0 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> Eq;
     Npos m' -> Lt};
   Npos n' ->
    case m of {
     N0 -> Gt;
     Npos m' -> compare n' m'}}

eqb1 :: N -> N -> Bool
eqb1 n m =
  case n of {
   N0 ->
    case m of {
     N0 -> True;
     Npos p -> False};
   Npos p ->
    case m of {
     N0 -> False;
     Npos q -> eqb0 p q}}

leb0 :: N -> N -> Bool
leb0 x y =
  case compare0 x y of {
   Gt -> False;
   _ -> True}

ltb0 :: N -> N -> Bool
ltb0 x y =
  case compare0 x y of {
   Lt -> True;
   _ -> False}

min0 :: N -> N -> N
min0 n n' =
  case compare0 n n' of {
   Gt -> n';
   _ -> n}

max0 :: N -> N -> N
max0 n n' =
  case compare0 n n' of {
   Gt -> n;
   _ -> n'}

div0 :: N -> N
div0 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    case p0 of {
     XI p -> Npos p;
     XO p -> Npos p;
     XH -> N0}}

even :: N -> Bool
even n =
  case n of {
   N0 -> True;
   Npos p ->
    case p of {
     XO p0 -> True;
     _ -> False}}

odd :: N -> Bool
odd n =
  negb (even n)

pow0 :: N -> N -> N
pow0 n p =
  case p of {
   N0 -> Npos XH;
   Npos p0 ->
    case n of {
     N0 -> N0;
     Npos q -> Npos (pow q p0)}}

square0 :: N -> N
square0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (square p)}

log2 :: N -> N
log2 n =
  case n of {
   N0 -> N0;
   Npos p0 ->
    case p0 of {
     XI p -> Npos (size p);
     XO p -> Npos (size p);
     XH -> N0}}

size0 :: N -> N
size0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (size p)}

size_nat0 :: N -> Nat
size_nat0 n =
  case n of {
   N0 -> O;
   Npos p -> size_nat p}

pos_div_eucl :: Positive -> N -> Prod N N
pos_div_eucl a b =
  case a of {
   XI a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub0 r' b);
       False -> Pair (double q) r'}};
   XO a' ->
    case pos_div_eucl a' b of {
     Pair q r ->
      let {r' = double r} in
      case leb0 b r' of {
       True -> Pair (succ_double q) (sub0 r' b);
       False -> Pair (double q) r'}};
   XH ->
    case b of {
     N0 -> Pair N0 (Npos XH);
     Npos p ->
      case p of {
       XH -> Pair (Npos XH) N0;
       _ -> Pair N0 (Npos XH)}}}

div_eucl :: N -> N -> Prod N N
div_eucl a b =
  case a of {
   N0 -> Pair N0 N0;
   Npos na ->
    case b of {
     N0 -> Pair N0 a;
     Npos p -> pos_div_eucl na b}}

div :: N -> N -> N
div a b =
  fst (div_eucl a b)

modulo :: N -> N -> N
modulo a b =
  snd (div_eucl a b)

gcd0 :: N -> N -> N
gcd0 a b =
  case a of {
   N0 -> b;
   Npos p ->
    case b of {
     N0 -> a;
     Npos q -> Npos (gcd p q)}}

ggcd0 :: N -> N -> Prod N (Prod N N)
ggcd0 a b =
  case a of {
   N0 -> Pair b (Pair N0 (Npos XH));
   Npos p ->
    case b of {
     N0 -> Pair a (Pair (Npos XH) N0);
     Npos q ->
      case ggcd p q of {
       Pair g p0 ->
        case p0 of {
         Pair aa bb -> Pair (Npos g) (Pair (Npos aa) (Npos bb))}}}}

sqrtrem0 :: N -> Prod N N
sqrtrem0 n =
  case n of {
   N0 -> Pair N0 N0;
   Npos p ->
    case sqrtrem p of {
     Pair s m ->
      case m of {
       IsPos r -> Pair (Npos s) (Npos r);
       _ -> Pair (Npos s) N0}}}

sqrt0 :: N -> N
sqrt0 n =
  case n of {
   N0 -> N0;
   Npos p -> Npos (sqrt p)}

lor0 :: N -> N -> N
lor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> Npos (lor p q)}}

land0 :: N -> N -> N
land0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> N0;
     Npos q -> land p q}}

ldiff0 :: N -> N -> N
ldiff0 n m =
  case n of {
   N0 -> N0;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> ldiff p q}}

lxor0 :: N -> N -> N
lxor0 n m =
  case n of {
   N0 -> m;
   Npos p ->
    case m of {
     N0 -> n;
     Npos q -> lxor p q}}

shiftl_nat0 :: N -> Nat -> N
shiftl_nat0 a n =
  nat_iter n double a

shiftr_nat0 :: N -> Nat -> N
shiftr_nat0 a n =
  nat_iter n div0 a

shiftl0 :: N -> N -> N
shiftl0 a n =
  case a of {
   N0 -> N0;
   Npos a0 -> Npos (shiftl a0 n)}

shiftr0 :: N -> N -> N
shiftr0 a n =
  case n of {
   N0 -> a;
   Npos p -> iter p div0 a}

testbit_nat0 :: N -> Nat -> Bool
testbit_nat0 a =
  case a of {
   N0 -> (\x -> False);
   Npos p -> testbit_nat p}

testbit0 :: N -> N -> Bool
testbit0 a n =
  case a of {
   N0 -> False;
   Npos p -> testbit p n}

to_nat0 :: N -> Nat
to_nat0 a =
  case a of {
   N0 -> O;
   Npos p -> to_nat p}

of_nat0 :: Nat -> N
of_nat0 n =
  case n of {
   O -> N0;
   S n' -> Npos (of_succ_nat n')}

iter0 :: N -> (a1 -> a1) -> a1 -> a1
iter0 n f x =
  case n of {
   N0 -> x;
   Npos p -> iter p f x}

eq_dec0 :: N -> N -> Sumbool
eq_dec0 n m =
  n_rec (\m0 ->
    case m0 of {
     N0 -> Left;
     Npos p -> Right}) (\p m0 ->
    case m0 of {
     N0 -> Right;
     Npos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0)}) n
    m

discr :: N -> Sumor Positive
discr n =
  case n of {
   N0 -> Inright;
   Npos p -> Inleft p}

binary_rect :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rect f0 f2 fS2 n =
  let {f2' = \p -> f2 (Npos p)} in
  let {fS2' = \p -> fS2 (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> positive_rect fS2' f2' (fS2 N0 f0) p}

binary_rec :: a1 -> (N -> a1 -> a1) -> (N -> a1 -> a1) -> N -> a1
binary_rec =
  binary_rect

peano_rect0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rect0 f0 f n =
  let {f' = \p -> f (Npos p)} in
  case n of {
   N0 -> f0;
   Npos p -> peano_rect (f N0 f0) f' p}

peano_rec0 :: a1 -> (N -> a1 -> a1) -> N -> a1
peano_rec0 =
  peano_rect0

leb_spec1 :: N -> N -> Reflect
leb_spec1 x y =
  iff_reflect (leb0 x y)

ltb_spec1 :: N -> N -> Reflect
ltb_spec1 x y =
  iff_reflect (ltb0 x y)

recursion :: a1 -> (N -> a1 -> a1) -> N -> a1
recursion =
  peano_rect0

sqrt_up :: N -> N
sqrt_up a =
  case compare0 N0 a of {
   Lt -> succ0 (sqrt0 (pred0 a));
   _ -> N0}

log2_up :: N -> N
log2_up a =
  case compare0 (Npos XH) a of {
   Lt -> succ0 (log2 (pred0 a));
   _ -> N0}

lcm :: N -> N -> N
lcm a b =
  mul0 a (div b (gcd0 a b))

eqb_spec0 :: N -> N -> Reflect
eqb_spec0 x y =
  iff_reflect (eqb1 x y)

b2n :: Bool -> N
b2n b =
  case b of {
   True -> Npos XH;
   False -> N0}

setbit :: N -> N -> N
setbit a n =
  lor0 a (shiftl0 (Npos XH) n)

clearbit :: N -> N -> N
clearbit a n =
  ldiff0 a (shiftl0 (Npos XH) n)

ones :: N -> N
ones n =
  pred0 (shiftl0 (Npos XH) n)

lnot :: N -> N -> N
lnot a n =
  lxor0 a (ones n)

max_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat n (max0 n m) __ (hl __);
   _ -> compat m (max0 n m) __ (hr __)}

max_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case1 n m x x0 x1 =
  max_case_strong1 n m x (\_ -> x0) (\_ -> x1)

max_dec1 :: N -> N -> Sumbool
max_dec1 n m =
  max_case1 n m (\x y _ h0 -> h0) Left Right

min_case_strong1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat m (min0 n m) __ (hr __);
   _ -> compat n (min0 n m) __ (hl __)}

min_case1 :: N -> N -> (N -> N -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case1 n m x x0 x1 =
  min_case_strong1 n m x (\_ -> x0) (\_ -> x1)

min_dec1 :: N -> N -> Sumbool
min_dec1 n m =
  min_case1 n m (\x y _ h0 -> h0) Left Right

max_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
max_case_strong2 n m x x0 =
  max_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case2 :: N -> N -> a1 -> a1 -> a1
max_case2 n m x x0 =
  max_case_strong2 n m (\_ -> x) (\_ -> x0)

max_dec2 :: N -> N -> Sumbool
max_dec2 =
  max_dec1

min_case_strong2 :: N -> N -> (() -> a1) -> (() -> a1) -> a1
min_case_strong2 n m x x0 =
  min_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case2 :: N -> N -> a1 -> a1 -> a1
min_case2 n m x x0 =
  min_case_strong2 n m (\_ -> x) (\_ -> x0)

min_dec2 :: N -> N -> Sumbool
min_dec2 =
  min_dec1

type T1 = Z

zero0 :: Z
zero0 =
  Z0

one0 :: Z
one0 =
  Zpos XH

two0 :: Z
two0 =
  Zpos (XO XH)

double0 :: Z -> Z
double0 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double0 :: Z -> Z
succ_double0 x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double0 (pos_sub p q);
     XO q -> succ_double0 (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double0 (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add1 :: Z -> Z -> Z
add1 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add x' y')}}

opp :: Z -> Z
opp x =
  case x of {
   Z0 -> Z0;
   Zpos x0 -> Zneg x0;
   Zneg x0 -> Zpos x0}

succ1 :: Z -> Z
succ1 x =
  add1 x (Zpos XH)

pred1 :: Z -> Z
pred1 x =
  add1 x (Zneg XH)

sub1 :: Z -> Z -> Z
sub1 m n =
  add1 m (opp n)

mul1 :: Z -> Z -> Z
mul1 x y =
  case x of {
   Z0 -> Z0;
   Zpos x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zpos (mul x' y');
     Zneg y' -> Zneg (mul x' y')};
   Zneg x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zneg (mul x' y');
     Zneg y' -> Zpos (mul x' y')}}

pow_pos :: Z -> Positive -> Z
pow_pos z n =
  iter n (mul1 z) (Zpos XH)

pow1 :: Z -> Z -> Z
pow1 x y =
  case y of {
   Z0 -> Zpos XH;
   Zpos p -> pow_pos x p;
   Zneg p -> Z0}

square1 :: Z -> Z
square1 x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (square p);
   Zneg p -> Zpos (square p)}

compare1 :: Z -> Z -> Comparison
compare1 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> Eq;
     Zpos y' -> Lt;
     Zneg y' -> Gt};
   Zpos x' ->
    case y of {
     Zpos y' -> compare x' y';
     _ -> Gt};
   Zneg x' ->
    case y of {
     Zneg y' -> compOpp (compare x' y');
     _ -> Lt}}

sgn :: Z -> Z
sgn z =
  case z of {
   Z0 -> Z0;
   Zpos p -> Zpos XH;
   Zneg p -> Zneg XH}

leb1 :: Z -> Z -> Bool
leb1 x y =
  case compare1 x y of {
   Gt -> False;
   _ -> True}

ltb1 :: Z -> Z -> Bool
ltb1 x y =
  case compare1 x y of {
   Lt -> True;
   _ -> False}

geb :: Z -> Z -> Bool
geb x y =
  case compare1 x y of {
   Lt -> False;
   _ -> True}

gtb :: Z -> Z -> Bool
gtb x y =
  case compare1 x y of {
   Gt -> True;
   _ -> False}

eqb2 :: Z -> Z -> Bool
eqb2 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> True;
     _ -> False};
   Zpos p ->
    case y of {
     Zpos q -> eqb0 p q;
     _ -> False};
   Zneg p ->
    case y of {
     Zneg q -> eqb0 p q;
     _ -> False}}

max1 :: Z -> Z -> Z
max1 n m =
  case compare1 n m of {
   Lt -> m;
   _ -> n}

min1 :: Z -> Z -> Z
min1 n m =
  case compare1 n m of {
   Gt -> m;
   _ -> n}

abs :: Z -> Z
abs z =
  case z of {
   Zneg p -> Zpos p;
   x -> x}

abs_nat :: Z -> Nat
abs_nat z =
  case z of {
   Z0 -> O;
   Zpos p -> to_nat p;
   Zneg p -> to_nat p}

abs_N :: Z -> N
abs_N z =
  case z of {
   Z0 -> N0;
   Zpos p -> Npos p;
   Zneg p -> Npos p}

to_nat1 :: Z -> Nat
to_nat1 z =
  case z of {
   Zpos p -> to_nat p;
   _ -> O}

to_N :: Z -> N
to_N z =
  case z of {
   Zpos p -> Npos p;
   _ -> N0}

of_nat1 :: Nat -> Z
of_nat1 n =
  case n of {
   O -> Z0;
   S n0 -> Zpos (of_succ_nat n0)}

of_N :: N -> Z
of_N n =
  case n of {
   N0 -> Z0;
   Npos p -> Zpos p}

to_pos :: Z -> Positive
to_pos z =
  case z of {
   Zpos p -> p;
   _ -> XH}

iter1 :: Z -> (a1 -> a1) -> a1 -> a1
iter1 n f x =
  case n of {
   Zpos p -> iter p f x;
   _ -> x}

pos_div_eucl0 :: Positive -> Z -> Prod Z Z
pos_div_eucl0 a b =
  case a of {
   XI a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {r' = add1 (mul1 (Zpos (XO XH)) r) (Zpos XH)} in
      case ltb1 r' b of {
       True -> Pair (mul1 (Zpos (XO XH)) q) r';
       False -> Pair (add1 (mul1 (Zpos (XO XH)) q) (Zpos XH)) (sub1 r' b)}};
   XO a' ->
    case pos_div_eucl0 a' b of {
     Pair q r ->
      let {r' = mul1 (Zpos (XO XH)) r} in
      case ltb1 r' b of {
       True -> Pair (mul1 (Zpos (XO XH)) q) r';
       False -> Pair (add1 (mul1 (Zpos (XO XH)) q) (Zpos XH)) (sub1 r' b)}};
   XH ->
    case leb1 (Zpos (XO XH)) b of {
     True -> Pair Z0 (Zpos XH);
     False -> Pair (Zpos XH) Z0}}

div_eucl0 :: Z -> Z -> Prod Z Z
div_eucl0 a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos p -> pos_div_eucl0 a' b;
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add1 q (Zpos XH))) (add1 b r)}}};
   Zneg a' ->
    case b of {
     Z0 -> Pair Z0 Z0;
     Zpos p ->
      case pos_div_eucl0 a' b of {
       Pair q r ->
        case r of {
         Z0 -> Pair (opp q) Z0;
         _ -> Pair (opp (add1 q (Zpos XH))) (sub1 b r)}};
     Zneg b' ->
      case pos_div_eucl0 a' (Zpos b') of {
       Pair q r -> Pair q (opp r)}}}

div1 :: Z -> Z -> Z
div1 a b =
  case div_eucl0 a b of {
   Pair q x -> q}

modulo0 :: Z -> Z -> Z
modulo0 a b =
  case div_eucl0 a b of {
   Pair x r -> r}

quotrem :: Z -> Z -> Prod Z Z
quotrem a b =
  case a of {
   Z0 -> Pair Z0 Z0;
   Zpos a0 ->
    case b of {
     Z0 -> Pair Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (of_N r)};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (of_N r)}};
   Zneg a0 ->
    case b of {
     Z0 -> Pair Z0 a;
     Zpos b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (opp (of_N q)) (opp (of_N r))};
     Zneg b0 ->
      case pos_div_eucl a0 (Npos b0) of {
       Pair q r -> Pair (of_N q) (opp (of_N r))}}}

quot :: Z -> Z -> Z
quot a b =
  fst (quotrem a b)

rem :: Z -> Z -> Z
rem a b =
  snd (quotrem a b)

even0 :: Z -> Bool
even0 z =
  case z of {
   Z0 -> True;
   Zpos p ->
    case p of {
     XO p0 -> True;
     _ -> False};
   Zneg p ->
    case p of {
     XO p0 -> True;
     _ -> False}}

odd0 :: Z -> Bool
odd0 z =
  case z of {
   Z0 -> False;
   Zpos p ->
    case p of {
     XO p0 -> False;
     _ -> True};
   Zneg p ->
    case p of {
     XO p0 -> False;
     _ -> True}}

div3 :: Z -> Z
div3 z =
  case z of {
   Z0 -> Z0;
   Zpos p ->
    case p of {
     XH -> Z0;
     _ -> Zpos (div2 p)};
   Zneg p -> Zneg (div2_up p)}

quot2 :: Z -> Z
quot2 z =
  case z of {
   Z0 -> Z0;
   Zpos p ->
    case p of {
     XH -> Z0;
     _ -> Zpos (div2 p)};
   Zneg p ->
    case p of {
     XH -> Z0;
     _ -> Zneg (div2 p)}}

log0 :: Z -> Z
log0 z =
  case z of {
   Zpos p0 ->
    case p0 of {
     XI p -> Zpos (size p);
     XO p -> Zpos (size p);
     XH -> Z0};
   _ -> Z0}

sqrtrem1 :: Z -> Prod Z Z
sqrtrem1 n =
  case n of {
   Zpos p ->
    case sqrtrem p of {
     Pair s m ->
      case m of {
       IsPos r -> Pair (Zpos s) (Zpos r);
       _ -> Pair (Zpos s) Z0}};
   _ -> Pair Z0 Z0}

sqrt1 :: Z -> Z
sqrt1 n =
  case n of {
   Zpos p -> Zpos (sqrt p);
   _ -> Z0}

gcd1 :: Z -> Z -> Z
gcd1 a b =
  case a of {
   Z0 -> abs b;
   Zpos a0 ->
    case b of {
     Z0 -> abs a;
     Zpos b0 -> Zpos (gcd a0 b0);
     Zneg b0 -> Zpos (gcd a0 b0)};
   Zneg a0 ->
    case b of {
     Z0 -> abs a;
     Zpos b0 -> Zpos (gcd a0 b0);
     Zneg b0 -> Zpos (gcd a0 b0)}}

ggcd1 :: Z -> Z -> Prod Z (Prod Z Z)
ggcd1 a b =
  case a of {
   Z0 -> Pair (abs b) (Pair Z0 (sgn b));
   Zpos a0 ->
    case b of {
     Z0 -> Pair (abs a) (Pair (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zpos aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zpos aa) (Zneg bb))}}};
   Zneg a0 ->
    case b of {
     Z0 -> Pair (abs a) (Pair (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zneg aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       Pair g p ->
        case p of {
         Pair aa bb -> Pair (Zpos g) (Pair (Zneg aa) (Zneg bb))}}}}

testbit1 :: Z -> Z -> Bool
testbit1 a n =
  case n of {
   Z0 -> odd0 a;
   Zpos p ->
    case a of {
     Z0 -> False;
     Zpos a0 -> testbit a0 (Npos p);
     Zneg a0 -> negb (testbit0 (pred_N a0) (Npos p))};
   Zneg p -> False}

shiftl1 :: Z -> Z -> Z
shiftl1 a n =
  case n of {
   Z0 -> a;
   Zpos p -> iter p (mul1 (Zpos (XO XH))) a;
   Zneg p -> iter p div3 a}

shiftr1 :: Z -> Z -> Z
shiftr1 a n =
  shiftl1 a (opp n)

lor1 :: Z -> Z -> Z
lor1 a b =
  case a of {
   Z0 -> b;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zpos (lor a0 b0);
     Zneg b0 -> Zneg (succ_pos (ldiff0 (pred_N b0) (Npos a0)))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (ldiff0 (pred_N a0) (Npos b0)));
     Zneg b0 -> Zneg (succ_pos (land0 (pred_N a0) (pred_N b0)))}}

land1 :: Z -> Z -> Z
land1 a b =
  case a of {
   Z0 -> Z0;
   Zpos a0 ->
    case b of {
     Z0 -> Z0;
     Zpos b0 -> of_N (land a0 b0);
     Zneg b0 -> of_N (ldiff0 (Npos a0) (pred_N b0))};
   Zneg a0 ->
    case b of {
     Z0 -> Z0;
     Zpos b0 -> of_N (ldiff0 (Npos b0) (pred_N a0));
     Zneg b0 -> Zneg (succ_pos (lor0 (pred_N a0) (pred_N b0)))}}

ldiff1 :: Z -> Z -> Z
ldiff1 a b =
  case a of {
   Z0 -> Z0;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> of_N (ldiff a0 b0);
     Zneg b0 -> of_N (land0 (Npos a0) (pred_N b0))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (lor0 (pred_N a0) (Npos b0)));
     Zneg b0 -> of_N (ldiff0 (pred_N b0) (pred_N a0))}}

lxor1 :: Z -> Z -> Z
lxor1 a b =
  case a of {
   Z0 -> b;
   Zpos a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> of_N (lxor a0 b0);
     Zneg b0 -> Zneg (succ_pos (lxor0 (Npos a0) (pred_N b0)))};
   Zneg a0 ->
    case b of {
     Z0 -> a;
     Zpos b0 -> Zneg (succ_pos (lxor0 (pred_N a0) (Npos b0)));
     Zneg b0 -> of_N (lxor0 (pred_N a0) (pred_N b0))}}

eq_dec1 :: Z -> Z -> Sumbool
eq_dec1 x y =
  z_rec (\y0 ->
    case y0 of {
     Z0 -> Left;
     _ -> Right}) (\p y0 ->
    case y0 of {
     Zpos p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0);
     _ -> Right}) (\p y0 ->
    case y0 of {
     Zneg p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0);
     _ -> Right}) x y

leb_spec2 :: Z -> Z -> Reflect
leb_spec2 x y =
  iff_reflect (leb1 x y)

ltb_spec2 :: Z -> Z -> Reflect
ltb_spec2 x y =
  iff_reflect (ltb1 x y)

sqrt_up0 :: Z -> Z
sqrt_up0 a =
  case compare1 Z0 a of {
   Lt -> succ1 (sqrt1 (pred1 a));
   _ -> Z0}

log2_up0 :: Z -> Z
log2_up0 a =
  case compare1 (Zpos XH) a of {
   Lt -> succ1 (log0 (pred1 a));
   _ -> Z0}

div4 :: Z -> Z -> Z
div4 =
  quot

modulo1 :: Z -> Z -> Z
modulo1 =
  rem

lcm0 :: Z -> Z -> Z
lcm0 a b =
  abs (mul1 a (div1 b (gcd1 a b)))

eqb_spec1 :: Z -> Z -> Reflect
eqb_spec1 x y =
  iff_reflect (eqb2 x y)

b2z :: Bool -> Z
b2z b =
  case b of {
   True -> Zpos XH;
   False -> Z0}

setbit0 :: Z -> Z -> Z
setbit0 a n =
  lor1 a (shiftl1 (Zpos XH) n)

clearbit0 :: Z -> Z -> Z
clearbit0 a n =
  ldiff1 a (shiftl1 (Zpos XH) n)

lnot0 :: Z -> Z
lnot0 a =
  pred1 (opp a)

ones0 :: Z -> Z
ones0 n =
  pred1 (shiftl1 (Zpos XH) n)

max_case_strong3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat n (max1 n m) __ (hl __);
   _ -> compat m (max1 n m) __ (hr __)}

max_case3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case3 n m x x0 x1 =
  max_case_strong3 n m x (\_ -> x0) (\_ -> x1)

max_dec3 :: Z -> Z -> Sumbool
max_dec3 n m =
  max_case3 n m (\x y _ h0 -> h0) Left Right

min_case_strong3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat m (min1 n m) __ (hr __);
   _ -> compat n (min1 n m) __ (hl __)}

min_case3 :: Z -> Z -> (Z -> Z -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case3 n m x x0 x1 =
  min_case_strong3 n m x (\_ -> x0) (\_ -> x1)

min_dec3 :: Z -> Z -> Sumbool
min_dec3 n m =
  min_case3 n m (\x y _ h0 -> h0) Left Right

max_case_strong4 :: Z -> Z -> (() -> a1) -> (() -> a1) -> a1
max_case_strong4 n m x x0 =
  max_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case4 :: Z -> Z -> a1 -> a1 -> a1
max_case4 n m x x0 =
  max_case_strong4 n m (\_ -> x) (\_ -> x0)

max_dec4 :: Z -> Z -> Sumbool
max_dec4 =
  max_dec3

min_case_strong4 :: Z -> Z -> (() -> a1) -> (() -> a1) -> a1
min_case_strong4 n m x x0 =
  min_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case4 :: Z -> Z -> a1 -> a1 -> a1
min_case4 n m x x0 =
  min_case_strong4 n m (\_ -> x) (\_ -> x0)

min_dec4 :: Z -> Z -> Sumbool
min_dec4 =
  min_dec3

z_lt_dec :: Z -> Z -> Sumbool
z_lt_dec x y =
  case compare1 x y of {
   Lt -> Left;
   _ -> Right}

z_le_dec :: Z -> Z -> Sumbool
z_le_dec x y =
  case compare1 x y of {
   Gt -> Right;
   _ -> Left}

z_lt_ge_dec :: Z -> Z -> Sumbool
z_lt_ge_dec x y =
  z_lt_dec x y

z_le_gt_dec :: Z -> Z -> Sumbool
z_le_gt_dec x y =
  sumbool_rec (\_ -> Left) (\_ -> Right) (z_le_dec x y)

zeq_bool :: Z -> Z -> Bool
zeq_bool x y =
  case compare1 x y of {
   Eq -> True;
   _ -> False}

shift_nat :: Nat -> Positive -> Positive
shift_nat n z =
  nat_iter n (\x -> XO x) z

shift_pos :: Positive -> Positive -> Positive
shift_pos n z =
  iter n (\x -> XO x) z

two_power_nat :: Nat -> Z
two_power_nat n =
  Zpos (shift_nat n XH)

two_power_pos :: Positive -> Z
two_power_pos x =
  Zpos (shift_pos x XH)

two_p :: Z -> Z
two_p x =
  case x of {
   Z0 -> Zpos XH;
   Zpos y -> two_power_pos y;
   Zneg y -> Z0}

peq :: Positive -> Positive -> Sumbool
peq x y =
  case compare_cont x y Eq of {
   Eq -> Left;
   _ -> Right}

zeq :: Z -> Z -> Sumbool
zeq =
  eq_dec1

zlt :: Z -> Z -> Sumbool
zlt =
  z_lt_ge_dec

zle :: Z -> Z -> Sumbool
zle =
  z_le_gt_dec

option_map :: (a1 -> a2) -> (Option a1) -> Option a2
option_map f x =
  case x of {
   Some y -> Some (f y);
   None -> None}

proj_sumbool :: Sumbool -> Bool
proj_sumbool a =
  case a of {
   Left -> True;
   Right -> False}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

ascii_rect :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
              -> a1) -> Ascii0 -> a1
ascii_rect f a =
  case a of {
   Ascii x x0 x1 x2 x3 x4 x5 x6 -> f x x0 x1 x2 x3 x4 x5 x6}

ascii_rec :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool ->
             a1) -> Ascii0 -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Ascii0 -> Ascii0 -> Sumbool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 b8 ->
    case b8 of {
     Ascii b9 b10 b11 b12 b13 b14 b15 b16 ->
      sumbool_rec (\_ ->
        eq_rec_r b9
          (sumbool_rec (\_ ->
            eq_rec_r b10
              (sumbool_rec (\_ ->
                eq_rec_r b11
                  (sumbool_rec (\_ ->
                    eq_rec_r b12
                      (sumbool_rec (\_ ->
                        eq_rec_r b13
                          (sumbool_rec (\_ ->
                            eq_rec_r b14
                              (sumbool_rec (\_ ->
                                eq_rec_r b15
                                  (sumbool_rec (\_ -> eq_rec_r b16 Left b7)
                                    (\_ -> Right) (bool_dec b7 b16)) b6)
                                (\_ -> Right) (bool_dec b6 b15)) b5) (\_ ->
                            Right) (bool_dec b5 b14)) b4) (\_ -> Right)
                        (bool_dec b4 b13)) b3) (\_ -> Right)
                    (bool_dec b3 b12)) b2) (\_ -> Right) (bool_dec b2 b11))
              b1) (\_ -> Right) (bool_dec b1 b10)) b0) (\_ -> Right)
        (bool_dec b0 b9)}) a b

data String =
   EmptyString
 | String0 Ascii0 String

append :: String -> String -> String
append s1 s2 =
  case s1 of {
   EmptyString -> s2;
   String0 c s1' -> String0 c (append s1' s2)}

wordsize :: Nat -> Nat
wordsize wordsize_minus_one =
  S wordsize_minus_one

modulus :: Nat -> Z
modulus wordsize_minus_one =
  two_power_nat (wordsize wordsize_minus_one)

half_modulus :: Nat -> Z
half_modulus wordsize_minus_one =
  div1 (modulus wordsize_minus_one) (Zpos (XO XH))

data Comparison0 =
   Ceq
 | Cne
 | Clt
 | Cle
 | Cgt
 | Cge

comparison_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Comparison0 -> a1
comparison_rect f f0 f1 f2 f3 f4 c =
  case c of {
   Ceq -> f;
   Cne -> f0;
   Clt -> f1;
   Cle -> f2;
   Cgt -> f3;
   Cge -> f4}

comparison_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Comparison0 -> a1
comparison_rec =
  comparison_rect

negate_comparison :: Comparison0 -> Comparison0
negate_comparison c =
  case c of {
   Ceq -> Cne;
   Cne -> Ceq;
   Clt -> Cge;
   Cle -> Cgt;
   Cgt -> Cle;
   Cge -> Clt}

swap_comparison :: Comparison0 -> Comparison0
swap_comparison c =
  case c of {
   Clt -> Cgt;
   Cle -> Cge;
   Cgt -> Clt;
   Cge -> Cle;
   x -> x}

type Int =
  Z
  -- singleton inductive, whose constructor was mkint
  
int_rect :: Nat -> (Z -> () -> a1) -> Int -> a1
int_rect wordsize_minus_one f i =
  f i __

int_rec :: Nat -> (Z -> () -> a1) -> Int -> a1
int_rec wordsize_minus_one =
  int_rect wordsize_minus_one

intval :: Nat -> Int -> Z
intval wordsize_minus_one i =
  i

max_unsigned :: Nat -> Z
max_unsigned wordsize_minus_one =
  sub1 (modulus wordsize_minus_one) (Zpos XH)

max_signed :: Nat -> Z
max_signed wordsize_minus_one =
  sub1 (half_modulus wordsize_minus_one) (Zpos XH)

min_signed :: Nat -> Z
min_signed wordsize_minus_one =
  opp (half_modulus wordsize_minus_one)

unsigned :: Nat -> Int -> Z
unsigned wordsize_minus_one n =
  intval wordsize_minus_one n

signed :: Nat -> Int -> Z
signed wordsize_minus_one n =
  case zlt (unsigned wordsize_minus_one n) (half_modulus wordsize_minus_one) of {
   Left -> unsigned wordsize_minus_one n;
   Right -> sub1 (unsigned wordsize_minus_one n) (modulus wordsize_minus_one)}

repr :: Nat -> Z -> Int
repr wordsize_minus_one x =
  modulo0 x (modulus wordsize_minus_one)

zero1 :: Nat -> Int
zero1 wordsize_minus_one =
  repr wordsize_minus_one Z0

one1 :: Nat -> Int
one1 wordsize_minus_one =
  repr wordsize_minus_one (Zpos XH)

mone :: Nat -> Int
mone wordsize_minus_one =
  repr wordsize_minus_one (Zneg XH)

eq_dec2 :: Nat -> Int -> Int -> Sumbool
eq_dec2 wordsize_minus_one x y =
  zeq x y

eq :: Nat -> Int -> Int -> Bool
eq wordsize_minus_one x y =
  case zeq (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y) of {
   Left -> True;
   Right -> False}

lt :: Nat -> Int -> Int -> Bool
lt wordsize_minus_one x y =
  case zlt (signed wordsize_minus_one x) (signed wordsize_minus_one y) of {
   Left -> True;
   Right -> False}

ltu :: Nat -> Int -> Int -> Bool
ltu wordsize_minus_one x y =
  case zlt (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y) of {
   Left -> True;
   Right -> False}

lequ :: Nat -> Int -> Int -> Bool
lequ wordsize_minus_one x y =
  orb (ltu wordsize_minus_one x y) (eq wordsize_minus_one x y)

neg :: Nat -> Int -> Int
neg wordsize_minus_one x =
  repr wordsize_minus_one (opp (unsigned wordsize_minus_one x))

zero_ext :: Nat -> Z -> Int -> Int
zero_ext wordsize_minus_one n x =
  repr wordsize_minus_one (modulo0 (unsigned wordsize_minus_one x) (two_p n))

sign_ext :: Nat -> Z -> Int -> Int
sign_ext wordsize_minus_one n x =
  repr wordsize_minus_one
    (let {p = two_p n} in
     let {y = modulo0 (unsigned wordsize_minus_one x) p} in
     case zlt y (two_p (sub1 n (Zpos XH))) of {
      Left -> y;
      Right -> sub1 y p})

add2 :: Nat -> Int -> Int -> Int
add2 wordsize_minus_one x y =
  repr wordsize_minus_one
    (add1 (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y))

sub2 :: Nat -> Int -> Int -> Int
sub2 wordsize_minus_one x y =
  repr wordsize_minus_one
    (sub1 (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y))

mul2 :: Nat -> Int -> Int -> Int
mul2 wordsize_minus_one x y =
  repr wordsize_minus_one
    (mul1 (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y))

zdiv_round :: Z -> Z -> Z
zdiv_round x y =
  case zlt x Z0 of {
   Left ->
    case zlt y Z0 of {
     Left -> div1 (opp x) (opp y);
     Right -> opp (div1 (opp x) y)};
   Right ->
    case zlt y Z0 of {
     Left -> opp (div1 x (opp y));
     Right -> div1 x y}}

zmod_round :: Z -> Z -> Z
zmod_round x y =
  sub1 x (mul1 (zdiv_round x y) y)

divs :: Nat -> Int -> Int -> Int
divs wordsize_minus_one x y =
  repr wordsize_minus_one
    (zdiv_round (signed wordsize_minus_one x) (signed wordsize_minus_one y))

mods :: Nat -> Int -> Int -> Int
mods wordsize_minus_one x y =
  repr wordsize_minus_one
    (zmod_round (signed wordsize_minus_one x) (signed wordsize_minus_one y))

divu :: Nat -> Int -> Int -> Int
divu wordsize_minus_one x y =
  repr wordsize_minus_one
    (div1 (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y))

modu :: Nat -> Int -> Int -> Int
modu wordsize_minus_one x y =
  repr wordsize_minus_one
    (modulo0 (unsigned wordsize_minus_one x) (unsigned wordsize_minus_one y))

bool_to_int :: Nat -> Bool -> Int
bool_to_int wordsize_minus_one b =
  case b of {
   True -> one1 wordsize_minus_one;
   False -> zero1 wordsize_minus_one}

unsigned_overflow :: Nat -> Z -> Z -> Bool
unsigned_overflow wordsize_minus_one o1 o2 =
  let {res = add1 o1 o2} in
  case zlt res (modulus wordsize_minus_one) of {
   Left -> False;
   Right -> True}

unsigned_overflow_with_carry :: Nat -> Z -> Z -> Bool -> Bool
unsigned_overflow_with_carry wordsize_minus_one o1 o2 carry =
  let {c = bool_to_int wordsize_minus_one carry} in
  let {res = add1 (add1 o1 o2) (unsigned wordsize_minus_one c)} in
  case zle res (max_unsigned wordsize_minus_one) of {
   Left -> False;
   Right -> True}

signed_overflow :: Nat -> Z -> Z -> Bool
signed_overflow wordsize_minus_one o1 o2 =
  let {res = add1 o1 o2} in
  case andb (proj_sumbool (zle res (max_signed wordsize_minus_one)))
         (proj_sumbool (zle (min_signed wordsize_minus_one) res)) of {
   True -> False;
   False -> True}

signed_overflow_with_carry :: Nat -> Z -> Z -> Bool -> Bool
signed_overflow_with_carry wordsize_minus_one o1 o2 carry =
  let {c = bool_to_int wordsize_minus_one carry} in
  let {res = add1 (add1 o1 o2) (signed wordsize_minus_one c)} in
  case andb (proj_sumbool (zle res (max_signed wordsize_minus_one)))
         (proj_sumbool (zle (min_signed wordsize_minus_one) res)) of {
   True -> False;
   False -> True}

signed_overflow_with_borrow :: Nat -> Z -> Z -> Bool -> Bool
signed_overflow_with_borrow wordsize_minus_one o1 o2 borrow =
  let {b = bool_to_int wordsize_minus_one borrow} in
  let {res = sub1 (add1 o1 o2) (signed wordsize_minus_one b)} in
  case andb (proj_sumbool (zle res (max_signed wordsize_minus_one)))
         (proj_sumbool (zle (min_signed wordsize_minus_one) res)) of {
   True -> False;
   False -> True}

is_zero :: Nat -> Int -> Bool
is_zero wordsize_minus_one i =
  eq wordsize_minus_one i (zero1 wordsize_minus_one)

is_signed :: Nat -> Int -> Bool
is_signed wordsize_minus_one i =
  lt wordsize_minus_one i (zero1 wordsize_minus_one)

z_shift_add :: Bool -> Z -> Z
z_shift_add b x =
  case b of {
   True -> add1 (mul1 (Zpos (XO XH)) x) (Zpos XH);
   False -> mul1 (Zpos (XO XH)) x}

z_bin_decomp :: Z -> Prod Bool Z
z_bin_decomp x =
  case x of {
   Z0 -> Pair False Z0;
   Zpos p ->
    case p of {
     XI q -> Pair True (Zpos q);
     XO q -> Pair False (Zpos q);
     XH -> Pair True Z0};
   Zneg p ->
    case p of {
     XI q -> Pair True (sub1 (Zneg q) (Zpos XH));
     XO q -> Pair False (Zneg q);
     XH -> Pair True (Zneg XH)}}

bits_of_Z :: Nat -> Z -> Z -> Bool
bits_of_Z n x =
  case n of {
   O -> (\i -> False);
   S m ->
    case z_bin_decomp x of {
     Pair b y ->
      let {f = bits_of_Z m y} in
      (\i ->
      case zeq i Z0 of {
       Left -> b;
       Right -> f (sub1 i (Zpos XH))})}}

z_of_bits :: Nat -> (Z -> Bool) -> Z
z_of_bits n f =
  case n of {
   O -> Z0;
   S m -> z_shift_add (f Z0) (z_of_bits m (\i -> f (add1 i (Zpos XH))))}

bitwise_binop :: Nat -> (Bool -> Bool -> Bool) -> Int -> Int -> Int
bitwise_binop wordsize_minus_one f x y =
  let {
   fx = bits_of_Z (wordsize wordsize_minus_one)
          (unsigned wordsize_minus_one x)}
  in
  let {
   fy = bits_of_Z (wordsize wordsize_minus_one)
          (unsigned wordsize_minus_one y)}
  in
  repr wordsize_minus_one
    (z_of_bits (wordsize wordsize_minus_one) (\i -> f (fx i) (fy i)))

and :: Nat -> Int -> Int -> Int
and wordsize_minus_one x y =
  bitwise_binop wordsize_minus_one andb x y

or :: Nat -> Int -> Int -> Int
or wordsize_minus_one x y =
  bitwise_binop wordsize_minus_one orb x y

xor :: Nat -> Int -> Int -> Int
xor wordsize_minus_one x y =
  bitwise_binop wordsize_minus_one xorb x y

not :: Nat -> Int -> Int
not wordsize_minus_one x =
  xor wordsize_minus_one x (mone wordsize_minus_one)

shl :: Nat -> Int -> Int -> Int
shl wordsize_minus_one x y =
  let {
   fx = bits_of_Z (wordsize wordsize_minus_one)
          (unsigned wordsize_minus_one x)}
  in
  let {vy = unsigned wordsize_minus_one y} in
  repr wordsize_minus_one
    (z_of_bits (wordsize wordsize_minus_one) (\i -> fx (sub1 i vy)))

shru :: Nat -> Int -> Int -> Int
shru wordsize_minus_one x y =
  let {
   fx = bits_of_Z (wordsize wordsize_minus_one)
          (unsigned wordsize_minus_one x)}
  in
  let {vy = unsigned wordsize_minus_one y} in
  repr wordsize_minus_one
    (z_of_bits (wordsize wordsize_minus_one) (\i -> fx (add1 i vy)))

shr :: Nat -> Int -> Int -> Int
shr wordsize_minus_one x y =
  repr wordsize_minus_one
    (div1 (signed wordsize_minus_one x)
      (two_p (unsigned wordsize_minus_one y)))

shrx :: Nat -> Int -> Int -> Int
shrx wordsize_minus_one x y =
  divs wordsize_minus_one x
    (shl wordsize_minus_one (one1 wordsize_minus_one) y)

shr_carry :: Nat -> Int -> Int -> Int
shr_carry wordsize_minus_one x y =
  sub2 wordsize_minus_one (shrx wordsize_minus_one x y)
    (shr wordsize_minus_one x y)

rol :: Nat -> Int -> Int -> Int
rol wordsize_minus_one x y =
  let {
   fx = bits_of_Z (wordsize wordsize_minus_one)
          (unsigned wordsize_minus_one x)}
  in
  let {vy = unsigned wordsize_minus_one y} in
  repr wordsize_minus_one
    (z_of_bits (wordsize wordsize_minus_one) (\i ->
      fx (modulo0 (sub1 i vy) (of_nat1 (wordsize wordsize_minus_one)))))

ror :: Nat -> Int -> Int -> Int
ror wordsize_minus_one x y =
  let {
   fx = bits_of_Z (wordsize wordsize_minus_one)
          (unsigned wordsize_minus_one x)}
  in
  let {vy = unsigned wordsize_minus_one y} in
  repr wordsize_minus_one
    (z_of_bits (wordsize wordsize_minus_one) (\i ->
      fx (modulo0 (add1 i vy) (of_nat1 (wordsize wordsize_minus_one)))))

rolm :: Nat -> Int -> Int -> Int -> Int
rolm wordsize_minus_one x a m =
  and wordsize_minus_one (rol wordsize_minus_one x a) m

z_one_bits :: Nat -> Z -> Z -> List Z
z_one_bits n x i =
  case n of {
   O -> Nil;
   S m ->
    case z_bin_decomp x of {
     Pair b y ->
      case b of {
       True -> Cons i (z_one_bits m y (add1 i (Zpos XH)));
       False -> z_one_bits m y (add1 i (Zpos XH))}}}

one_bits :: Nat -> Int -> List Int
one_bits wordsize_minus_one x =
  map (repr wordsize_minus_one)
    (z_one_bits (wordsize wordsize_minus_one) (unsigned wordsize_minus_one x)
      Z0)

is_power2 :: Nat -> Int -> Option Int
is_power2 wordsize_minus_one x =
  case z_one_bits (wordsize wordsize_minus_one)
         (unsigned wordsize_minus_one x) Z0 of {
   Nil -> None;
   Cons i l ->
    case l of {
     Nil -> Some (repr wordsize_minus_one i);
     Cons z l0 -> None}}

data Rlw_state =
   RLW_S0
 | RLW_S1
 | RLW_S2
 | RLW_S3
 | RLW_S4
 | RLW_S5
 | RLW_S6
 | RLW_Sbad

rlw_state_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Rlw_state
                  -> a1
rlw_state_rect f f0 f1 f2 f3 f4 f5 f6 r =
  case r of {
   RLW_S0 -> f;
   RLW_S1 -> f0;
   RLW_S2 -> f1;
   RLW_S3 -> f2;
   RLW_S4 -> f3;
   RLW_S5 -> f4;
   RLW_S6 -> f5;
   RLW_Sbad -> f6}

rlw_state_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Rlw_state ->
                 a1
rlw_state_rec =
  rlw_state_rect

rlw_transition :: Rlw_state -> Bool -> Rlw_state
rlw_transition s b =
  case s of {
   RLW_S0 ->
    case b of {
     True -> RLW_S4;
     False -> RLW_S1};
   RLW_S1 ->
    case b of {
     True -> RLW_S2;
     False -> RLW_S1};
   RLW_S2 ->
    case b of {
     True -> RLW_S2;
     False -> RLW_S3};
   RLW_S3 ->
    case b of {
     True -> RLW_Sbad;
     False -> RLW_S3};
   RLW_S4 ->
    case b of {
     True -> RLW_S4;
     False -> RLW_S5};
   RLW_S5 ->
    case b of {
     True -> RLW_S6;
     False -> RLW_S5};
   RLW_S6 ->
    case b of {
     True -> RLW_S6;
     False -> RLW_Sbad};
   RLW_Sbad -> RLW_Sbad}

rlw_accepting :: Rlw_state -> Bool
rlw_accepting s =
  case s of {
   RLW_S0 -> False;
   RLW_S1 -> False;
   RLW_Sbad -> False;
   _ -> True}

is_rlw_mask_rec :: Nat -> Rlw_state -> Z -> Bool
is_rlw_mask_rec n s x =
  case n of {
   O -> rlw_accepting s;
   S m ->
    case z_bin_decomp x of {
     Pair b y -> is_rlw_mask_rec m (rlw_transition s b) y}}

is_rlw_mask :: Nat -> Int -> Bool
is_rlw_mask wordsize_minus_one x =
  is_rlw_mask_rec (wordsize wordsize_minus_one) RLW_S0
    (unsigned wordsize_minus_one x)

cmp :: Nat -> Comparison0 -> Int -> Int -> Bool
cmp wordsize_minus_one c x y =
  case c of {
   Ceq -> eq wordsize_minus_one x y;
   Cne -> negb (eq wordsize_minus_one x y);
   Clt -> lt wordsize_minus_one x y;
   Cle -> negb (lt wordsize_minus_one y x);
   Cgt -> lt wordsize_minus_one y x;
   Cge -> negb (lt wordsize_minus_one x y)}

cmpu :: Nat -> Comparison0 -> Int -> Int -> Bool
cmpu wordsize_minus_one c x y =
  case c of {
   Ceq -> eq wordsize_minus_one x y;
   Cne -> negb (eq wordsize_minus_one x y);
   Clt -> ltu wordsize_minus_one x y;
   Cle -> negb (ltu wordsize_minus_one y x);
   Cgt -> ltu wordsize_minus_one y x;
   Cge -> negb (ltu wordsize_minus_one x y)}

notbool :: Nat -> Int -> Int
notbool wordsize_minus_one x =
  case eq wordsize_minus_one x (zero1 wordsize_minus_one) of {
   True -> one1 wordsize_minus_one;
   False -> zero1 wordsize_minus_one}

check_equal_on_range :: Nat -> (Int -> Int) -> (Int -> Int) -> Nat -> Bool
check_equal_on_range wordsize_minus_one f g n =
  case n of {
   O -> True;
   S n0 ->
    case eq wordsize_minus_one (f (repr wordsize_minus_one (of_nat1 n0)))
           (g (repr wordsize_minus_one (of_nat1 n0))) of {
     True -> check_equal_on_range wordsize_minus_one f g n0;
     False -> False}}

powerserie :: (List Z) -> Z
powerserie l =
  case l of {
   Nil -> Z0;
   Cons x xs -> add1 (two_p x) (powerserie xs)}

int_of_one_bits :: Nat -> (List Int) -> Int
int_of_one_bits wordsize_minus_one l =
  case l of {
   Nil -> zero1 wordsize_minus_one;
   Cons a b ->
    add2 wordsize_minus_one
      (shl wordsize_minus_one (one1 wordsize_minus_one) a)
      (int_of_one_bits wordsize_minus_one b)}

string_to_bool_list :: String -> List Bool
string_to_bool_list s =
  case s of {
   EmptyString -> Nil;
   String0 a s0 -> Cons
    (case ascii_dec a (Ascii False False False False True True False False) of {
      Left -> False;
      Right -> True}) (string_to_bool_list s0)}

string_to_Z_bool :: String -> Z -> Bool
string_to_Z_bool s =
  let {lb = string_to_bool_list s} in
  let {
   to_Z_bool l i =
     case l of {
      Nil -> False;
      Cons b l' ->
       case zeq i Z0 of {
        Left -> b;
        Right -> to_Z_bool l' (sub1 i (Zpos XH))}}}
  in to_Z_bool (rev lb)

string_to_int :: Nat -> String -> Int
string_to_int n s =
  let {zb = string_to_Z_bool s} in repr n (z_of_bits n zb)

type Int1 = Int

type Int2 = Int

type Int3 = Int

type Int8 = Int

type Int16 = Int

type Int32 = Int

type Int80 = Int

type Port_number = Int8

type Interrupt_type = Int8

type Selector = Int16

data Register =
   EAX
 | ECX
 | EDX
 | EBX
 | ESP
 | EBP
 | ESI
 | EDI

register_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Register ->
                 a1
register_rect f f0 f1 f2 f3 f4 f5 f6 r =
  case r of {
   EAX -> f;
   ECX -> f0;
   EDX -> f1;
   EBX -> f2;
   ESP -> f3;
   EBP -> f4;
   ESI -> f5;
   EDI -> f6}

register_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Register ->
                a1
register_rec =
  register_rect

register_eq_dec :: Register -> Register -> Sumbool
register_eq_dec x y =
  register_rec (\y0 ->
    case y0 of {
     EAX -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     ECX -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     EDX -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     EBX -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     ESP -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     EBP -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     ESI -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     EDI -> Left;
     _ -> Right}) x y

data Scale =
   Scale1
 | Scale2
 | Scale4
 | Scale8

data Segment_register =
   ES
 | CS
 | SS
 | DS
 | FS
 | GS

segment_register_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Segment_register
                         -> a1
segment_register_rect f f0 f1 f2 f3 f4 s =
  case s of {
   ES -> f;
   CS -> f0;
   SS -> f1;
   DS -> f2;
   FS -> f3;
   GS -> f4}

segment_register_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Segment_register
                        -> a1
segment_register_rec =
  segment_register_rect

segment_register_eq_dec :: Segment_register -> Segment_register -> Sumbool
segment_register_eq_dec x y =
  segment_register_rec (\y0 ->
    case y0 of {
     ES -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     CS -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     SS -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     DS -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     FS -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     GS -> Left;
     _ -> Right}) x y

data Control_register =
   CR0
 | CR2
 | CR3
 | CR4

control_register_rect :: a1 -> a1 -> a1 -> a1 -> Control_register -> a1
control_register_rect f f0 f1 f2 c =
  case c of {
   CR0 -> f;
   CR2 -> f0;
   CR3 -> f1;
   CR4 -> f2}

control_register_rec :: a1 -> a1 -> a1 -> a1 -> Control_register -> a1
control_register_rec =
  control_register_rect

control_register_eq_dec :: Control_register -> Control_register -> Sumbool
control_register_eq_dec x y =
  control_register_rec (\y0 ->
    case y0 of {
     CR0 -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     CR2 -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     CR3 -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     CR4 -> Left;
     _ -> Right}) x y

data Debug_register =
   DR0
 | DR1
 | DR2
 | DR3
 | DR6
 | DR7

debug_register_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Debug_register ->
                       a1
debug_register_rect f f0 f1 f2 f3 f4 d =
  case d of {
   DR0 -> f;
   DR1 -> f0;
   DR2 -> f1;
   DR3 -> f2;
   DR6 -> f3;
   DR7 -> f4}

debug_register_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Debug_register ->
                      a1
debug_register_rec =
  debug_register_rect

debug_register_eq_dec :: Debug_register -> Debug_register -> Sumbool
debug_register_eq_dec x y =
  debug_register_rec (\y0 ->
    case y0 of {
     DR0 -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     DR1 -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     DR2 -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     DR3 -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     DR6 -> Left;
     _ -> Right}) (\y0 ->
    case y0 of {
     DR7 -> Left;
     _ -> Right}) x y

data Address =
   MkAddress Int32 (Option Register) (Option (Prod Scale Register))

addrDisp :: Address -> Int32
addrDisp a =
  case a of {
   MkAddress addrDisp0 addrBase0 addrIndex0 -> addrDisp0}

addrBase :: Address -> Option Register
addrBase a =
  case a of {
   MkAddress addrDisp0 addrBase0 addrIndex0 -> addrBase0}

addrIndex :: Address -> Option (Prod Scale Register)
addrIndex a =
  case a of {
   MkAddress addrDisp0 addrBase0 addrIndex0 -> addrIndex0}

data Operand =
   Imm_op Int32
 | Reg_op Register
 | Address_op Address
 | Offset_op Int32

data Reg_or_immed =
   Reg_ri Register
 | Imm_ri Int8

data Condition_type =
   O_ct
 | NO_ct
 | B_ct
 | NB_ct
 | E_ct
 | NE_ct
 | BE_ct
 | NBE_ct
 | S_ct
 | NS_ct
 | P_ct
 | NP_ct
 | L_ct
 | NL_ct
 | LE_ct
 | NLE_ct

data Fp_operand =
   FPS_op Int3
 | FPM16_op Address
 | FPM32_op Address
 | FPM64_op Address
 | FPM80_op Address

data Fp_condition_type =
   B_fct
 | E_fct
 | BE_fct
 | U_fct
 | NB_fct
 | NE_fct
 | NBE_fct
 | NU_fct

data Mmx_register =
   MM0
 | MM1
 | MM2
 | MM3
 | MM4
 | MM5
 | MM6
 | MM7

data Mmx_granularity =
   MMX_8
 | MMX_16
 | MMX_32
 | MMX_64

data Mmx_operand =
   GP_Reg_op Register
 | MMX_Addr_op Address
 | MMX_Reg_op Mmx_register
 | MMX_Imm_op Int32

data Sse_register =
   XMM0
 | XMM1
 | XMM2
 | XMM3
 | XMM4
 | XMM5
 | XMM6
 | XMM7

data Sse_operand =
   SSE_XMM_Reg_op Sse_register
 | SSE_MM_Reg_op Mmx_register
 | SSE_Addr_op Address
 | SSE_GP_Reg_op Register
 | SSE_Imm_op Int32

data Instr =
   AAA
 | AAD
 | AAM
 | AAS
 | ADC Bool Operand Operand
 | ADD Bool Operand Operand
 | AND Bool Operand Operand
 | ARPL Operand Operand
 | BOUND Operand Operand
 | BSF Operand Operand
 | BSR Operand Operand
 | BSWAP Register
 | BT Operand Operand
 | BTC Operand Operand
 | BTR Operand Operand
 | BTS Operand Operand
 | CALL Bool Bool Operand (Option Selector)
 | CDQ
 | CLC
 | CLD
 | CLI
 | CLTS
 | CMC
 | CMOVcc Condition_type Operand Operand
 | CMP Bool Operand Operand
 | CMPS Bool
 | CMPXCHG Bool Operand Operand
 | CPUID
 | CWDE
 | DAA
 | DAS
 | DEC Bool Operand
 | DIV Bool Operand
 | F2XM1
 | FABS
 | FADD Bool Fp_operand
 | FADDP Fp_operand
 | FBLD Fp_operand
 | FBSTP Fp_operand
 | FCHS
 | FCMOVcc Fp_condition_type Fp_operand
 | FCOM Fp_operand
 | FCOMP Fp_operand
 | FCOMPP
 | FCOMIP Fp_operand
 | FCOS
 | FDECSTP
 | FDIV Bool Fp_operand
 | FDIVP Fp_operand
 | FDIVR Bool Fp_operand
 | FDIVRP Fp_operand
 | FFREE Fp_operand
 | FIADD Fp_operand
 | FICOM Fp_operand
 | FICOMP Fp_operand
 | FIDIV Fp_operand
 | FIDIVR Fp_operand
 | FILD Fp_operand
 | FIMUL Fp_operand
 | FINCSTP
 | FIST Fp_operand
 | FISTP Fp_operand
 | FISUB Fp_operand
 | FISUBR Fp_operand
 | FLD Fp_operand
 | FLD1
 | FLDCW Fp_operand
 | FLDENV Fp_operand
 | FLDL2E
 | FLDL2T
 | FLDLG2
 | FLDLN2
 | FLDPI
 | FLDZ
 | FMUL Bool Fp_operand
 | FMULP Fp_operand
 | FNCLEX
 | FNINIT
 | FNOP
 | FNSAVE Fp_operand
 | FNSTCW Fp_operand
 | FNSTSW (Option Fp_operand)
 | FPATAN
 | FPREM
 | FPREM1
 | FPTAN
 | FRNDINT
 | FRSTOR Fp_operand
 | FSCALE
 | FSIN
 | FSINCOS
 | FSQRT
 | FST Fp_operand
 | FSTENV Fp_operand
 | FSTP Fp_operand
 | FSUB Bool Fp_operand
 | FSUBP Fp_operand
 | FSUBR Bool Fp_operand
 | FSUBRP Fp_operand
 | FTST
 | FUCOM Fp_operand
 | FUCOMP Fp_operand
 | FUCOMPP
 | FUCOMI Fp_operand
 | FUCOMIP Fp_operand
 | FXAM
 | FXCH Fp_operand
 | FXTRACT
 | FYL2X
 | FYL2XP1
 | FWAIT
 | EMMS
 | MOVD Mmx_operand Mmx_operand
 | MOVQ Mmx_operand Mmx_operand
 | PACKSSDW Mmx_operand Mmx_operand
 | PACKSSWB Mmx_operand Mmx_operand
 | PACKUSWB Mmx_operand Mmx_operand
 | PADD Mmx_granularity Mmx_operand Mmx_operand
 | PADDS Mmx_granularity Mmx_operand Mmx_operand
 | PADDUS Mmx_granularity Mmx_operand Mmx_operand
 | PAND Mmx_operand Mmx_operand
 | PANDN Mmx_operand Mmx_operand
 | PCMPEQ Mmx_granularity Mmx_operand Mmx_operand
 | PCMPGT Mmx_granularity Mmx_operand Mmx_operand
 | PMADDWD Mmx_operand Mmx_operand
 | PMULHUW Mmx_operand Mmx_operand
 | PMULHW Mmx_operand Mmx_operand
 | PMULLW Mmx_operand Mmx_operand
 | POR Mmx_operand Mmx_operand
 | PSLL Mmx_granularity Mmx_operand Mmx_operand
 | PSRA Mmx_granularity Mmx_operand Mmx_operand
 | PSRL Mmx_granularity Mmx_operand Mmx_operand
 | PSUB Mmx_granularity Mmx_operand Mmx_operand
 | PSUBS Mmx_granularity Mmx_operand Mmx_operand
 | PSUBUS Mmx_granularity Mmx_operand Mmx_operand
 | PUNPCKH Mmx_granularity Mmx_operand Mmx_operand
 | PUNPCKL Mmx_granularity Mmx_operand Mmx_operand
 | PXOR Mmx_operand Mmx_operand
 | ADDPS Sse_operand Sse_operand
 | ADDSS Sse_operand Sse_operand
 | ANDNPS Sse_operand Sse_operand
 | ANDPS Sse_operand Sse_operand
 | CMPPS Sse_operand Sse_operand Sse_operand
 | CMPSS Sse_operand Sse_operand Sse_operand
 | COMISS Sse_operand Sse_operand
 | CVTPI2PS Sse_operand Sse_operand
 | CVTPS2PI Sse_operand Sse_operand
 | CVTSI2SS Sse_operand Sse_operand
 | CVTSS2SI Sse_operand Sse_operand
 | CVTTPS2PI Sse_operand Sse_operand
 | CVTTSS2SI Sse_operand Sse_operand
 | DIVPS Sse_operand Sse_operand
 | DIVSS Sse_operand Sse_operand
 | LDMXCSR Sse_operand
 | MAXPS Sse_operand Sse_operand
 | MAXSS Sse_operand Sse_operand
 | MINPS Sse_operand Sse_operand
 | MINSS Sse_operand Sse_operand
 | MOVAPS Sse_operand Sse_operand
 | MOVHLPS Sse_operand Sse_operand
 | MOVHPS Sse_operand Sse_operand
 | MOVLHPS Sse_operand Sse_operand
 | MOVLPS Sse_operand Sse_operand
 | MOVMSKPS Sse_operand Sse_operand
 | MOVSS Sse_operand Sse_operand
 | MOVUPS Sse_operand Sse_operand
 | MULPS Sse_operand Sse_operand
 | MULSS Sse_operand Sse_operand
 | ORPS Sse_operand Sse_operand
 | RCPPS Sse_operand Sse_operand
 | RCPSS Sse_operand Sse_operand
 | RSQRTPS Sse_operand Sse_operand
 | RSQRTSS Sse_operand Sse_operand
 | SHUFPS Sse_operand Sse_operand Sse_operand
 | SQRTPS Sse_operand Sse_operand
 | SQRTSS Sse_operand Sse_operand
 | STMXCSR Sse_operand
 | SUBPS Sse_operand Sse_operand
 | SUBSS Sse_operand Sse_operand
 | UCOMISS Sse_operand Sse_operand
 | UNPCKHPS Sse_operand Sse_operand
 | UNPCKLPS Sse_operand Sse_operand
 | XORPS Sse_operand Sse_operand
 | PAVGB Sse_operand Sse_operand
 | PEXTRW Sse_operand Sse_operand Sse_operand
 | PINSRW Sse_operand Sse_operand Sse_operand
 | PMAXSW Sse_operand Sse_operand
 | PMAXUB Sse_operand Sse_operand
 | PMINSW Sse_operand Sse_operand
 | PMINUB Sse_operand Sse_operand
 | PMOVMSKB Sse_operand Sse_operand
 | PSADBW Sse_operand Sse_operand
 | PSHUFW Sse_operand Sse_operand Sse_operand
 | MASKMOVQ Sse_operand Sse_operand
 | MOVNTPS Sse_operand Sse_operand
 | MOVNTQ Sse_operand Sse_operand
 | PREFETCHT0 Sse_operand
 | PREFETCHT1 Sse_operand
 | PREFETCHT2 Sse_operand
 | PREFETCHNTA Sse_operand
 | SFENCE
 | HLT
 | IDIV Bool Operand
 | IMUL Bool Operand (Option Operand) (Option Int32)
 | IN Bool (Option Port_number)
 | INC Bool Operand
 | INS Bool
 | INTn Interrupt_type
 | INT
 | INTO
 | INVD
 | INVLPG Operand
 | IRET
 | Jcc Condition_type Int32
 | JCXZ Int8
 | JMP Bool Bool Operand (Option Selector)
 | LAHF
 | LAR Operand Operand
 | LDS Operand Operand
 | LEA Operand Operand
 | LEAVE
 | LES Operand Operand
 | LFS Operand Operand
 | LGDT Operand
 | LGS Operand Operand
 | LIDT Operand
 | LLDT Operand
 | LMSW Operand
 | LODS Bool
 | LOOP Int8
 | LOOPZ Int8
 | LOOPNZ Int8
 | LSL Operand Operand
 | LSS Operand Operand
 | LTR Operand
 | MOV Bool Operand Operand
 | MOVCR Bool Control_register Register
 | MOVDR Bool Debug_register Register
 | MOVSR Bool Segment_register Operand
 | MOVBE Operand Operand
 | MOVS Bool
 | MOVSX Bool Operand Operand
 | MOVZX Bool Operand Operand
 | MUL Bool Operand
 | NEG Bool Operand
 | NOP Operand
 | NOT Bool Operand
 | OR Bool Operand Operand
 | OUT Bool (Option Port_number)
 | OUTS Bool
 | POP Operand
 | POPSR Segment_register
 | POPA
 | POPF
 | PUSH Bool Operand
 | PUSHSR Segment_register
 | PUSHA
 | PUSHF
 | RCL Bool Operand Reg_or_immed
 | RCR Bool Operand Reg_or_immed
 | RDMSR
 | RDPMC
 | RDTSC
 | RDTSCP
 | RET Bool (Option Int16)
 | ROL Bool Operand Reg_or_immed
 | ROR Bool Operand Reg_or_immed
 | RSM
 | SAHF
 | SAR Bool Operand Reg_or_immed
 | SBB Bool Operand Operand
 | SCAS Bool
 | SETcc Condition_type Operand
 | SGDT Operand
 | SHL Bool Operand Reg_or_immed
 | SHLD Operand Register Reg_or_immed
 | SHR Bool Operand Reg_or_immed
 | SHRD Operand Register Reg_or_immed
 | SIDT Operand
 | SLDT Operand
 | SMSW Operand
 | STC
 | STD
 | STI
 | STOS Bool
 | STR Operand
 | SUB Bool Operand Operand
 | TEST Bool Operand Operand
 | UD2
 | VERR Operand
 | VERW Operand
 | WBINVD
 | WRMSR
 | XADD Bool Operand Operand
 | XCHG Bool Operand Operand
 | XLAT
 | XOR Bool Operand Operand

data Lock_or_rep =
   Lock
 | Rep
 | Repn

data Prefix =
   MkPrefix (Option Lock_or_rep) (Option Segment_register) Bool Bool

seg_override :: Prefix -> Option Segment_register
seg_override p =
  case p of {
   MkPrefix lock_rep seg_override0 op_override0 addr_override0 ->
    seg_override0}

op_override :: Prefix -> Bool
op_override p =
  case p of {
   MkPrefix lock_rep seg_override0 op_override0 addr_override0 ->
    op_override0}

addr_override :: Prefix -> Bool
addr_override p =
  case p of {
   MkPrefix lock_rep seg_override0 op_override0 addr_override0 ->
    addr_override0}

type Elt = Positive

elt_eq :: Positive -> Positive -> Sumbool
elt_eq =
  peq

data Tree a =
   Leaf
 | Node (Tree a) (Option a) (Tree a)

tree_rect :: a2 -> ((Tree a1) -> a2 -> (Option a1) -> (Tree a1) -> a2 -> a2)
             -> (Tree a1) -> a2
tree_rect f f0 t =
  case t of {
   Leaf -> f;
   Node t0 o t1 -> f0 t0 (tree_rect f f0 t0) o t1 (tree_rect f f0 t1)}

tree_rec :: a2 -> ((Tree a1) -> a2 -> (Option a1) -> (Tree a1) -> a2 -> a2)
            -> (Tree a1) -> a2
tree_rec =
  tree_rect

type T2 a = Tree a

eq0 :: (a1 -> a1 -> Sumbool) -> (T2 a1) -> (T2 a1) -> Sumbool
eq0 eqA a b =
  tree_rect (\b0 ->
    case b0 of {
     Leaf -> Left;
     Node t0 o t1 -> Right}) (\t0 x o t1 x0 b0 ->
    case b0 of {
     Leaf -> Right;
     Node t2 o0 t3 ->
      sumbool_rec (\_ ->
        eq_rec_r t2
          (sumbool_rec (\_ ->
            eq_rec_r o0
              (sumbool_rec (\_ -> eq_rec_r t3 Left t1) (\_ -> Right) (x0 t3))
              o) (\_ -> Right)
            (option_rect (\a0 o3 ->
              case o3 of {
               Some a1 ->
                sumbool_rec (\_ -> eq_rec_r a1 Left a0) (\_ -> Right)
                  (eqA a0 a1);
               None -> Right}) (\o3 ->
              case o3 of {
               Some a0 -> Right;
               None -> Left}) o o0)) t0) (\_ -> Right) (x t2)}) a b

empty :: T2 a1
empty =
  Leaf

get :: Positive -> (T2 a1) -> Option a1
get i m =
  case m of {
   Leaf -> None;
   Node l o r ->
    case i of {
     XI ii -> get ii r;
     XO ii -> get ii l;
     XH -> o}}

set :: Positive -> a1 -> (T2 a1) -> T2 a1
set i v m =
  case m of {
   Leaf ->
    case i of {
     XI ii -> Node Leaf None (set ii v Leaf);
     XO ii -> Node (set ii v Leaf) None Leaf;
     XH -> Node Leaf (Some v) Leaf};
   Node l o r ->
    case i of {
     XI ii -> Node l o (set ii v r);
     XO ii -> Node (set ii v l) o r;
     XH -> Node l (Some v) r}}

remove :: Positive -> (T2 a1) -> T2 a1
remove i m =
  case i of {
   XI ii ->
    case m of {
     Leaf -> Leaf;
     Node l o r ->
      case l of {
       Leaf ->
        case o of {
         Some a -> Node l o (remove ii r);
         None ->
          case remove ii r of {
           Leaf -> Leaf;
           Node t o0 t0 -> Node Leaf None (Node t o0 t0)}};
       Node t o0 t0 -> Node l o (remove ii r)}};
   XO ii ->
    case m of {
     Leaf -> Leaf;
     Node l o r ->
      case o of {
       Some a -> Node (remove ii l) o r;
       None ->
        case r of {
         Leaf ->
          case remove ii l of {
           Leaf -> Leaf;
           Node t o0 t0 -> Node (Node t o0 t0) None Leaf};
         Node t o0 t0 -> Node (remove ii l) o r}}};
   XH ->
    case m of {
     Leaf -> Leaf;
     Node l o r ->
      case l of {
       Leaf ->
        case r of {
         Leaf -> Leaf;
         Node t o0 t0 -> Node l None r};
       Node t o0 t0 -> Node l None r}}}

bempty :: (T2 a1) -> Bool
bempty m =
  case m of {
   Leaf -> True;
   Node l o r ->
    case o of {
     Some a -> False;
     None -> andb (bempty l) (bempty r)}}

beq :: (a1 -> a1 -> Bool) -> (T2 a1) -> (T2 a1) -> Bool
beq beqA m1 m2 =
  case m1 of {
   Leaf -> bempty m2;
   Node l1 o1 r2 ->
    case m2 of {
     Leaf -> bempty m1;
     Node l2 o2 r3 ->
      andb
        (andb
          (case o1 of {
            Some y1 ->
             case o2 of {
              Some y2 -> beqA y1 y2;
              None -> False};
            None ->
             case o2 of {
              Some a -> False;
              None -> True}}) (beq beqA l1 l2)) (beq beqA r2 r3)}}

append0 :: Positive -> Positive -> Positive
append0 i j =
  case i of {
   XI ii -> XI (append0 ii j);
   XO ii -> XO (append0 ii j);
   XH -> j}

xmap :: (Positive -> a1 -> a2) -> (T2 a1) -> Positive -> T2 a2
xmap f m i =
  case m of {
   Leaf -> Leaf;
   Node l o r -> Node (xmap f l (append0 i (XO XH))) (option_map (f i) o)
    (xmap f r (append0 i (XI XH)))}

map0 :: (Positive -> a1 -> a2) -> (T2 a1) -> T2 a2
map0 f m =
  xmap f m XH

node' :: (T2 a1) -> (Option a1) -> (T2 a1) -> T2 a1
node' l x r =
  case l of {
   Leaf ->
    case x of {
     Some a -> Node l x r;
     None ->
      case r of {
       Leaf -> Leaf;
       Node t o t0 -> Node l x r}};
   Node t o t0 -> Node l x r}

xcombine_l :: ((Option a1) -> (Option a1) -> Option a1) -> (T2 a1) -> T2 a1
xcombine_l f m =
  case m of {
   Leaf -> Leaf;
   Node l o r -> node' (xcombine_l f l) (f o None) (xcombine_l f r)}

xcombine_r :: ((Option a1) -> (Option a1) -> Option a1) -> (T2 a1) -> T2 a1
xcombine_r f m =
  case m of {
   Leaf -> Leaf;
   Node l o r -> node' (xcombine_r f l) (f None o) (xcombine_r f r)}

combine :: ((Option a1) -> (Option a1) -> Option a1) -> (T2 a1) -> (T2 
           a1) -> T2 a1
combine f m1 m2 =
  case m1 of {
   Leaf -> xcombine_r f m2;
   Node l1 o1 r2 ->
    case m2 of {
     Leaf -> xcombine_l f m1;
     Node l2 o2 r3 -> node' (combine f l1 l2) (f o1 o2) (combine f r2 r3)}}

xelements :: (T2 a1) -> Positive -> List (Prod Positive a1)
xelements m i =
  case m of {
   Leaf -> Nil;
   Node l o r ->
    case o of {
     Some x ->
      app (xelements l (append0 i (XO XH))) (Cons (Pair i x)
        (xelements r (append0 i (XI XH))));
     None ->
      app (xelements l (append0 i (XO XH))) (xelements r (append0 i (XI XH)))}}

elements :: (T2 a1) -> List (Prod Positive a1)
elements m =
  xelements m XH

xget :: Positive -> Positive -> (T2 a1) -> Option a1
xget i j m =
  case i of {
   XI ii ->
    case j of {
     XI jj -> xget ii jj m;
     XO p -> None;
     XH -> get i m};
   XO ii ->
    case j of {
     XI p -> None;
     XO jj -> xget ii jj m;
     XH -> get i m};
   XH ->
    case j of {
     XH -> get i m;
     _ -> None}}

xkeys :: (T2 a1) -> Positive -> List Positive
xkeys m i =
  map fst (xelements m i)

xfold :: (a2 -> Positive -> a1 -> a2) -> Positive -> (T2 a1) -> a2 -> a2
xfold f i m v =
  case m of {
   Leaf -> v;
   Node l o r ->
    case o of {
     Some x ->
      let {v1 = xfold f (append0 i (XO XH)) l v} in
      let {v2 = f v1 i x} in xfold f (append0 i (XI XH)) r v2;
     None ->
      let {v1 = xfold f (append0 i (XO XH)) l v} in
      xfold f (append0 i (XI XH)) r v1}}

fold :: (a2 -> Positive -> a1 -> a2) -> (T2 a1) -> a2 -> a2
fold f m v =
  xfold f XH m v

type Elt0 = Positive

elt_eq0 :: Positive -> Positive -> Sumbool
elt_eq0 =
  peq

type T3 a = Prod a (T2 a)

eq1 :: (a1 -> a1 -> Sumbool) -> (T3 a1) -> (T3 a1) -> Sumbool
eq1 x a b =
  let {x0 = eq0 x} in
  prod_rect (\a0 b0 b1 ->
    case b1 of {
     Pair a1 t0 ->
      sumbool_rec (\_ ->
        eq_rec_r a1
          (sumbool_rec (\_ -> eq_rec_r t0 Left b0) (\_ -> Right) (x0 b0 t0))
          a0) (\_ -> Right) (x a0 a1)}) a b

init :: a1 -> Prod a1 (T2 a1)
init x =
  Pair x empty

get0 :: Positive -> (T3 a1) -> a1
get0 i m =
  case get i (snd m) of {
   Some x -> x;
   None -> fst m}

set0 :: Positive -> a1 -> (T3 a1) -> Prod a1 (T2 a1)
set0 i x m =
  Pair (fst m) (set i x (snd m))

map1 :: (a1 -> a2) -> (T3 a1) -> T3 a2
map1 f m =
  Pair (f (fst m)) (map0 (\x -> f) (snd m))

type T4 = Z

index :: Z -> Positive
index z =
  case z of {
   Z0 -> XH;
   Zpos p -> XO p;
   Zneg p -> XI p}

eq2 :: Z -> Z -> Sumbool
eq2 =
  zeq

data Monad m =
   Build_Monad (() -> () -> m) (() -> () -> m -> (() -> m) -> m)

return :: (Monad a1) -> a2 -> a1
return monad x =
  case monad of {
   Build_Monad return0 bind0 -> unsafeCoerce return0 __ x}

bind :: (Monad a1) -> a1 -> (a2 -> a1) -> a1
bind monad x x0 =
  case monad of {
   Build_Monad return0 bind0 -> unsafeCoerce bind0 __ __ x x0}

type R = () -- AXIOM TO BE REALIZED


r0 :: R
r0 =
  Prelude.error "AXIOM TO BE REALIZED"

r1 :: R
r1 =
  Prelude.error "AXIOM TO BE REALIZED"

rplus :: R -> R -> R
rplus =
  Prelude.error "AXIOM TO BE REALIZED"

rmult :: R -> R -> R
rmult =
  Prelude.error "AXIOM TO BE REALIZED"

ropp :: R -> R
ropp =
  Prelude.error "AXIOM TO BE REALIZED"

rinv :: R -> R
rinv =
  Prelude.error "AXIOM TO BE REALIZED"

total_order_T :: R -> R -> Sumor Sumbool
total_order_T =
  Prelude.error "AXIOM TO BE REALIZED"

zeven :: Z -> Bool
zeven n =
  case n of {
   Z0 -> True;
   Zpos p ->
    case p of {
     XO p0 -> True;
     _ -> False};
   Zneg p ->
    case p of {
     XO p0 -> True;
     _ -> False}}

type Radix =
  Z
  -- singleton inductive, whose constructor was Build_radix
  
radix_val :: Radix -> Z
radix_val r =
  r

cond_Zopp :: Bool -> Z -> Z
cond_Zopp b m =
  case b of {
   True -> opp m;
   False -> m}

p2R :: Positive -> R
p2R p =
  case p of {
   XI t ->
    case t of {
     XH -> rplus r1 (rplus r1 r1);
     _ -> rplus r1 (rmult (rplus r1 r1) (p2R t))};
   XO t ->
    case t of {
     XH -> rplus r1 r1;
     _ -> rmult (rplus r1 r1) (p2R t)};
   XH -> r1}

z2R :: Z -> R
z2R n =
  case n of {
   Z0 -> r0;
   Zpos p -> p2R p;
   Zneg p -> ropp (p2R p)}

rcompare :: R -> R -> Comparison
rcompare x y =
  case total_order_T x y of {
   Inleft s ->
    case s of {
     Left -> Lt;
     Right -> Eq};
   Inright -> Gt}

bpow :: Radix -> Z -> R
bpow r e =
  case e of {
   Z0 -> r1;
   Zpos p -> z2R (pow_pos (radix_val r) p);
   Zneg p -> rinv (z2R (pow_pos (radix_val r) p))}

data Float0 =
   Float Z Z

fnum :: Radix -> Float0 -> Z
fnum beta f =
  case f of {
   Float fnum0 fexp0 -> fnum0}

fexp :: Radix -> Float0 -> Z
fexp beta f =
  case f of {
   Float fnum0 fexp0 -> fexp0}

f2R :: Radix -> Float0 -> R
f2R beta f =
  rmult (z2R (fnum beta f)) (bpow beta (fexp beta f))

fLT_exp :: Z -> Z -> Z -> Z
fLT_exp emin prec e =
  max1 (sub1 e prec) emin

digits2_Pnat :: Positive -> Nat
digits2_Pnat n =
  case n of {
   XI p -> S (digits2_Pnat p);
   XO p -> S (digits2_Pnat p);
   XH -> O}

data Location =
   Loc_Exact
 | Loc_Inexact Comparison

new_location_even :: Z -> Z -> Location -> Location
new_location_even nb_steps k l =
  case zeq_bool k Z0 of {
   True ->
    case l of {
     Loc_Exact -> l;
     Loc_Inexact c -> Loc_Inexact Lt};
   False -> Loc_Inexact
    (case compare1 (mul1 (Zpos (XO XH)) k) nb_steps of {
      Eq ->
       case l of {
        Loc_Exact -> Eq;
        Loc_Inexact c -> Gt};
      x -> x})}

new_location_odd :: Z -> Z -> Location -> Location
new_location_odd nb_steps k l =
  case zeq_bool k Z0 of {
   True ->
    case l of {
     Loc_Exact -> l;
     Loc_Inexact c -> Loc_Inexact Lt};
   False -> Loc_Inexact
    (case compare1 (add1 (mul1 (Zpos (XO XH)) k) (Zpos XH)) nb_steps of {
      Eq ->
       case l of {
        Loc_Exact -> Lt;
        Loc_Inexact l0 -> l0};
      x -> x})}

new_location :: Z -> Z -> Location -> Location
new_location nb_steps =
  case zeven nb_steps of {
   True -> new_location_even nb_steps;
   False -> new_location_odd nb_steps}

cond_incr :: Bool -> Z -> Z
cond_incr b m =
  case b of {
   True -> add1 m (Zpos XH);
   False -> m}

round_sign_DN :: Bool -> Location -> Bool
round_sign_DN s l =
  case l of {
   Loc_Exact -> False;
   Loc_Inexact c -> s}

round_sign_UP :: Bool -> Location -> Bool
round_sign_UP s l =
  case l of {
   Loc_Exact -> False;
   Loc_Inexact c -> negb s}

round_N :: Bool -> Location -> Bool
round_N p l =
  case l of {
   Loc_Exact -> False;
   Loc_Inexact c ->
    case c of {
     Eq -> p;
     Lt -> False;
     Gt -> True}}

data Full_float =
   F754_zero Bool
 | F754_infinity Bool
 | F754_nan
 | F754_finite Bool Positive Z

data Binary_float =
   B754_zero Bool
 | B754_infinity Bool
 | B754_nan
 | B754_finite Bool Positive Z

fF2B :: Z -> Z -> Full_float -> Binary_float
fF2B prec emax x =
  case x of {
   F754_zero s -> B754_zero s;
   F754_infinity s -> B754_infinity s;
   F754_nan -> B754_nan;
   F754_finite s m e -> B754_finite s m e}

radix2 :: Radix
radix2 =
  Zpos (XO XH)

b2R :: Z -> Z -> Binary_float -> R
b2R prec emax f =
  case f of {
   B754_finite s m e -> f2R radix2 (Float (cond_Zopp s (Zpos m)) e);
   _ -> r0}

bopp :: Z -> Z -> Binary_float -> Binary_float
bopp prec emax x =
  case x of {
   B754_zero sx -> B754_zero (negb sx);
   B754_infinity sx -> B754_infinity (negb sx);
   B754_nan -> x;
   B754_finite sx mx ex -> B754_finite (negb sx) mx ex}

data Shr_record =
   Build_shr_record Z Bool Bool

shr_m :: Shr_record -> Z
shr_m s =
  case s of {
   Build_shr_record shr_m0 shr_r shr_s -> shr_m0}

shr_1 :: Shr_record -> Shr_record
shr_1 mrs =
  case mrs of {
   Build_shr_record m r s ->
    let {s0 = orb r s} in
    case m of {
     Z0 -> Build_shr_record Z0 False s0;
     Zpos p0 ->
      case p0 of {
       XI p -> Build_shr_record (Zpos p) True s0;
       XO p -> Build_shr_record (Zpos p) False s0;
       XH -> Build_shr_record Z0 True s0};
     Zneg p0 ->
      case p0 of {
       XI p -> Build_shr_record (Zneg p) True s0;
       XO p -> Build_shr_record (Zneg p) False s0;
       XH -> Build_shr_record Z0 True s0}}}

loc_of_shr_record :: Shr_record -> Location
loc_of_shr_record mrs =
  case mrs of {
   Build_shr_record shr_m0 shr_r shr_s ->
    case shr_r of {
     True ->
      case shr_s of {
       True -> Loc_Inexact Gt;
       False -> Loc_Inexact Eq};
     False ->
      case shr_s of {
       True -> Loc_Inexact Lt;
       False -> Loc_Exact}}}

shr_record_of_loc :: Z -> Location -> Shr_record
shr_record_of_loc m l =
  case l of {
   Loc_Exact -> Build_shr_record m False False;
   Loc_Inexact c ->
    case c of {
     Eq -> Build_shr_record m True False;
     Lt -> Build_shr_record m False True;
     Gt -> Build_shr_record m True True}}

shr0 :: Shr_record -> Z -> Z -> Prod Shr_record Z
shr0 mrs e n =
  case n of {
   Zpos p -> Pair (iter p shr_1 mrs) (add1 e n);
   _ -> Pair mrs e}

zdigits2 :: Z -> Z
zdigits2 m =
  case m of {
   Z0 -> m;
   Zpos p -> of_nat1 (S (digits2_Pnat p));
   Zneg p -> of_nat1 (S (digits2_Pnat p))}

shr_fexp :: Z -> Z -> Z -> Z -> Location -> Prod Shr_record Z
shr_fexp prec emax =
  let {emin = sub1 (sub1 (Zpos (XI XH)) emax) prec} in
  let {fexp0 = fLT_exp emin prec} in
  (\m e l ->
  shr0 (shr_record_of_loc m l) e (sub1 (fexp0 (add1 (zdigits2 m) e)) e))

data Mode =
   Mode_NE
 | Mode_ZR
 | Mode_DN
 | Mode_UP
 | Mode_NA

choice_mode :: Mode -> Bool -> Z -> Location -> Z
choice_mode m sx mx lx =
  case m of {
   Mode_NE -> cond_incr (round_N (negb (zeven mx)) lx) mx;
   Mode_ZR -> mx;
   Mode_DN -> cond_incr (round_sign_DN sx lx) mx;
   Mode_UP -> cond_incr (round_sign_UP sx lx) mx;
   Mode_NA -> cond_incr (round_N True lx) mx}

overflow_to_inf :: Mode -> Bool -> Bool
overflow_to_inf m s =
  case m of {
   Mode_ZR -> False;
   Mode_DN -> s;
   Mode_UP -> negb s;
   _ -> True}

binary_overflow :: Z -> Z -> Mode -> Bool -> Full_float
binary_overflow prec emax m s =
  case overflow_to_inf m s of {
   True -> F754_infinity s;
   False -> F754_finite s
    (case sub1 (pow1 (Zpos (XO XH)) prec) (Zpos XH) of {
      Zpos p -> p;
      _ -> XH}) (sub1 emax prec)}

binary_round_aux :: Z -> Z -> Mode -> Bool -> Positive -> Z -> Location ->
                    Full_float
binary_round_aux prec emax mode sx mx ex lx =
  case shr_fexp prec emax (Zpos mx) ex lx of {
   Pair mrs' e' ->
    case shr_fexp prec emax
           (choice_mode mode sx (shr_m mrs') (loc_of_shr_record mrs')) e'
           Loc_Exact of {
     Pair mrs'' e'' ->
      case shr_m mrs'' of {
       Z0 -> F754_zero sx;
       Zpos m ->
        case leb1 e'' (sub1 emax prec) of {
         True -> F754_finite sx m e'';
         False -> binary_overflow prec emax mode sx};
       Zneg p -> F754_nan}}}

bmult :: Z -> Z -> Mode -> Binary_float -> Binary_float -> Binary_float
bmult prec emax m x y =
  case x of {
   B754_zero sx ->
    case y of {
     B754_zero sy -> B754_zero (xorb sx sy);
     B754_infinity b -> B754_nan;
     B754_nan -> y;
     B754_finite sy m0 e -> B754_zero (xorb sx sy)};
   B754_infinity sx ->
    case y of {
     B754_zero b -> B754_nan;
     B754_infinity sy -> B754_infinity (xorb sx sy);
     B754_nan -> y;
     B754_finite sy m0 e -> B754_infinity (xorb sx sy)};
   B754_nan -> x;
   B754_finite sx mx ex ->
    case y of {
     B754_zero sy -> B754_zero (xorb sx sy);
     B754_infinity sy -> B754_infinity (xorb sx sy);
     B754_nan -> y;
     B754_finite sy my ey ->
      fF2B prec emax
        (binary_round_aux prec emax m (xorb sx sy) (mul mx my) (add1 ex ey)
          Loc_Exact)}}

shl_align :: Positive -> Z -> Z -> Prod Positive Z
shl_align mx ex ex' =
  case sub1 ex' ex of {
   Zneg d -> Pair (shift_pos d mx) ex';
   _ -> Pair mx ex}

shl_align_fexp :: Z -> Z -> Positive -> Z -> Prod Positive Z
shl_align_fexp prec emax =
  let {emin = sub1 (sub1 (Zpos (XI XH)) emax) prec} in
  let {fexp0 = fLT_exp emin prec} in
  (\mx ex ->
  shl_align mx ex (fexp0 (add1 (of_nat1 (S (digits2_Pnat mx))) ex)))

binary_round :: Z -> Z -> Mode -> Bool -> Positive -> Z -> Full_float
binary_round prec emax m sx mx ex =
  case shl_align_fexp prec emax mx ex of {
   Pair mz ez -> binary_round_aux prec emax m sx mz ez Loc_Exact}

binary_normalize :: Z -> Z -> Mode -> Z -> Z -> Bool -> Binary_float
binary_normalize prec emax mode m e szero =
  case m of {
   Z0 -> B754_zero szero;
   Zpos m0 -> fF2B prec emax (binary_round prec emax mode False m0 e);
   Zneg m0 -> fF2B prec emax (binary_round prec emax mode True m0 e)}

bplus :: Z -> Z -> Mode -> Binary_float -> Binary_float -> Binary_float
bplus prec emax m x y =
  case x of {
   B754_zero sx ->
    case y of {
     B754_zero sy ->
      case eqb sx sy of {
       True -> x;
       False ->
        case m of {
         Mode_DN -> B754_zero True;
         _ -> B754_zero False}};
     _ -> y};
   B754_infinity sx ->
    case y of {
     B754_infinity sy ->
      case eqb sx sy of {
       True -> x;
       False -> B754_nan};
     B754_nan -> y;
     _ -> x};
   B754_nan -> x;
   B754_finite sx mx ex ->
    case y of {
     B754_zero b -> x;
     B754_finite sy my ey ->
      let {ez = min1 ex ey} in
      binary_normalize prec emax m
        (add1 (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))))
          (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))) ez
        (case m of {
          Mode_DN -> True;
          _ -> False});
     _ -> y}}

bminus :: Z -> Z -> Mode -> Binary_float -> Binary_float -> Binary_float
bminus prec emax m x y =
  bplus prec emax m x (bopp prec emax y)

fdiv_core_binary :: Z -> Z -> Z -> Z -> Z -> Prod (Prod Z Z) Location
fdiv_core_binary prec m1 e1 m2 e2 =
  let {d1 = zdigits2 m1} in
  let {d2 = zdigits2 m2} in
  let {e = sub1 e1 e2} in
  case sub1 (add1 d2 prec) d1 of {
   Zpos p ->
    let {m = mul1 m1 (pow_pos (Zpos (XO XH)) p)} in
    let {e' = add1 e (Zneg p)} in
    case div_eucl0 m m2 of {
     Pair q r -> Pair (Pair q e') (new_location m2 r Loc_Exact)};
   _ ->
    case div_eucl0 m1 m2 of {
     Pair q r -> Pair (Pair q e) (new_location m2 r Loc_Exact)}}

bdiv :: Z -> Z -> Mode -> Binary_float -> Binary_float -> Binary_float
bdiv prec emax m x y =
  case x of {
   B754_zero sx ->
    case y of {
     B754_zero sy -> B754_nan;
     B754_infinity sy -> B754_zero (xorb sx sy);
     B754_nan -> y;
     B754_finite sy m0 e -> B754_zero (xorb sx sy)};
   B754_infinity sx ->
    case y of {
     B754_zero sy -> B754_infinity (xorb sx sy);
     B754_infinity sy -> B754_nan;
     B754_nan -> y;
     B754_finite sy m0 e -> B754_infinity (xorb sx sy)};
   B754_nan -> x;
   B754_finite sx mx ex ->
    case y of {
     B754_zero sy -> B754_infinity (xorb sx sy);
     B754_infinity sy -> B754_infinity (xorb sx sy);
     B754_nan -> y;
     B754_finite sy my ey ->
      fF2B prec emax
        (case fdiv_core_binary prec (Zpos mx) ex (Zpos my) ey of {
          Pair p lz ->
           case p of {
            Pair mz ez ->
             case mz of {
              Zpos mz0 -> binary_round_aux prec emax m (xorb sx sy) mz0 ez lz;
              _ -> F754_nan}}})}}

join_bits :: Z -> Z -> Bool -> Z -> Z -> Z
join_bits mw ew s m e =
  add1
    (mul1
      (add1
        (case s of {
          True -> pow1 (Zpos (XO XH)) ew;
          False -> Z0}) e) (pow1 (Zpos (XO XH)) mw)) m

split_bits :: Z -> Z -> Z -> Prod (Prod Bool Z) Z
split_bits mw ew x =
  let {mm = pow1 (Zpos (XO XH)) mw} in
  let {em = pow1 (Zpos (XO XH)) ew} in
  Pair (Pair (leb1 (mul1 mm em) x) (modulo0 x mm)) (modulo0 (div1 x mm) em)

bits_of_binary_float :: Z -> Z -> Binary_float -> Z
bits_of_binary_float mw ew =
  let {emax = pow1 (Zpos (XO XH)) (sub1 ew (Zpos XH))} in
  let {prec = add1 mw (Zpos XH)} in
  let {emin = sub1 (sub1 (Zpos (XI XH)) emax) prec} in
  (\x ->
  case x of {
   B754_zero sx -> join_bits mw ew sx Z0 Z0;
   B754_infinity sx ->
    join_bits mw ew sx Z0 (sub1 (pow1 (Zpos (XO XH)) ew) (Zpos XH));
   B754_nan ->
    join_bits mw ew False (sub1 (pow1 (Zpos (XO XH)) mw) (Zpos XH))
      (sub1 (pow1 (Zpos (XO XH)) ew) (Zpos XH));
   B754_finite sx mx ex ->
    case leb1 (pow1 (Zpos (XO XH)) mw) (Zpos mx) of {
     True ->
      join_bits mw ew sx (sub1 (Zpos mx) (pow1 (Zpos (XO XH)) mw))
        (add1 (sub1 ex emin) (Zpos XH));
     False -> join_bits mw ew sx (Zpos mx) Z0}})

binary_float_of_bits_aux :: Z -> Z -> Z -> Full_float
binary_float_of_bits_aux mw ew =
  let {emax = pow1 (Zpos (XO XH)) (sub1 ew (Zpos XH))} in
  let {prec = add1 mw (Zpos XH)} in
  let {emin = sub1 (sub1 (Zpos (XI XH)) emax) prec} in
  (\x ->
  case split_bits mw ew x of {
   Pair p ex ->
    case p of {
     Pair sx mx ->
      case zeq_bool ex Z0 of {
       True ->
        case mx of {
         Z0 -> F754_zero sx;
         Zpos px -> F754_finite sx px emin;
         Zneg p0 -> F754_nan};
       False ->
        case zeq_bool ex (sub1 (pow1 (Zpos (XO XH)) ew) (Zpos XH)) of {
         True ->
          case zeq_bool mx Z0 of {
           True -> F754_infinity sx;
           False -> F754_nan};
         False ->
          case add1 mx (pow1 (Zpos (XO XH)) mw) of {
           Zpos px -> F754_finite sx px (sub1 (add1 ex emin) (Zpos XH));
           _ -> F754_nan}}}}})

binary_float_of_bits :: Z -> Z -> Z -> Binary_float
binary_float_of_bits mw ew x =
  let {emax = pow1 (Zpos (XO XH)) (sub1 ew (Zpos XH))} in
  let {prec = add1 mw (Zpos XH)} in
  fF2B prec emax (binary_float_of_bits_aux mw ew x)

type Binary32 = Binary_float

b32_of_bits :: Z -> Binary32
b32_of_bits =
  binary_float_of_bits (Zpos (XI (XI (XI (XO XH))))) (Zpos (XO (XO (XO XH))))

bits_of_b32 :: Binary32 -> Z
bits_of_b32 =
  bits_of_binary_float (Zpos (XI (XI (XI (XO XH))))) (Zpos (XO (XO (XO XH))))

type Binary64 = Binary_float

b64_of_bits :: Z -> Binary64
b64_of_bits =
  binary_float_of_bits (Zpos (XO (XO (XI (XO (XI XH)))))) (Zpos (XI (XI (XO
    XH))))

bits_of_b64 :: Binary64 -> Z
bits_of_b64 =
  bits_of_binary_float (Zpos (XO (XO (XI (XO (XI XH)))))) (Zpos (XI (XI (XO
    XH))))

size1 :: Nat
size1 =
  O

size2 :: Nat
size2 =
  S O

size3 :: Nat
size3 =
  S (S O)

size4 :: Nat
size4 =
  S (S (S O))

size8 :: Nat
size8 =
  S (S (S (S (S (S (S O))))))

size16 :: Nat
size16 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))

size32 :: Nat
size32 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O))))))))))))))))))))))))))))))

size64 :: Nat
size64 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

size79 :: Nat
size79 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

size80 :: Nat
size80 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

type Int0 = Int

type Binary79 = Binary_float

b79_of_bits :: Z -> Binary79
b79_of_bits =
  binary_float_of_bits (Zpos (XI (XI (XI (XI (XI XH)))))) (Zpos (XI (XI (XI
    XH))))

bits_of_b79 :: Binary79 -> Z
bits_of_b79 =
  bits_of_binary_float (Zpos (XI (XI (XI (XI (XI XH)))))) (Zpos (XI (XI (XI
    XH))))

type De_float = Binary79

de_float_of_bits :: Z -> De_float
de_float_of_bits x =
  case split_bits (Zpos (XO (XO (XO (XO (XO (XO XH))))))) (Zpos (XI (XI (XI
         XH)))) x of {
   Pair p ex ->
    case p of {
     Pair sx mx ->
      let {
       mx' = modulo0 mx
               (pow1 (Zpos (XO XH)) (Zpos (XI (XI (XI (XI (XI XH)))))))}
      in
      b79_of_bits
        (join_bits (Zpos (XI (XI (XI (XI (XI XH)))))) (Zpos (XI (XI (XI
          XH)))) sx mx' ex)}}

bits_of_de_float :: De_float -> Z
bits_of_de_float f =
  let {x = bits_of_b79 f} in
  case split_bits (Zpos (XI (XI (XI (XI (XI XH)))))) (Zpos (XI (XI (XI XH))))
         x of {
   Pair p ex ->
    case p of {
     Pair sx mx ->
      case zeq_bool ex Z0 of {
       True ->
        join_bits (Zpos (XO (XO (XO (XO (XO (XO XH))))))) (Zpos (XI (XI (XI
          XH)))) sx mx ex;
       False ->
        case zeq_bool ex
               (sub1 (pow1 (Zpos (XO XH)) (Zpos (XI (XI (XI XH))))) (Zpos
                 XH)) of {
         True ->
          join_bits (Zpos (XO (XO (XO (XO (XO (XO XH))))))) (Zpos (XI (XI (XI
            XH)))) sx mx ex;
         False ->
          join_bits (Zpos (XO (XO (XO (XO (XO (XO XH))))))) (Zpos (XI (XI (XI
            XH)))) sx
            (add1 (pow1 (Zpos (XO XH)) (Zpos (XI (XI (XI (XI (XI XH)))))))
              mx) ex}}}}

size_addr :: Nat
size_addr =
  size32

data Flag =
   ID
 | VIP
 | VIF
 | AC
 | VM
 | RF
 | NT
 | IOPL
 | OF
 | DF
 | IF_flag
 | TF
 | SF
 | ZF
 | AF
 | PF
 | CF

flag_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
             -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Flag -> a1
flag_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 =
  case f16 of {
   ID -> f;
   VIP -> f0;
   VIF -> f1;
   AC -> f2;
   VM -> f3;
   RF -> f4;
   NT -> f5;
   IOPL -> f6;
   OF -> f7;
   DF -> f8;
   IF_flag -> f9;
   TF -> f10;
   SF -> f11;
   ZF -> f12;
   AF -> f13;
   PF -> f14;
   CF -> f15}

flag_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
            a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Flag -> a1
flag_rec =
  flag_rect

flag_eq_dec :: Flag -> Flag -> Sumbool
flag_eq_dec f1 f2 =
  flag_rec (\f0 ->
    case f0 of {
     ID -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     VIP -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     VIF -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     AC -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     VM -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     RF -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     NT -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     IOPL -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     OF -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     DF -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     IF_flag -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     TF -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     SF -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     ZF -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     AF -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     PF -> Left;
     _ -> Right}) (\f0 ->
    case f0 of {
     CF -> Left;
     _ -> Right}) f1 f2

data Fpu_flag =
   F_Busy
 | F_C3
 | F_C2
 | F_C1
 | F_C0
 | F_ES
 | F_SF
 | F_PE
 | F_UE
 | F_OE
 | F_ZE
 | F_DE
 | F_IE

fpu_flag_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
                 a1 -> a1 -> a1 -> Fpu_flag -> a1
fpu_flag_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 =
  case f12 of {
   F_Busy -> f;
   F_C3 -> f0;
   F_C2 -> f1;
   F_C1 -> f2;
   F_C0 -> f3;
   F_ES -> f4;
   F_SF -> f5;
   F_PE -> f6;
   F_UE -> f7;
   F_OE -> f8;
   F_ZE -> f9;
   F_DE -> f10;
   F_IE -> f11}

fpu_flag_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
                a1 -> a1 -> a1 -> Fpu_flag -> a1
fpu_flag_rec =
  fpu_flag_rect

data Fpu_ctrl_flag =
   F_Res15
 | F_Res14
 | F_Res13
 | F_Res7
 | F_Res6
 | F_IC
 | F_PM
 | F_UM
 | F_OM
 | F_ZM
 | F_DM
 | F_IM

fpu_ctrl_flag_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
                      a1 -> a1 -> a1 -> Fpu_ctrl_flag -> a1
fpu_ctrl_flag_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 =
  case f11 of {
   F_Res15 -> f;
   F_Res14 -> f0;
   F_Res13 -> f1;
   F_Res7 -> f2;
   F_Res6 -> f3;
   F_IC -> f4;
   F_PM -> f5;
   F_UM -> f6;
   F_OM -> f7;
   F_ZM -> f8;
   F_DM -> f9;
   F_IM -> f10}

fpu_ctrl_flag_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
                     -> a1 -> a1 -> Fpu_ctrl_flag -> a1
fpu_ctrl_flag_rec =
  fpu_ctrl_flag_rect

size11 :: Nat
size11 =
  S (S (S (S (S (S (S (S (S (S O)))))))))

size48 :: Nat
size48 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))

type Int48 = Int

data Loc =
   Reg_loc Register
 | Seg_reg_start_loc Segment_register
 | Seg_reg_limit_loc Segment_register
 | Flag_loc Flag
 | Control_register_loc Control_register
 | Debug_register_loc Debug_register
 | Pc_loc
 | Fpu_stktop_loc
 | Fpu_flag_loc Fpu_flag
 | Fpu_rctrl_loc
 | Fpu_pctrl_loc
 | Fpu_ctrl_flag_loc Fpu_ctrl_flag
 | Fpu_lastInstrPtr_loc
 | Fpu_lastDataPtr_loc
 | Fpu_lastOpcode_loc

loc_rect :: (Register -> a1) -> (Segment_register -> a1) -> (Segment_register
            -> a1) -> (Flag -> a1) -> (Control_register -> a1) ->
            (Debug_register -> a1) -> a1 -> a1 -> (Fpu_flag -> a1) -> a1 ->
            a1 -> (Fpu_ctrl_flag -> a1) -> a1 -> a1 -> a1 -> Nat -> Loc -> a1
loc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 n l =
  case l of {
   Reg_loc x -> f x;
   Seg_reg_start_loc x -> f0 x;
   Seg_reg_limit_loc x -> f1 x;
   Flag_loc x -> f2 x;
   Control_register_loc x -> f3 x;
   Debug_register_loc x -> f4 x;
   Pc_loc -> f5;
   Fpu_stktop_loc -> f6;
   Fpu_flag_loc x -> f7 x;
   Fpu_rctrl_loc -> f8;
   Fpu_pctrl_loc -> f9;
   Fpu_ctrl_flag_loc x -> f10 x;
   Fpu_lastInstrPtr_loc -> f11;
   Fpu_lastDataPtr_loc -> f12;
   Fpu_lastOpcode_loc -> f13}

loc_rec :: (Register -> a1) -> (Segment_register -> a1) -> (Segment_register
           -> a1) -> (Flag -> a1) -> (Control_register -> a1) ->
           (Debug_register -> a1) -> a1 -> a1 -> (Fpu_flag -> a1) -> a1 -> a1
           -> (Fpu_ctrl_flag -> a1) -> a1 -> a1 -> a1 -> Nat -> Loc -> a1
loc_rec =
  loc_rect

type Location0 = Loc

data Arr =
   Fpu_datareg
 | Fpu_tag

arr_rect :: a1 -> a1 -> Nat -> Nat -> Arr -> a1
arr_rect f f0 n n0 a =
  case a of {
   Fpu_datareg -> f;
   Fpu_tag -> f0}

arr_rec :: a1 -> a1 -> Nat -> Nat -> Arr -> a1
arr_rec =
  arr_rect

type Array = Arr

type Fmap a b = a -> b

upd :: (a1 -> a1 -> Sumbool) -> (Fmap a1 a2) -> a1 -> a2 -> Fmap a1 a2
upd eq_dec3 f x v y =
  case eq_dec3 x y of {
   Left -> v;
   Right -> f y}

look :: (Fmap a1 a2) -> a1 -> a2
look f x =
  f x

data Core_state =
   Build_core_state (Fmap Register Int32) (Fmap Segment_register Int32) 
 (Fmap Segment_register Int32) (Fmap Flag Int1) (Fmap Control_register Int32) 
 (Fmap Debug_register Int32) Int0

core_state_rect :: ((Fmap Register Int32) -> (Fmap Segment_register Int32) ->
                   (Fmap Segment_register Int32) -> (Fmap Flag Int1) -> (Fmap
                   Control_register Int32) -> (Fmap Debug_register Int32) ->
                   Int0 -> a1) -> Core_state -> a1
core_state_rect f c =
  case c of {
   Build_core_state x x0 x1 x2 x3 x4 x5 -> f x x0 x1 x2 x3 x4 x5}

core_state_rec :: ((Fmap Register Int32) -> (Fmap Segment_register Int32) ->
                  (Fmap Segment_register Int32) -> (Fmap Flag Int1) -> (Fmap
                  Control_register Int32) -> (Fmap Debug_register Int32) ->
                  Int0 -> a1) -> Core_state -> a1
core_state_rec =
  core_state_rect

gp_regs :: Core_state -> Fmap Register Int32
gp_regs c =
  case c of {
   Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
    control_regs0 debug_regs0 pc_reg0 -> gp_regs0}

seg_regs_starts :: Core_state -> Fmap Segment_register Int32
seg_regs_starts c =
  case c of {
   Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
    control_regs0 debug_regs0 pc_reg0 -> seg_regs_starts0}

seg_regs_limits :: Core_state -> Fmap Segment_register Int32
seg_regs_limits c =
  case c of {
   Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
    control_regs0 debug_regs0 pc_reg0 -> seg_regs_limits0}

flags_reg :: Core_state -> Fmap Flag Int1
flags_reg c =
  case c of {
   Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
    control_regs0 debug_regs0 pc_reg0 -> flags_reg0}

control_regs :: Core_state -> Fmap Control_register Int32
control_regs c =
  case c of {
   Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
    control_regs0 debug_regs0 pc_reg0 -> control_regs0}

debug_regs :: Core_state -> Fmap Debug_register Int32
debug_regs c =
  case c of {
   Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
    control_regs0 debug_regs0 pc_reg0 -> debug_regs0}

pc_reg :: Core_state -> Int0
pc_reg c =
  case c of {
   Build_core_state gp_regs0 seg_regs_starts0 seg_regs_limits0 flags_reg0
    control_regs0 debug_regs0 pc_reg0 -> pc_reg0}

data Fpu_state =
   Build_fpu_state (Fmap Int3 Int80) Int16 Int16 (Fmap Int3 Int2) Int48 
 Int48 Int0

fpu_state_rect :: ((Fmap Int3 Int80) -> Int16 -> Int16 -> (Fmap Int3 
                  Int2) -> Int48 -> Int48 -> Int0 -> a1) -> Fpu_state -> a1
fpu_state_rect f f0 =
  case f0 of {
   Build_fpu_state x x0 x1 x2 x3 x4 x5 -> f x x0 x1 x2 x3 x4 x5}

fpu_state_rec :: ((Fmap Int3 Int80) -> Int16 -> Int16 -> (Fmap Int3 Int2) ->
                 Int48 -> Int48 -> Int0 -> a1) -> Fpu_state -> a1
fpu_state_rec =
  fpu_state_rect

fpu_data_regs :: Fpu_state -> Fmap Int3 Int80
fpu_data_regs f =
  case f of {
   Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
    fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0 -> fpu_data_regs0}

fpu_status :: Fpu_state -> Int16
fpu_status f =
  case f of {
   Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
    fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0 -> fpu_status0}

fpu_control :: Fpu_state -> Int16
fpu_control f =
  case f of {
   Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
    fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0 -> fpu_control0}

fpu_tags :: Fpu_state -> Fmap Int3 Int2
fpu_tags f =
  case f of {
   Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
    fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0 -> fpu_tags0}

fpu_lastInstrPtr :: Fpu_state -> Int48
fpu_lastInstrPtr f =
  case f of {
   Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
    fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0 -> fpu_lastInstrPtr0}

fpu_lastDataPtr :: Fpu_state -> Int48
fpu_lastDataPtr f =
  case f of {
   Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
    fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0 -> fpu_lastDataPtr0}

fpu_lastOpcode :: Fpu_state -> Int0
fpu_lastOpcode f =
  case f of {
   Build_fpu_state fpu_data_regs0 fpu_status0 fpu_control0 fpu_tags0
    fpu_lastInstrPtr0 fpu_lastDataPtr0 fpu_lastOpcode0 -> fpu_lastOpcode0}

data Mach =
   Build_mach Core_state Fpu_state

mach_rect :: (Core_state -> Fpu_state -> a1) -> Mach -> a1
mach_rect f m =
  case m of {
   Build_mach x x0 -> f x x0}

mach_rec :: (Core_state -> Fpu_state -> a1) -> Mach -> a1
mach_rec =
  mach_rect

core :: Mach -> Core_state
core m =
  case m of {
   Build_mach core0 fpu0 -> core0}

fpu :: Mach -> Fpu_state
fpu m =
  case m of {
   Build_mach core0 fpu0 -> fpu0}

type Mach_state = Mach

get_bits_rng :: Nat -> Int0 -> Nat -> Nat -> Int0
get_bits_rng s i n m =
  repr (minus m n) (unsigned s (shru s i (repr s (of_nat1 n))))

set_bits_rng :: Nat -> Int0 -> Nat -> Nat -> Int0 -> Int0
set_bits_rng s i n m v =
  let {
   highbits = unsigned s (shru s i (repr s (add1 (of_nat1 m) (Zpos XH))))}
  in
  let {lowbits = modulo0 (unsigned s i) (two_power_nat n)} in
  repr s
    (add1 (add1 lowbits (mul1 (unsigned (minus m n) v) (two_power_nat n)))
      (mul1 highbits (two_power_nat (plus m (S O)))))

get_bit :: Nat -> Int0 -> Z -> Int1
get_bit s i n =
  let {wordsize0 = S s} in
  case bits_of_Z wordsize0 (unsigned s i) n of {
   True -> one1 O;
   False -> zero1 O}

set_bit :: Nat -> Int0 -> Nat -> Bool -> Int0
set_bit s i n v =
  set_bits_rng s i n n (bool_to_int (minus n n) v)

get_fpu_flag_reg :: Fpu_flag -> Fpu_state -> Int1
get_fpu_flag_reg f fs =
  case f of {
   F_Busy ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XI (XI (XI XH))));
   F_C3 ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XO (XI (XI XH))));
   F_C2 ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XO (XI (XO XH))));
   F_C1 ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XI (XO (XO XH))));
   F_C0 ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XO (XO (XO XH))));
   F_ES ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XI (XI XH)));
   F_SF ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XO (XI XH)));
   F_PE ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XI (XO XH)));
   F_UE ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XO (XO XH)));
   F_OE ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XI XH));
   F_ZE ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos (XO XH));
   F_DE ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) (Zpos XH);
   F_IE ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_status fs) Z0}

get_stktop_reg :: Fpu_state -> Int3
get_stktop_reg fs =
  get_bits_rng (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
    (fpu_status fs) (S (S (S (S (S (S (S (S (S (S (S O))))))))))) (S (S (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))))

get_fpu_ctrl_flag_reg :: Fpu_ctrl_flag -> Fpu_state -> Int1
get_fpu_ctrl_flag_reg f fs =
  case f of {
   F_Res15 ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XI (XI (XI XH))));
   F_Res14 ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XO (XI (XI XH))));
   F_Res13 ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XI (XO (XI XH))));
   F_Res7 ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XI (XI XH)));
   F_Res6 ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XO (XI XH)));
   F_IC ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XO (XO (XI XH))));
   F_PM ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XI (XO XH)));
   F_UM ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XO (XO XH)));
   F_OM ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XI XH));
   F_ZM ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos (XO XH));
   F_DM ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) (Zpos XH);
   F_IM ->
    get_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
      (fpu_control fs) Z0}

get_rctrl_reg :: Fpu_state -> Int2
get_rctrl_reg fs =
  get_bits_rng (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
    (fpu_control fs) (S (S (S (S (S (S (S (S (S (S O)))))))))) (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))

get_pctrl_reg :: Fpu_state -> Int2
get_pctrl_reg fs =
  get_bits_rng (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
    (fpu_control fs) (S (S (S (S (S (S (S (S O)))))))) (S (S (S (S (S (S (S
    (S (S O)))))))))

get_location :: Nat -> Loc -> Mach_state -> Int0
get_location s l m =
  case l of {
   Reg_loc r -> look (gp_regs (core m)) r;
   Seg_reg_start_loc r -> look (seg_regs_starts (core m)) r;
   Seg_reg_limit_loc r -> look (seg_regs_limits (core m)) r;
   Flag_loc f -> look (flags_reg (core m)) f;
   Control_register_loc r -> look (control_regs (core m)) r;
   Debug_register_loc r -> look (debug_regs (core m)) r;
   Pc_loc -> pc_reg (core m);
   Fpu_stktop_loc -> get_stktop_reg (fpu m);
   Fpu_flag_loc f -> get_fpu_flag_reg f (fpu m);
   Fpu_ctrl_flag_loc f -> get_fpu_ctrl_flag_reg f (fpu m);
   Fpu_lastInstrPtr_loc -> fpu_lastInstrPtr (fpu m);
   Fpu_lastDataPtr_loc -> fpu_lastDataPtr (fpu m);
   Fpu_lastOpcode_loc -> fpu_lastOpcode (fpu m);
   _ -> get_rctrl_reg (fpu m)}

set_gp_reg :: Register -> Int32 -> Mach -> Mach
set_gp_reg r v m =
  Build_mach (Build_core_state (upd register_eq_dec (gp_regs (core m)) r v)
    (seg_regs_starts (core m)) (seg_regs_limits (core m))
    (flags_reg (core m)) (control_regs (core m)) (debug_regs (core m))
    (pc_reg (core m))) (fpu m)

set_seg_reg_start :: Segment_register -> Int32 -> Mach -> Mach
set_seg_reg_start r v m =
  Build_mach (Build_core_state (gp_regs (core m))
    (upd segment_register_eq_dec (seg_regs_starts (core m)) r v)
    (seg_regs_limits (core m)) (flags_reg (core m)) (control_regs (core m))
    (debug_regs (core m)) (pc_reg (core m))) (fpu m)

set_seg_reg_limit :: Segment_register -> Int32 -> Mach -> Mach
set_seg_reg_limit r v m =
  Build_mach (Build_core_state (gp_regs (core m)) (seg_regs_starts (core m))
    (upd segment_register_eq_dec (seg_regs_limits (core m)) r v)
    (flags_reg (core m)) (control_regs (core m)) (debug_regs (core m))
    (pc_reg (core m))) (fpu m)

set_flags_reg :: Flag -> Int1 -> Mach -> Mach
set_flags_reg r v m =
  Build_mach (Build_core_state (gp_regs (core m)) (seg_regs_starts (core m))
    (seg_regs_limits (core m)) (upd flag_eq_dec (flags_reg (core m)) r v)
    (control_regs (core m)) (debug_regs (core m)) (pc_reg (core m))) 
    (fpu m)

set_control_reg :: Control_register -> Int32 -> Mach -> Mach
set_control_reg r v m =
  Build_mach (Build_core_state (gp_regs (core m)) (seg_regs_starts (core m))
    (seg_regs_limits (core m)) (flags_reg (core m))
    (upd control_register_eq_dec (control_regs (core m)) r v)
    (debug_regs (core m)) (pc_reg (core m))) (fpu m)

set_debug_reg :: Debug_register -> Int32 -> Mach -> Mach
set_debug_reg r v m =
  Build_mach (Build_core_state (gp_regs (core m)) (seg_regs_starts (core m))
    (seg_regs_limits (core m)) (flags_reg (core m)) (control_regs (core m))
    (upd debug_register_eq_dec (debug_regs (core m)) r v) (pc_reg (core m)))
    (fpu m)

set_pc :: Int0 -> Mach -> Mach
set_pc v m =
  Build_mach (Build_core_state (gp_regs (core m)) (seg_regs_starts (core m))
    (seg_regs_limits (core m)) (flags_reg (core m)) (control_regs (core m))
    (debug_regs (core m)) v) (fpu m)

set_fpu_stktop_reg :: Int3 -> Mach -> Mach
set_fpu_stktop_reg v m =
  Build_mach (core m) (Build_fpu_state (fpu_data_regs (fpu m))
    (set_bits_rng (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))) (fpu_status (fpu m)) (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))) (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))) v)
    (fpu_control (fpu m)) (fpu_tags (fpu m)) (fpu_lastInstrPtr (fpu m))
    (fpu_lastDataPtr (fpu m)) (fpu_lastOpcode (fpu m)))

set_fpu_flags_reg :: Fpu_flag -> Int1 -> Mach -> Mach
set_fpu_flags_reg f v m =
  Build_mach (core m) (Build_fpu_state (fpu_data_regs (fpu m))
    (let {old_status = fpu_status (fpu m)} in
     let {b = negb (eq O v (zero1 O))} in
     case f of {
      F_Busy ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))) b;
      F_C3 ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))
         b;
      F_C2 ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S (S (S (S (S (S (S (S O)))))))))) b;
      F_C1 ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S (S (S (S (S (S (S O))))))))) b;
      F_C0 ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S (S (S (S (S (S O)))))))) b;
      F_ES ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S (S (S (S (S O))))))) b;
      F_SF ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S (S (S (S O)))))) b;
      F_PE ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S (S (S O))))) b;
      F_UE ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S (S O)))) b;
      F_OE ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S (S O))) b;
      F_ZE ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S (S O)) b;
      F_DE ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status (S O) b;
      F_IE ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_status O b}) (fpu_control (fpu m)) (fpu_tags (fpu m))
    (fpu_lastInstrPtr (fpu m)) (fpu_lastDataPtr (fpu m))
    (fpu_lastOpcode (fpu m)))

set_fpu_rctrl_reg :: Int2 -> Mach -> Mach
set_fpu_rctrl_reg v m =
  Build_mach (core m) (Build_fpu_state (fpu_data_regs (fpu m))
    (fpu_status (fpu m))
    (set_bits_rng (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))) (fpu_control (fpu m)) (S (S (S (S (S (S (S (S (S (S
      O)))))))))) (S (S (S (S (S (S (S (S (S (S (S O))))))))))) v)
    (fpu_tags (fpu m)) (fpu_lastInstrPtr (fpu m)) (fpu_lastDataPtr (fpu m))
    (fpu_lastOpcode (fpu m)))

set_fpu_pctrl_reg :: Int2 -> Mach -> Mach
set_fpu_pctrl_reg v m =
  Build_mach (core m) (Build_fpu_state (fpu_data_regs (fpu m))
    (fpu_status (fpu m))
    (set_bits_rng (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))) (fpu_control (fpu m)) (S (S (S (S (S (S (S (S
      O)))))))) (S (S (S (S (S (S (S (S (S O))))))))) v) (fpu_tags (fpu m))
    (fpu_lastInstrPtr (fpu m)) (fpu_lastDataPtr (fpu m))
    (fpu_lastOpcode (fpu m)))

set_fpu_ctrl_reg :: Fpu_ctrl_flag -> Int1 -> Mach -> Mach
set_fpu_ctrl_reg f v m =
  Build_mach (core m) (Build_fpu_state (fpu_data_regs (fpu m))
    (fpu_status (fpu m))
    (let {old_ctrl = fpu_control (fpu m)} in
     let {b = negb (eq O v (zero1 O))} in
     case f of {
      F_Res15 ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))) b;
      F_Res14 ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))) b;
      F_Res13 ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))) b;
      F_Res7 ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S (S (S (S (S (S O))))))) b;
      F_Res6 ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S (S (S (S (S O)))))) b;
      F_IC ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))) b;
      F_PM ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S (S (S (S O))))) b;
      F_UM ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S (S (S O)))) b;
      F_OM ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S (S O))) b;
      F_ZM ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S (S O)) b;
      F_DM ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl (S O) b;
      F_IM ->
       set_bit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))
         old_ctrl O b}) (fpu_tags (fpu m)) (fpu_lastInstrPtr (fpu m))
    (fpu_lastDataPtr (fpu m)) (fpu_lastOpcode (fpu m)))

set_fpu_lastInstrPtr_reg :: Int48 -> Mach -> Mach
set_fpu_lastInstrPtr_reg v m =
  Build_mach (core m) (Build_fpu_state (fpu_data_regs (fpu m))
    (fpu_status (fpu m)) (fpu_control (fpu m)) (fpu_tags (fpu m)) v
    (fpu_lastDataPtr (fpu m)) (fpu_lastOpcode (fpu m)))

set_fpu_lastDataPtr_reg :: Int48 -> Mach -> Mach
set_fpu_lastDataPtr_reg v m =
  Build_mach (core m) (Build_fpu_state (fpu_data_regs (fpu m))
    (fpu_status (fpu m)) (fpu_control (fpu m)) (fpu_tags (fpu m))
    (fpu_lastInstrPtr (fpu m)) v (fpu_lastOpcode (fpu m)))

set_lastOpcode_reg :: Int0 -> Mach -> Mach
set_lastOpcode_reg v m =
  Build_mach (core m) (Build_fpu_state (fpu_data_regs (fpu m))
    (fpu_status (fpu m)) (fpu_control (fpu m)) (fpu_tags (fpu m))
    (fpu_lastInstrPtr (fpu m)) (fpu_lastDataPtr (fpu m)) v)

set_location :: Nat -> Loc -> Int0 -> Mach -> Mach_state
set_location s l v m =
  case l of {
   Reg_loc r -> set_gp_reg r v m;
   Seg_reg_start_loc r -> set_seg_reg_start r v m;
   Seg_reg_limit_loc r -> set_seg_reg_limit r v m;
   Flag_loc f -> set_flags_reg f v m;
   Control_register_loc r -> set_control_reg r v m;
   Debug_register_loc r -> set_debug_reg r v m;
   Pc_loc -> set_pc v m;
   Fpu_stktop_loc -> set_fpu_stktop_reg v m;
   Fpu_flag_loc f -> set_fpu_flags_reg f v m;
   Fpu_rctrl_loc -> set_fpu_rctrl_reg v m;
   Fpu_pctrl_loc -> set_fpu_pctrl_reg v m;
   Fpu_ctrl_flag_loc f -> set_fpu_ctrl_reg f v m;
   Fpu_lastInstrPtr_loc -> set_fpu_lastInstrPtr_reg v m;
   Fpu_lastDataPtr_loc -> set_fpu_lastDataPtr_reg v m;
   Fpu_lastOpcode_loc -> set_lastOpcode_reg v m}

array_sub :: Nat -> Nat -> Array -> Int0 -> Mach_state -> Int0
array_sub l s a i m =
  case a of {
   Fpu_datareg -> look (fpu_data_regs (fpu m)) i;
   Fpu_tag -> look (fpu_tags (fpu m)) i}

set_fpu_datareg :: Int3 -> Int80 -> Mach -> Mach
set_fpu_datareg r v m =
  Build_mach (core m) (Build_fpu_state
    (upd (eq_dec2 size3) (fpu_data_regs (fpu m)) r v) (fpu_status (fpu m))
    (fpu_control (fpu m)) (fpu_tags (fpu m)) (fpu_lastInstrPtr (fpu m))
    (fpu_lastDataPtr (fpu m)) (fpu_lastOpcode (fpu m)))

set_fpu_tags_reg :: Int -> Int2 -> Mach -> Mach
set_fpu_tags_reg r v m =
  Build_mach (core m) (Build_fpu_state (fpu_data_regs (fpu m))
    (fpu_status (fpu m)) (fpu_control (fpu m))
    (upd (eq_dec2 size3) (fpu_tags (fpu m)) r v) (fpu_lastInstrPtr (fpu m))
    (fpu_lastDataPtr (fpu m)) (fpu_lastOpcode (fpu m)))

array_upd :: Nat -> Nat -> Array -> Int0 -> Int0 -> Mach -> Mach_state
array_upd l s a i v m =
  case a of {
   Fpu_datareg -> set_fpu_datareg i v m;
   Fpu_tag -> set_fpu_tags_reg i v m}

type T5 = Int0

index0 :: Int0 -> Positive
index0 i =
  index (unsigned size_addr i)

eq3 :: Int -> Int -> Sumbool
eq3 =
  eq_dec2 size_addr

type Elt1 = T5

elt_eq1 :: T5 -> T5 -> Sumbool
elt_eq1 =
  eq3

type T6 x = T3 x

eq4 :: (a1 -> a1 -> Sumbool) -> (T6 a1) -> (T6 a1) -> Sumbool
eq4 x a b =
  eq1 x a b

init0 :: a1 -> Prod a1 (T2 a1)
init0 x =
  init x

get1 :: T5 -> (T6 a1) -> a1
get1 i m =
  get0 (index0 i) m

set1 :: T5 -> a1 -> (T6 a1) -> Prod a1 (T2 a1)
set1 i v m =
  set0 (index0 i) v m

map2 :: (a1 -> a2) -> (T6 a1) -> T6 a2
map2 f m =
  map1 f m

data Bit_vector_op =
   Add_op
 | Sub_op
 | Mul_op
 | Divs_op
 | Divu_op
 | Modu_op
 | Mods_op
 | And_op
 | Or_op
 | Xor_op
 | Shl_op
 | Shr_op
 | Shru_op
 | Ror_op
 | Rol_op

bit_vector_op_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
                      a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> Bit_vector_op -> a1
bit_vector_op_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 b =
  case b of {
   Add_op -> f;
   Sub_op -> f0;
   Mul_op -> f1;
   Divs_op -> f2;
   Divu_op -> f3;
   Modu_op -> f4;
   Mods_op -> f5;
   And_op -> f6;
   Or_op -> f7;
   Xor_op -> f8;
   Shl_op -> f9;
   Shr_op -> f10;
   Shru_op -> f11;
   Ror_op -> f12;
   Rol_op -> f13}

bit_vector_op_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
                     -> a1 -> a1 -> a1 -> a1 -> a1 -> Bit_vector_op -> a1
bit_vector_op_rec =
  bit_vector_op_rect

data Float_arith_op =
   Fadd_op
 | Fsub_op
 | Fmul_op
 | Fdiv_op

float_arith_op_rect :: a1 -> a1 -> a1 -> a1 -> Float_arith_op -> a1
float_arith_op_rect f f0 f1 f2 f3 =
  case f3 of {
   Fadd_op -> f;
   Fsub_op -> f0;
   Fmul_op -> f1;
   Fdiv_op -> f2}

float_arith_op_rec :: a1 -> a1 -> a1 -> a1 -> Float_arith_op -> a1
float_arith_op_rec =
  float_arith_op_rect

data Test_op =
   Eq_op
 | Lt_op
 | Ltu_op

test_op_rect :: a1 -> a1 -> a1 -> Test_op -> a1
test_op_rect f f0 f1 t =
  case t of {
   Eq_op -> f;
   Lt_op -> f0;
   Ltu_op -> f1}

test_op_rec :: a1 -> a1 -> a1 -> Test_op -> a1
test_op_rec =
  test_op_rect

type Rounding_mode = Mode

data Rtl_exp =
   Arith_rtl_exp Nat Bit_vector_op Rtl_exp Rtl_exp
 | Test_rtl_exp Nat Test_op Rtl_exp Rtl_exp
 | If_rtl_exp Nat Rtl_exp Rtl_exp Rtl_exp
 | Cast_s_rtl_exp Nat Nat Rtl_exp
 | Cast_u_rtl_exp Nat Nat Rtl_exp
 | Imm_rtl_exp Nat Int0
 | Get_loc_rtl_exp Nat Location0
 | Get_array_rtl_exp Nat Nat Array Rtl_exp
 | Get_byte_rtl_exp Rtl_exp
 | Get_random_rtl_exp Nat
 | Farith_rtl_exp Positive Positive Float_arith_op Rtl_exp Rtl_exp Rtl_exp
 | Fcast_rtl_exp Positive Positive Positive Positive Rtl_exp Rtl_exp

rtl_exp_rect :: (Nat -> Bit_vector_op -> Rtl_exp -> a1 -> Rtl_exp -> a1 ->
                a1) -> (Nat -> Test_op -> Rtl_exp -> a1 -> Rtl_exp -> a1 ->
                a1) -> (Nat -> Rtl_exp -> a1 -> Rtl_exp -> a1 -> Rtl_exp ->
                a1 -> a1) -> (Nat -> Nat -> Rtl_exp -> a1 -> a1) -> (Nat ->
                Nat -> Rtl_exp -> a1 -> a1) -> (Nat -> Int0 -> a1) -> (Nat ->
                Location0 -> a1) -> (Nat -> Nat -> Array -> Rtl_exp -> a1 ->
                a1) -> (Rtl_exp -> a1 -> a1) -> (Nat -> a1) -> (Positive ->
                Positive -> () -> Float_arith_op -> Rtl_exp -> a1 -> Rtl_exp
                -> a1 -> Rtl_exp -> a1 -> a1) -> (Positive -> Positive ->
                Positive -> Positive -> () -> () -> Rtl_exp -> a1 -> Rtl_exp
                -> a1 -> a1) -> Nat -> Rtl_exp -> a1
rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 n r =
  case r of {
   Arith_rtl_exp s b e1 e2 ->
    f s b e1 (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e1) e2
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e2);
   Test_rtl_exp s top e1 e2 ->
    f0 s top e1 (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e1) e2
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e2);
   If_rtl_exp s cond e1 e2 ->
    f1 s cond (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size1 cond)
      e1 (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e1) e2
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s e2);
   Cast_s_rtl_exp s1 s2 e ->
    f2 s1 s2 e (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s1 e);
   Cast_u_rtl_exp s1 s2 e ->
    f3 s1 s2 e (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 s1 e);
   Imm_rtl_exp s i -> f4 s i;
   Get_loc_rtl_exp s l -> f5 s l;
   Get_array_rtl_exp l s a r2 ->
    f6 l s a r2 (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 l r2);
   Get_byte_rtl_exp addr ->
    f7 addr (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size_addr addr);
   Get_random_rtl_exp s -> f8 s;
   Farith_rtl_exp ew mw fop rounding x x0 ->
    let {len = plus (to_nat ew) (to_nat mw)} in
    f9 ew mw __ fop rounding
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size2 rounding) x
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 len x) x0
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 len x0);
   Fcast_rtl_exp ew1 mw1 ew2 mw2 rounding r2 ->
    f10 ew1 mw1 ew2 mw2 __ __ rounding
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 size2 rounding) r2
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
        (plus (to_nat ew1) (to_nat mw1)) r2)}

rtl_exp_rec :: (Nat -> Bit_vector_op -> Rtl_exp -> a1 -> Rtl_exp -> a1 -> a1)
               -> (Nat -> Test_op -> Rtl_exp -> a1 -> Rtl_exp -> a1 -> a1) ->
               (Nat -> Rtl_exp -> a1 -> Rtl_exp -> a1 -> Rtl_exp -> a1 -> a1)
               -> (Nat -> Nat -> Rtl_exp -> a1 -> a1) -> (Nat -> Nat ->
               Rtl_exp -> a1 -> a1) -> (Nat -> Int0 -> a1) -> (Nat ->
               Location0 -> a1) -> (Nat -> Nat -> Array -> Rtl_exp -> a1 ->
               a1) -> (Rtl_exp -> a1 -> a1) -> (Nat -> a1) -> (Positive ->
               Positive -> () -> Float_arith_op -> Rtl_exp -> a1 -> Rtl_exp
               -> a1 -> Rtl_exp -> a1 -> a1) -> (Positive -> Positive ->
               Positive -> Positive -> () -> () -> Rtl_exp -> a1 -> Rtl_exp
               -> a1 -> a1) -> Nat -> Rtl_exp -> a1
rtl_exp_rec =
  rtl_exp_rect

data Rtl_instr =
   Set_loc_rtl Nat Rtl_exp Location0
 | Set_array_rtl Nat Nat Array Rtl_exp Rtl_exp
 | Set_byte_rtl Rtl_exp Rtl_exp
 | Advance_oracle_rtl
 | If_rtl Rtl_exp Rtl_instr
 | Error_rtl
 | Trap_rtl

rtl_instr_rect :: (Nat -> Rtl_exp -> Location0 -> a1) -> (Nat -> Nat -> Array
                  -> Rtl_exp -> Rtl_exp -> a1) -> (Rtl_exp -> Rtl_exp -> a1)
                  -> a1 -> (Rtl_exp -> Rtl_instr -> a1 -> a1) -> a1 -> a1 ->
                  Rtl_instr -> a1
rtl_instr_rect f f0 f1 f2 f3 f4 f5 r =
  case r of {
   Set_loc_rtl s e l -> f s e l;
   Set_array_rtl l s a r2 r3 -> f0 l s a r2 r3;
   Set_byte_rtl e addr -> f1 e addr;
   Advance_oracle_rtl -> f2;
   If_rtl r2 r3 -> f3 r2 r3 (rtl_instr_rect f f0 f1 f2 f3 f4 f5 r3);
   Error_rtl -> f4;
   Trap_rtl -> f5}

rtl_instr_rec :: (Nat -> Rtl_exp -> Location0 -> a1) -> (Nat -> Nat -> Array
                 -> Rtl_exp -> Rtl_exp -> a1) -> (Rtl_exp -> Rtl_exp -> a1)
                 -> a1 -> (Rtl_exp -> Rtl_instr -> a1 -> a1) -> a1 -> a1 ->
                 Rtl_instr -> a1
rtl_instr_rec =
  rtl_instr_rect

data Oracle =
   Build_oracle (Nat -> Z -> Int0) Z

oracle_rect :: ((Nat -> Z -> Int0) -> Z -> a1) -> Oracle -> a1
oracle_rect f o =
  case o of {
   Build_oracle x x0 -> f x x0}

oracle_rec :: ((Nat -> Z -> Int0) -> Z -> a1) -> Oracle -> a1
oracle_rec =
  oracle_rect

oracle_bits :: Oracle -> Nat -> Z -> Int0
oracle_bits o =
  case o of {
   Build_oracle oracle_bits0 oracle_offset0 -> oracle_bits0}

oracle_offset :: Oracle -> Z
oracle_offset o =
  case o of {
   Build_oracle oracle_bits0 oracle_offset0 -> oracle_offset0}

data Rtl_state =
   Build_rtl_state Oracle Mach_state (T6 Int8)

rtl_state_rect :: (Oracle -> Mach_state -> (T6 Int8) -> a1) -> Rtl_state ->
                  a1
rtl_state_rect f r =
  case r of {
   Build_rtl_state x x0 x1 -> f x x0 x1}

rtl_state_rec :: (Oracle -> Mach_state -> (T6 Int8) -> a1) -> Rtl_state -> a1
rtl_state_rec =
  rtl_state_rect

rtl_oracle :: Rtl_state -> Oracle
rtl_oracle r =
  case r of {
   Build_rtl_state rtl_oracle0 rtl_mach_state0 rtl_memory0 -> rtl_oracle0}

rtl_mach_state :: Rtl_state -> Mach_state
rtl_mach_state r =
  case r of {
   Build_rtl_state rtl_oracle0 rtl_mach_state0 rtl_memory0 -> rtl_mach_state0}

rtl_memory :: Rtl_state -> T6 Int8
rtl_memory r =
  case r of {
   Build_rtl_state rtl_oracle0 rtl_mach_state0 rtl_memory0 -> rtl_memory0}

data RTL_ans a =
   Fail_ans
 | Trap_ans
 | Okay_ans a
 deriving (Prelude.Show) 

rTL_ans_rect :: a2 -> a2 -> (a1 -> a2) -> (RTL_ans a1) -> a2
rTL_ans_rect f f0 f1 r =
  case r of {
   Fail_ans -> f;
   Trap_ans -> f0;
   Okay_ans x -> f1 x}

rTL_ans_rec :: a2 -> a2 -> (a1 -> a2) -> (RTL_ans a1) -> a2
rTL_ans_rec =
  rTL_ans_rect

type RTL t = Rtl_state -> Prod (RTL_ans t) Rtl_state

rTL_monad :: Monad (RTL ())
rTL_monad =
  Build_Monad (\_ x rs -> Pair (Okay_ans x) rs) (\_ _ c f rs ->
    case c rs of {
     Pair r rs' ->
      case r of {
       Okay_ans v -> f v rs';
       x -> Pair x rs'}})

fail :: RTL a1
fail rs =
  Pair Fail_ans rs

trap :: RTL a1
trap rs =
  Pair Trap_ans rs

set_loc :: Nat -> Location0 -> Int0 -> RTL Unit
set_loc s l v rs =
  Pair (Okay_ans Tt) (Build_rtl_state (rtl_oracle rs)
    (set_location s l v (rtl_mach_state rs)) (rtl_memory rs))

set_array :: Nat -> Nat -> Array -> Int0 -> Int0 -> RTL Unit
set_array l s a i v rs =
  Pair (Okay_ans Tt) (Build_rtl_state (rtl_oracle rs)
    (array_upd l s a i v (rtl_mach_state rs)) (rtl_memory rs))

set_byte :: Int0 -> Int0 -> RTL Unit
set_byte addr v rs =
  Pair (Okay_ans Tt) (Build_rtl_state (rtl_oracle rs) (rtl_mach_state rs)
    (set1 addr v (rtl_memory rs)))

advance_oracle :: RTL Unit
advance_oracle rs =
  let {o = rtl_oracle rs} in
  let {o' = Build_oracle (oracle_bits o) (add1 (oracle_offset o) (Zpos XH))}
  in
  Pair (Okay_ans Tt) (Build_rtl_state o' (rtl_mach_state rs) (rtl_memory rs))

interp_arith :: Nat -> Bit_vector_op -> Int0 -> Int0 -> Int0
interp_arith s b v1 v2 =
  case b of {
   Add_op -> add2 s v1 v2;
   Sub_op -> sub2 s v1 v2;
   Mul_op -> mul2 s v1 v2;
   Divs_op -> divs s v1 v2;
   Divu_op -> divu s v1 v2;
   Modu_op -> modu s v1 v2;
   Mods_op -> mods s v1 v2;
   And_op -> and s v1 v2;
   Or_op -> or s v1 v2;
   Xor_op -> xor s v1 v2;
   Shl_op -> shl s v1 v2;
   Shr_op -> shr s v1 v2;
   Shru_op -> shru s v1 v2;
   Ror_op -> ror s v1 v2;
   Rol_op -> rol s v1 v2}

interp_test :: Nat -> Test_op -> Int0 -> Int0 -> Int0
interp_test s t v1 v2 =
  case case t of {
        Eq_op -> eq s v1 v2;
        Lt_op -> lt s v1 v2;
        Ltu_op -> ltu s v1 v2} of {
   True -> one1 size1;
   False -> zero1 size1}

dec_rounding_mode :: Int0 -> Rounding_mode
dec_rounding_mode rm =
  case eq size2 rm (repr size2 Z0) of {
   True -> Mode_NE;
   False ->
    case eq size2 rm (repr size2 (Zpos XH)) of {
     True -> Mode_DN;
     False ->
      case eq size2 rm (repr size2 (Zpos (XO XH))) of {
       True -> Mode_UP;
       False -> Mode_ZR}}}

interp_farith :: Positive -> Positive -> Float_arith_op -> Int0 -> Int0 ->
                 Int0 -> Int0
interp_farith ew mw fop rm v1 v2 =
  let {prec = add1 (Zpos mw) (Zpos XH)} in
  let {emax = pow1 (Zpos (XO XH)) (sub1 (Zpos ew) (Zpos XH))} in
  let {bf_of_bits = binary_float_of_bits (Zpos mw) (Zpos ew)} in
  let {bf1 = bf_of_bits (unsigned (plus (to_nat ew) (to_nat mw)) v1)} in
  let {bf2 = bf_of_bits (unsigned (plus (to_nat ew) (to_nat mw)) v2)} in
  let {md = dec_rounding_mode rm} in
  let {
   res = case fop of {
          Fadd_op -> bplus prec emax md bf1 bf2;
          Fsub_op -> bminus prec emax md bf1 bf2;
          Fmul_op -> bmult prec emax md bf1 bf2;
          Fdiv_op -> bdiv prec emax md bf1 bf2}}
  in
  repr (plus (to_nat ew) (to_nat mw))
    (bits_of_binary_float (Zpos mw) (Zpos ew) res)

cond_Zopp0 :: Bool -> Z -> Z
cond_Zopp0 b m =
  case b of {
   True -> opp m;
   False -> m}

binary_float_cast :: Z -> Z -> Z -> Z -> Int0 -> Binary_float -> Binary_float
binary_float_cast prec1 emax1 prec2 emax2 rm bf =
  let {md = dec_rounding_mode rm} in
  case bf of {
   B754_finite sign mant ep ->
    binary_normalize prec2 emax2 md (cond_Zopp0 sign (Zpos mant)) ep True;
   x -> x}

interp_fcast :: Positive -> Positive -> Positive -> Positive -> Int0 -> Int0
                -> Int0
interp_fcast ew1 mw1 ew2 mw2 rm v =
  let {bf_of_bits = binary_float_of_bits (Zpos mw1) (Zpos ew1)} in
  let {bf = bf_of_bits (unsigned (plus (to_nat ew1) (to_nat mw1)) v)} in
  let {
   bf' = binary_float_cast (add1 (Zpos mw1) (Zpos XH))
           (pow1 (Zpos (XO XH)) (sub1 (Zpos ew1) (Zpos XH)))
           (add1 (Zpos mw2) (Zpos XH))
           (pow1 (Zpos (XO XH)) (sub1 (Zpos ew2) (Zpos XH))) rm bf}
  in
  repr (plus (to_nat ew2) (to_nat mw2))
    (bits_of_binary_float (Zpos mw2) (Zpos ew2) bf')

interp_rtl_exp :: Nat -> Rtl_exp -> Rtl_state -> Int0
interp_rtl_exp s e rs =
  case e of {
   Arith_rtl_exp s0 b e1 e2 ->
    let {v1 = interp_rtl_exp s0 e1 rs} in
    let {v2 = interp_rtl_exp s0 e2 rs} in interp_arith s0 b v1 v2;
   Test_rtl_exp s0 t e1 e2 ->
    let {v1 = interp_rtl_exp s0 e1 rs} in
    let {v2 = interp_rtl_exp s0 e2 rs} in interp_test s0 t v1 v2;
   If_rtl_exp s0 cd e1 e2 ->
    let {v = interp_rtl_exp size1 cd rs} in
    case eq size1 v (one1 size1) of {
     True -> interp_rtl_exp s0 e1 rs;
     False -> interp_rtl_exp s0 e2 rs};
   Cast_s_rtl_exp s1 s2 e0 ->
    let {v = interp_rtl_exp s1 e0 rs} in repr s2 (signed s1 v);
   Cast_u_rtl_exp s1 s2 e0 ->
    let {v = interp_rtl_exp s1 e0 rs} in repr s2 (unsigned s1 v);
   Imm_rtl_exp s0 v -> v;
   Get_loc_rtl_exp s0 l -> get_location s0 l (rtl_mach_state rs);
   Get_array_rtl_exp l s0 a e0 ->
    let {i = interp_rtl_exp l e0 rs} in
    array_sub l s0 a i (rtl_mach_state rs);
   Get_byte_rtl_exp addr ->
    let {v = interp_rtl_exp size_addr addr rs} in get1 v (rtl_memory rs);
   Get_random_rtl_exp s0 ->
    let {oracle = rtl_oracle rs} in
    oracle_bits oracle s0 (oracle_offset oracle);
   Farith_rtl_exp ew mw fop rm x x0 ->
    let {len = plus (to_nat ew) (to_nat mw)} in
    let {v1 = interp_rtl_exp len x rs} in
    let {v2 = interp_rtl_exp len x0 rs} in
    let {vrm = interp_rtl_exp size2 rm rs} in
    interp_farith ew mw fop vrm v1 v2;
   Fcast_rtl_exp ew1 mw1 ew2 mw2 rm e0 ->
    let {v = interp_rtl_exp (plus (to_nat ew1) (to_nat mw1)) e0 rs} in
    let {vrm = interp_rtl_exp size2 rm rs} in
    interp_fcast ew1 mw1 ew2 mw2 vrm v}

interp_rtl_exp_comp :: Nat -> Rtl_exp -> RTL Int0
interp_rtl_exp_comp s e rs =
  Pair (Okay_ans (interp_rtl_exp s e rs)) rs

get_loc :: Nat -> Location0 -> RTL Int0
get_loc s l =
  interp_rtl_exp_comp s (Get_loc_rtl_exp s l)

get_array :: Nat -> Nat -> Array -> Int0 -> RTL Int0
get_array l s a i =
  interp_rtl_exp_comp s (Get_array_rtl_exp l s a (Imm_rtl_exp l i))

get_byte :: Int0 -> RTL Int0
get_byte addr =
  interp_rtl_exp_comp size8 (Get_byte_rtl_exp (Imm_rtl_exp size_addr addr))

get_random :: Nat -> RTL Int0
get_random s =
  interp_rtl_exp_comp s (Get_random_rtl_exp s)

interp_rtl :: Rtl_instr -> RTL Unit
interp_rtl instr =
  case instr of {
   Set_loc_rtl s e l ->
    bind (unsafeCoerce rTL_monad) (unsafeCoerce (interp_rtl_exp_comp s e))
      (\v -> set_loc s l v);
   Set_array_rtl l s a e1 e2 ->
    bind (unsafeCoerce rTL_monad) (unsafeCoerce (interp_rtl_exp_comp l e1))
      (\i ->
      bind (unsafeCoerce rTL_monad) (unsafeCoerce (interp_rtl_exp_comp s e2))
        (\v -> set_array l s a i v));
   Set_byte_rtl e addr ->
    bind (unsafeCoerce rTL_monad)
      (unsafeCoerce (interp_rtl_exp_comp size8 e)) (\v ->
      bind (unsafeCoerce rTL_monad)
        (unsafeCoerce (interp_rtl_exp_comp size_addr addr)) (\a ->
        set_byte a v));
   Advance_oracle_rtl -> advance_oracle;
   If_rtl r i ->
    bind (unsafeCoerce rTL_monad)
      (unsafeCoerce (interp_rtl_exp_comp size1 r)) (\v ->
      case eq size1 v (one1 size1) of {
       True -> interp_rtl i;
       False -> return (unsafeCoerce rTL_monad) Tt});
   Error_rtl -> fail;
   Trap_rtl -> trap}

data Instruction =
   Build_instruction String (List Rtl_instr)

instruction_rect :: (String -> (List Rtl_instr) -> a1) -> Instruction -> a1
instruction_rect f i =
  case i of {
   Build_instruction x x0 -> f x x0}

instruction_rec :: (String -> (List Rtl_instr) -> a1) -> Instruction -> a1
instruction_rec =
  instruction_rect

instr_assembly :: Instruction -> String
instr_assembly i =
  case i of {
   Build_instruction instr_assembly0 instr_rtl0 -> instr_assembly0}

instr_rtl :: Instruction -> List Rtl_instr
instr_rtl i =
  case i of {
   Build_instruction instr_assembly0 instr_rtl0 -> instr_rtl0}

type Conv_state =
  List Rtl_instr
  -- singleton inductive, whose constructor was Build_conv_state
  
conv_state_rect :: ((List Rtl_instr) -> a1) -> Conv_state -> a1
conv_state_rect f c =
  f c

conv_state_rec :: ((List Rtl_instr) -> a1) -> Conv_state -> a1
conv_state_rec =
  conv_state_rect

c_rev_i :: Conv_state -> List Rtl_instr
c_rev_i c =
  c

type Conv t = Conv_state -> Prod t Conv_state

conv_monad :: Monad (Conv ())
conv_monad =
  Build_Monad (\_ x s -> Pair x s) (\_ _ c f s ->
    case c s of {
     Pair v s' -> f v s'})

runConv :: (Conv Unit) -> List Rtl_instr
runConv c =
  case c Nil of {
   Pair u c' -> rev (c_rev_i c')}

eMIT :: Rtl_instr -> Conv Unit
eMIT i s =
  Pair Tt (Cons i (c_rev_i s))

raise_error :: Conv Unit
raise_error =
  eMIT Error_rtl

raise_trap :: Conv Unit
raise_trap =
  eMIT Trap_rtl

no_op :: Conv Unit
no_op =
  return (unsafeCoerce conv_monad) Tt

load_int :: Nat -> Int0 -> Conv Rtl_exp
load_int s i =
  return (unsafeCoerce conv_monad) (Imm_rtl_exp s i)

arith :: Nat -> Bit_vector_op -> Rtl_exp -> Rtl_exp -> Conv Rtl_exp
arith s b e1 e2 =
  return (unsafeCoerce conv_monad) (Arith_rtl_exp s b e1 e2)

test :: Nat -> Test_op -> Rtl_exp -> Rtl_exp -> Conv Rtl_exp
test s t e1 e2 =
  return (unsafeCoerce conv_monad) (Test_rtl_exp s t e1 e2)

cast_u :: Nat -> Nat -> Rtl_exp -> Conv Rtl_exp
cast_u s1 s2 e =
  return (unsafeCoerce conv_monad) (Cast_u_rtl_exp s1 s2 e)

cast_s :: Nat -> Nat -> Rtl_exp -> Conv Rtl_exp
cast_s s1 s2 e =
  return (unsafeCoerce conv_monad) (Cast_s_rtl_exp s1 s2 e)

read_loc :: Nat -> Loc -> Conv Rtl_exp
read_loc s l =
  return (unsafeCoerce conv_monad) (Get_loc_rtl_exp s l)

write_loc :: Nat -> Rtl_exp -> Loc -> Conv Unit
write_loc s e l =
  eMIT (Set_loc_rtl s e l)

read_array :: Nat -> Nat -> Array -> Rtl_exp -> Conv Rtl_exp
read_array l s a idx =
  return (unsafeCoerce conv_monad) (Get_array_rtl_exp l s a idx)

write_array :: Nat -> Nat -> Array -> Rtl_exp -> Rtl_exp -> Conv Unit
write_array l s a idx v =
  eMIT (Set_array_rtl l s a idx v)

read_byte :: Rtl_exp -> Conv Rtl_exp
read_byte a =
  return (unsafeCoerce conv_monad) (Get_byte_rtl_exp a)

write_byte :: Rtl_exp -> Rtl_exp -> Conv Unit
write_byte v a =
  eMIT (Set_byte_rtl v a)

if_exp :: Nat -> Rtl_exp -> Rtl_exp -> Rtl_exp -> Conv Rtl_exp
if_exp s g e1 e2 =
  return (unsafeCoerce conv_monad) (If_rtl_exp s g e1 e2)

if_trap :: Rtl_exp -> Conv Unit
if_trap g =
  eMIT (If_rtl g Trap_rtl)

if_set_loc :: Rtl_exp -> Nat -> Rtl_exp -> Location0 -> Conv Unit
if_set_loc cond s e l =
  eMIT (If_rtl cond (Set_loc_rtl s e l))

choose :: Nat -> Conv Rtl_exp
choose s =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (eMIT Advance_oracle_rtl))
    (\x -> return (unsafeCoerce conv_monad) (Get_random_rtl_exp s))

fcast :: Positive -> Positive -> Positive -> Positive -> Rtl_exp -> Rtl_exp
         -> Conv Rtl_exp
fcast ew1 mw1 ew2 mw2 rm e =
  return (unsafeCoerce conv_monad) (Fcast_rtl_exp ew1 mw1 ew2 mw2 rm e)

farith_float79 :: Float_arith_op -> Rtl_exp -> Rtl_exp -> Rtl_exp -> Conv
                  Rtl_exp
farith_float79 op rm e1 e2 =
  return (unsafeCoerce conv_monad) (Farith_rtl_exp (XI (XI (XI XH))) (XI (XI
    (XI (XI (XI XH))))) op rm e1 e2)

load_Z :: Nat -> Z -> Conv Rtl_exp
load_Z s z =
  load_int s (repr s z)

load_reg :: Register -> Conv Rtl_exp
load_reg r =
  read_loc size32 (Reg_loc r)

set_reg :: Rtl_exp -> Register -> Conv Unit
set_reg p r =
  write_loc size32 p (Reg_loc r)

get_seg_start :: Segment_register -> Conv Rtl_exp
get_seg_start s =
  read_loc size32 (Seg_reg_start_loc s)

get_seg_limit :: Segment_register -> Conv Rtl_exp
get_seg_limit s =
  read_loc size32 (Seg_reg_limit_loc s)

get_flag :: Flag -> Conv Rtl_exp
get_flag fl =
  read_loc size1 (Flag_loc fl)

set_flag :: Flag -> Rtl_exp -> Conv Unit
set_flag fl r =
  write_loc size1 r (Flag_loc fl)

get_pc :: Conv Rtl_exp
get_pc =
  read_loc size32 Pc_loc

set_pc0 :: Rtl_exp -> Conv Unit
set_pc0 v =
  write_loc size32 v Pc_loc

not0 :: Nat -> Rtl_exp -> Conv Rtl_exp
not0 s p =
  bind (unsafeCoerce conv_monad) (load_Z s (max_unsigned s)) (\mask ->
    arith s Xor_op p mask)

undef_flag :: Flag -> Conv Unit
undef_flag f =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (choose size1)) (\v ->
    set_flag f v)

first_bits :: Nat -> Nat -> Rtl_exp -> Conv Rtl_exp
first_bits s1 s2 x =
  bind (unsafeCoerce conv_monad) (load_Z s2 (of_nat1 (minus s2 s1))) (\c ->
    bind (unsafeCoerce conv_monad) (arith s2 Shru_op x c) (\r ->
      cast_u s2 s1 r))

last_bits :: Nat -> Nat -> Rtl_exp -> Conv Rtl_exp
last_bits s1 s2 x =
  bind (unsafeCoerce conv_monad) (load_Z s2 (two_power_nat (plus s1 (S O))))
    (\c ->
    bind (unsafeCoerce conv_monad) (arith s2 Modu_op x c) (\r ->
      cast_u s2 s1 r))

concat_bits :: Nat -> Nat -> Rtl_exp -> Rtl_exp -> Conv Rtl_exp
concat_bits s1 s2 x y =
  bind (unsafeCoerce conv_monad) (cast_u s1 (plus (plus s1 s2) (S O)) x)
    (\x' ->
    bind (unsafeCoerce conv_monad)
      (load_Z (plus (plus s1 s2) (S O)) (of_nat1 (plus s2 (S O)))) (\c ->
      bind (unsafeCoerce conv_monad)
        (arith (plus (plus s1 s2) (S O)) Shl_op x' c) (\raised_x ->
        bind (unsafeCoerce conv_monad)
          (cast_u s2 (plus (plus s1 s2) (S O)) y) (\y' ->
          arith (plus (plus s1 s2) (S O)) Add_op raised_x y'))))

copy_ps :: Nat -> Rtl_exp -> Conv Rtl_exp
copy_ps s rs =
  cast_u s s rs

scale_to_int32 :: Scale -> Int32
scale_to_int32 s =
  repr (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
    (case s of {
      Scale1 -> Zpos XH;
      Scale2 -> Zpos (XO XH);
      Scale4 -> Zpos (XO (XO XH));
      Scale8 -> Zpos (XO (XO (XO XH)))})

compute_addr :: Address -> Conv Rtl_exp
compute_addr a =
  let {disp = addrDisp a} in
  case addrBase a of {
   Some r2 ->
    case addrIndex a of {
     Some p ->
      case p of {
       Pair s r3 ->
        bind (unsafeCoerce conv_monad) (load_reg r2) (\b ->
          bind (unsafeCoerce conv_monad) (load_reg r3) (\i ->
            bind (unsafeCoerce conv_monad)
              (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S
                O))))))))))))))))))))))))))))))) (scale_to_int32 s)) (\s0 ->
              bind (unsafeCoerce conv_monad) (arith size32 Mul_op i s0)
                (\p0 ->
                bind (unsafeCoerce conv_monad) (arith size32 Add_op b p0)
                  (\p1 ->
                  bind (unsafeCoerce conv_monad)
                    (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      O))))))))))))))))))))))))))))))) disp) (\disp0 ->
                    arith size32 Add_op p1 disp0))))))};
     None ->
      bind (unsafeCoerce conv_monad) (load_reg r2) (\p1 ->
        bind (unsafeCoerce conv_monad)
          (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))) disp) (\p2 ->
          arith size32 Add_op p1 p2))};
   None ->
    case addrIndex a of {
     Some p ->
      case p of {
       Pair s r ->
        bind (unsafeCoerce conv_monad) (load_reg r) (\i ->
          bind (unsafeCoerce conv_monad)
            (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))) (scale_to_int32 s)) (\s0 ->
            bind (unsafeCoerce conv_monad)
              (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S
                O))))))))))))))))))))))))))))))) disp) (\disp0 ->
              bind (unsafeCoerce conv_monad) (arith size32 Mul_op i s0)
                (\p0 ->
                arith (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S
                  O))))))))))))))))))))))))))))))) Add_op disp0 p0))))};
     None ->
      load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) disp}}

add_and_check_segment :: Segment_register -> Rtl_exp -> Conv Rtl_exp
add_and_check_segment seg a =
  bind (unsafeCoerce conv_monad) (get_seg_start seg) (\start ->
    bind (unsafeCoerce conv_monad) (get_seg_limit seg) (\limit ->
      bind (unsafeCoerce conv_monad) (test size32 Ltu_op limit a) (\guard ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce (if_trap guard)) (\x ->
          arith size32 Add_op start a))))

lmem :: Segment_register -> Rtl_exp -> Conv Rtl_exp
lmem seg a =
  bind (unsafeCoerce conv_monad) (add_and_check_segment seg a) (\p ->
    read_byte p)

smem :: Segment_register -> Rtl_exp -> Rtl_exp -> Conv Unit
smem seg v a =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (add_and_check_segment seg a))
    (\p -> write_byte v p)

load_mem_n :: Segment_register -> Rtl_exp -> Nat -> Conv Rtl_exp
load_mem_n seg addr nbytes_minus_one =
  case nbytes_minus_one of {
   O -> lmem seg addr;
   S n ->
    bind (unsafeCoerce conv_monad) (load_mem_n seg addr n) (\rec ->
      bind (unsafeCoerce conv_monad) (load_Z size32 (of_nat1 (S n)))
        (\count ->
        bind (unsafeCoerce conv_monad) (arith size32 Add_op addr count)
          (\p3 ->
          bind (unsafeCoerce conv_monad) (lmem seg p3) (\nb ->
            bind (unsafeCoerce conv_monad)
              (cast_u
                (minus
                  (mult (plus n (S O)) (S (S (S (S (S (S (S (S O))))))))) (S
                  O))
                (minus
                  (mult (plus nbytes_minus_one (S O)) (S (S (S (S (S (S (S (S
                    O))))))))) (S O)) rec) (\p5 ->
              bind (unsafeCoerce conv_monad)
                (cast_u size8
                  (minus
                    (mult (plus nbytes_minus_one (S O)) (S (S (S (S (S (S (S
                      (S O))))))))) (S O)) nb) (\p6 ->
                bind (unsafeCoerce conv_monad)
                  (load_Z
                    (minus
                      (mult (plus nbytes_minus_one (S O)) (S (S (S (S (S (S
                        (S (S O))))))))) (S O))
                    (mul1 (of_nat1 (S n)) (Zpos (XO (XO (XO XH)))))) (\p7 ->
                  bind (unsafeCoerce conv_monad)
                    (arith
                      (minus
                        (mult (plus nbytes_minus_one (S O)) (S (S (S (S (S (S
                          (S (S O))))))))) (S O)) Shl_op p6 p7) (\p8 ->
                    arith
                      (minus
                        (mult (plus (S n) (S O)) (S (S (S (S (S (S (S (S
                          O))))))))) (S O)) Or_op
                      (eq_rect
                        (minus
                          (mult (plus nbytes_minus_one (S O)) (S (S (S (S (S
                            (S (S (S O))))))))) (S O)) p5
                        (minus
                          (mult (plus (S n) (S O)) (S (S (S (S (S (S (S (S
                            O))))))))) (S O)))
                      (eq_rect
                        (minus
                          (mult (plus nbytes_minus_one (S O)) (S (S (S (S (S
                            (S (S (S O))))))))) (S O)) p8
                        (minus
                          (mult (plus (S n) (S O)) (S (S (S (S (S (S (S (S
                            O))))))))) (S O)))))))))))}

load_mem80 :: Segment_register -> Rtl_exp -> Conv Rtl_exp
load_mem80 seg addr =
  load_mem_n seg addr (S (S (S (S (S (S (S (S (S O)))))))))

load_mem64 :: Segment_register -> Rtl_exp -> Conv Rtl_exp
load_mem64 seg addr =
  load_mem_n seg addr (S (S (S (S (S (S (S O)))))))

load_mem32 :: Segment_register -> Rtl_exp -> Conv Rtl_exp
load_mem32 seg addr =
  load_mem_n seg addr (S (S (S O)))

load_mem16 :: Segment_register -> Rtl_exp -> Conv Rtl_exp
load_mem16 seg addr =
  load_mem_n seg addr (S O)

load_mem8 :: Segment_register -> Rtl_exp -> Conv Rtl_exp
load_mem8 seg addr =
  load_mem_n seg addr O

opsize :: Bool -> Bool -> Nat
opsize override w =
  case override of {
   True ->
    case w of {
     True -> size16;
     False -> size8};
   False ->
    case w of {
     True -> size32;
     False -> size8}}

load_mem :: Prefix -> Bool -> Segment_register -> Rtl_exp -> Conv Rtl_exp
load_mem p w seg op =
  case op_override p of {
   True ->
    case w of {
     True -> load_mem16 seg op;
     False -> load_mem8 seg op};
   False ->
    case w of {
     True -> load_mem32 seg op;
     False -> load_mem8 seg op}}

iload_op32 :: Segment_register -> Operand -> Conv Rtl_exp
iload_op32 seg op =
  case op of {
   Imm_op i ->
    load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i;
   Reg_op r -> load_reg r;
   Address_op a ->
    bind (unsafeCoerce conv_monad) (compute_addr a) (\p1 ->
      load_mem32 seg p1);
   Offset_op off ->
    bind (unsafeCoerce conv_monad)
      (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
        off) (\p1 -> load_mem32 seg p1)}

iload_op16 :: Segment_register -> Operand -> Conv Rtl_exp
iload_op16 seg op =
  case op of {
   Imm_op i ->
    bind (unsafeCoerce conv_monad)
      (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i)
      (\tmp ->
      cast_u (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) size16
        tmp);
   Reg_op r ->
    bind (unsafeCoerce conv_monad) (load_reg r) (\tmp ->
      cast_u size32 size16 tmp);
   Address_op a ->
    bind (unsafeCoerce conv_monad) (compute_addr a) (\p1 ->
      load_mem16 seg p1);
   Offset_op off ->
    bind (unsafeCoerce conv_monad)
      (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
        off) (\p1 -> load_mem16 seg p1)}

iload_op8 :: Segment_register -> Operand -> Conv Rtl_exp
iload_op8 seg op =
  case op of {
   Imm_op i ->
    bind (unsafeCoerce conv_monad)
      (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i)
      (\tmp ->
      cast_u (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) size8
        tmp);
   Reg_op r ->
    bind (unsafeCoerce conv_monad)
      (load_reg
        (case r of {
          ESP -> EAX;
          EBP -> ECX;
          ESI -> EDX;
          EDI -> EBX;
          x -> x})) (\tmp ->
      case r of {
       EAX -> cast_u size32 size8 tmp;
       ECX -> cast_u size32 size8 tmp;
       EDX -> cast_u size32 size8 tmp;
       EBX -> cast_u size32 size8 tmp;
       _ ->
        bind (unsafeCoerce conv_monad)
          (load_Z size32 (Zpos (XO (XO (XO XH))))) (\eight ->
          bind (unsafeCoerce conv_monad) (arith size32 Shru_op tmp eight)
            (\tmp2 -> cast_u size32 size8 tmp2))});
   Address_op a ->
    bind (unsafeCoerce conv_monad) (compute_addr a) (\p1 -> load_mem8 seg p1);
   Offset_op off ->
    bind (unsafeCoerce conv_monad)
      (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
        off) (\p1 -> load_mem8 seg p1)}

set_mem_n :: Nat -> Segment_register -> Rtl_exp -> Rtl_exp -> Conv Unit
set_mem_n t seg v addr =
  case t of {
   O ->
    smem seg
      (eq_rect
        (minus (mult (S (S (S (S (S (S (S (S O)))))))) (plus t (S O))) (S O))
        v size8) addr;
   S u ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce
        (cast_u
          (minus (mult (S (S (S (S (S (S (S (S O)))))))) (plus t (S O))) (S
            O))
          (minus (mult (S (S (S (S (S (S (S (S O)))))))) (plus u (S O))) (S
            O)) v)) (\p1 ->
      bind (unsafeCoerce conv_monad) (set_mem_n u seg p1 addr) (\x ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce
            (load_Z
              (minus (mult (S (S (S (S (S (S (S (S O)))))))) (plus t (S O)))
                (S O))
              (of_nat1 (mult (S u) (S (S (S (S (S (S (S (S O))))))))))))
          (\p2 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce
              (arith
                (minus
                  (mult (S (S (S (S (S (S (S (S O)))))))) (plus t (S O))) (S
                  O)) Shru_op v p2)) (\p3 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce
                (cast_u
                  (minus
                    (mult (S (S (S (S (S (S (S (S O)))))))) (plus t (S O)))
                    (S O)) size8 p3)) (\p4 ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (load_Z size32 (of_nat1 (S u)))) (\p5 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (arith size32 Add_op p5 addr)) (\p6 ->
                  smem seg p4 p6)))))))}

set_mem80 :: Segment_register -> Rtl_exp -> Rtl_exp -> Conv Unit
set_mem80 seg v a =
  set_mem_n (S (S (S (S (S (S (S (S (S O))))))))) seg v a

set_mem64 :: Segment_register -> Rtl_exp -> Rtl_exp -> Conv Unit
set_mem64 seg v a =
  set_mem_n (S (S (S (S (S (S (S O))))))) seg v a

set_mem32 :: Segment_register -> Rtl_exp -> Rtl_exp -> Conv Unit
set_mem32 seg v a =
  set_mem_n (S (S (S O))) seg v a

set_mem16 :: Segment_register -> Rtl_exp -> Rtl_exp -> Conv Unit
set_mem16 seg v a =
  set_mem_n (S O) seg v a

set_mem8 :: Segment_register -> Rtl_exp -> Rtl_exp -> Conv Unit
set_mem8 seg v a =
  set_mem_n O seg v a

set_mem :: Prefix -> Bool -> Segment_register -> Rtl_exp -> Rtl_exp -> Conv
           Unit
set_mem p w seg =
  case op_override p of {
   True ->
    case w of {
     True -> set_mem16 seg;
     False -> set_mem8 seg};
   False ->
    case w of {
     True -> set_mem32 seg;
     False -> set_mem8 seg}}

iset_op80 :: Segment_register -> Rtl_exp -> Operand -> Conv Unit
iset_op80 seg p op =
  case op of {
   Imm_op i -> raise_error;
   Reg_op r ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (cast_u size80 size32 p))
      (\tmp -> set_reg tmp r);
   Address_op a ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a)) (\addr ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (cast_u size80 size32 p))
        (\tmp -> set_mem32 seg tmp addr));
   Offset_op off ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce
        (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
          off)) (\addr ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (cast_u size80 size32 p))
        (\tmp -> set_mem32 seg tmp addr))}

iset_op32 :: Segment_register -> Rtl_exp -> Operand -> Conv Unit
iset_op32 seg p op =
  case op of {
   Imm_op i -> raise_error;
   Reg_op r -> set_reg p r;
   Address_op a ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a)) (\addr ->
      set_mem32 seg p addr);
   Offset_op off ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce
        (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
          off)) (\addr -> set_mem32 seg p addr)}

iset_op16 :: Segment_register -> Rtl_exp -> Operand -> Conv Unit
iset_op16 seg p op =
  case op of {
   Imm_op i -> raise_error;
   Reg_op r ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg r)) (\tmp ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (load_int size32 (mone size32))) (\mask ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (load_Z size32 (Zpos (XO (XO (XO (XO XH)))))))
          (\sixteen ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (arith size32 Shl_op mask sixteen)) (\mask2 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (arith size32 And_op mask2 tmp)) (\tmp2 ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (cast_u size16 size32 p)) (\p32 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (arith size32 Or_op tmp2 p32)) (\tmp3 ->
                  set_reg tmp3 r)))))));
   Address_op a ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a)) (\addr ->
      set_mem16 seg p addr);
   Offset_op off ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce
        (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
          off)) (\addr -> set_mem16 seg p addr)}

iset_op8 :: Segment_register -> Rtl_exp -> Operand -> Conv Unit
iset_op8 seg p op =
  case op of {
   Imm_op i -> raise_error;
   Reg_op r ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce
        (load_reg
          (case r of {
            ESP -> EAX;
            EBP -> ECX;
            ESI -> EDX;
            EDI -> EBX;
            x -> x}))) (\tmp0 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce
          (load_Z size32
            (case r of {
              EAX -> Z0;
              ECX -> Z0;
              EDX -> Z0;
              EBX -> Z0;
              _ -> Zpos (XO (XO (XO XH)))}))) (\shift ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (load_int size32 (mone size32))) (\mone0 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce
              (load_Z size32 (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))
            (\mask0 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (arith size32 Shl_op mask0 shift)) (\mask1 ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (arith size32 Xor_op mask1 mone0)) (\mask2 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (arith size32 And_op tmp0 mask2)) (\tmp1 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (cast_u size8 size32 p)) (\pext ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (arith size32 Shl_op pext shift))
                      (\pext_shift ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (arith size32 Or_op tmp1 pext_shift))
                        (\res ->
                        set_reg res
                          (case r of {
                            ESP -> EAX;
                            EBP -> ECX;
                            ESI -> EDX;
                            EDI -> EBX;
                            x -> x})))))))))));
   Address_op a ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a)) (\addr ->
      set_mem8 seg p addr);
   Offset_op off ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce
        (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
          off)) (\addr -> set_mem8 seg p addr)}

load_op :: Prefix -> Bool -> Segment_register -> Operand -> Conv Rtl_exp
load_op p w seg op =
  case op_override p of {
   True ->
    case w of {
     True -> iload_op16 seg op;
     False -> iload_op8 seg op};
   False ->
    case w of {
     True -> iload_op32 seg op;
     False -> iload_op8 seg op}}

set_op :: Prefix -> Bool -> Segment_register -> Rtl_exp -> Operand -> Conv
          Unit
set_op p w seg =
  case op_override p of {
   True ->
    case w of {
     True -> iset_op16 seg;
     False -> iset_op8 seg};
   False ->
    case w of {
     True -> iset_op32 seg;
     False -> iset_op8 seg}}

get_segment :: Prefix -> Segment_register -> Segment_register
get_segment p def =
  case seg_override p of {
   Some s -> s;
   None -> def}

op_contains_stack :: Operand -> Bool
op_contains_stack op =
  case op of {
   Address_op a ->
    case addrBase a of {
     Some r ->
      case r of {
       ESP -> True;
       EBP -> True;
       _ -> False};
     None -> False};
   _ -> False}

get_segment_op :: Prefix -> Segment_register -> Operand -> Segment_register
get_segment_op p def op =
  case seg_override p of {
   Some s -> s;
   None ->
    case op_contains_stack op of {
     True -> SS;
     False -> def}}

get_segment_op2 :: Prefix -> Segment_register -> Operand -> Operand ->
                   Segment_register
get_segment_op2 p def op1 op2 =
  case seg_override p of {
   Some s -> s;
   None ->
    let {b = op_contains_stack op1} in
    let {b0 = op_contains_stack op2} in
    case b of {
     True -> SS;
     False ->
      case b0 of {
       True -> SS;
       False -> def}}}

compute_cc :: Condition_type -> Conv Rtl_exp
compute_cc ct =
  case ct of {
   O_ct -> get_flag OF;
   NO_ct -> bind (unsafeCoerce conv_monad) (get_flag OF) (\p -> not0 size1 p);
   B_ct -> get_flag CF;
   NB_ct -> bind (unsafeCoerce conv_monad) (get_flag CF) (\p -> not0 size1 p);
   E_ct -> get_flag ZF;
   NE_ct -> bind (unsafeCoerce conv_monad) (get_flag ZF) (\p -> not0 size1 p);
   BE_ct ->
    bind (unsafeCoerce conv_monad) (get_flag CF) (\cf ->
      bind (unsafeCoerce conv_monad) (get_flag ZF) (\zf ->
        arith size1 Or_op cf zf));
   NBE_ct ->
    bind (unsafeCoerce conv_monad) (get_flag CF) (\cf ->
      bind (unsafeCoerce conv_monad) (get_flag ZF) (\zf ->
        bind (unsafeCoerce conv_monad) (arith size1 Or_op cf zf) (\p ->
          not0 size1 p)));
   S_ct -> get_flag SF;
   NS_ct -> bind (unsafeCoerce conv_monad) (get_flag SF) (\p -> not0 size1 p);
   P_ct -> get_flag PF;
   NP_ct -> bind (unsafeCoerce conv_monad) (get_flag PF) (\p -> not0 size1 p);
   L_ct ->
    bind (unsafeCoerce conv_monad) (get_flag SF) (\sf ->
      bind (unsafeCoerce conv_monad) (get_flag OF) (\of0 ->
        arith size1 Xor_op sf of0));
   NL_ct ->
    bind (unsafeCoerce conv_monad) (get_flag SF) (\sf ->
      bind (unsafeCoerce conv_monad) (get_flag OF) (\of0 ->
        bind (unsafeCoerce conv_monad) (arith size1 Xor_op sf of0) (\p ->
          not0 size1 p)));
   LE_ct ->
    bind (unsafeCoerce conv_monad) (get_flag ZF) (\zf ->
      bind (unsafeCoerce conv_monad) (get_flag OF) (\of0 ->
        bind (unsafeCoerce conv_monad) (get_flag SF) (\sf ->
          bind (unsafeCoerce conv_monad) (arith size1 Xor_op of0 sf) (\p ->
            arith size1 Or_op zf p))));
   NLE_ct ->
    bind (unsafeCoerce conv_monad) (get_flag ZF) (\zf ->
      bind (unsafeCoerce conv_monad) (get_flag OF) (\of0 ->
        bind (unsafeCoerce conv_monad) (get_flag SF) (\sf ->
          bind (unsafeCoerce conv_monad) (arith size1 Xor_op of0 sf) (\p0 ->
            bind (unsafeCoerce conv_monad) (arith size1 Or_op zf p0) (\p1 ->
              not0 size1 p1)))))}

compute_parity_aux :: Nat -> Rtl_exp -> Rtl_exp -> Nat -> Conv Rtl_exp
compute_parity_aux s op1 op2 n =
  case n of {
   O -> load_Z size1 Z0;
   S m ->
    bind (unsafeCoerce conv_monad) (compute_parity_aux s op1 op2 m) (\op3 ->
      bind (unsafeCoerce conv_monad) (load_Z s (Zpos XH)) (\one2 ->
        bind (unsafeCoerce conv_monad) (arith s Shru_op op1 one2) (\op4 ->
          bind (unsafeCoerce conv_monad) (cast_u s size1 op4) (\r ->
            arith size1 Xor_op r op3))))}

compute_parity :: Nat -> Rtl_exp -> Conv Rtl_exp
compute_parity s op =
  bind (unsafeCoerce conv_monad) (load_Z size1 Z0) (\r2 ->
    bind (unsafeCoerce conv_monad) (load_Z size1 (Zpos XH)) (\one2 ->
      bind (unsafeCoerce conv_monad)
        (compute_parity_aux s op r2 (S (S (S (S (S (S (S (S O))))))))) (\p ->
        arith size1 Xor_op p one2)))

conv_INC :: Prefix -> Bool -> Operand -> Conv Unit
conv_INC pre w op =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op pre DS op} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op) (\p0 ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (load_Z (opsize (op_override pre) w) (Zpos XH))) (\p1 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith (opsize (op_override pre) w) Add_op p0 p1))
        (\p2 ->
        bind (unsafeCoerce conv_monad) (set2 seg p2 op) (\x ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (load_Z (opsize (op_override pre) w) Z0))
            (\zero2 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (test (opsize (op_override pre) w) Lt_op p2 p0))
              (\ofp ->
              bind (unsafeCoerce conv_monad) (set_flag OF ofp) (\x0 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (test (opsize (op_override pre) w) Eq_op p2 zero2))
                  (\zfp ->
                  bind (unsafeCoerce conv_monad) (set_flag ZF zfp) (\x1 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce
                        (test (opsize (op_override pre) w) Lt_op p2 zero2))
                      (\sfp ->
                      bind (unsafeCoerce conv_monad) (set_flag SF sfp)
                        (\x2 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (compute_parity (opsize (op_override pre) w) p2))
                          (\pfp ->
                          bind (unsafeCoerce conv_monad) (set_flag PF pfp)
                            (\x3 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_u (opsize (op_override pre) w) size4
                                  p0)) (\n0 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (load_Z size4 (Zpos XH)))
                                (\n1 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (arith size4 Add_op n0 n1))
                                  (\n2 ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce (test size4 Ltu_op n2 n0))
                                    (\afp -> set_flag AF afp)))))))))))))))))

conv_DEC :: Prefix -> Bool -> Operand -> Conv Unit
conv_DEC pre w op =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op pre DS op} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op) (\p0 ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (load_Z (opsize (op_override pre) w) (Zpos XH))) (\p1 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith (opsize (op_override pre) w) Sub_op p0 p1))
        (\p2 ->
        bind (unsafeCoerce conv_monad) (set2 seg p2 op) (\x ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (load_Z (opsize (op_override pre) w) Z0))
            (\zero2 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (test (opsize (op_override pre) w) Lt_op p0 p2))
              (\ofp ->
              bind (unsafeCoerce conv_monad) (set_flag OF ofp) (\x0 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (test (opsize (op_override pre) w) Eq_op p2 zero2))
                  (\zfp ->
                  bind (unsafeCoerce conv_monad) (set_flag ZF zfp) (\x1 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce
                        (test (opsize (op_override pre) w) Lt_op p2 zero2))
                      (\sfp ->
                      bind (unsafeCoerce conv_monad) (set_flag SF sfp)
                        (\x2 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (compute_parity (opsize (op_override pre) w) p2))
                          (\pfp ->
                          bind (unsafeCoerce conv_monad) (set_flag PF pfp)
                            (\x3 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_u (opsize (op_override pre) w) size4
                                  p0)) (\n0 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (load_Z size4 (Zpos XH)))
                                (\n1 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (arith size4 Sub_op n0 n1))
                                  (\n2 ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce (test size4 Ltu_op n0 n2))
                                    (\afp -> set_flag AF afp)))))))))))))))))

conv_ADC :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_ADC pre w op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op2 pre DS op1 op2} in
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce (load_Z (opsize (op_override pre) w) Z0)) (\zero2 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 (Zpos XH)))
      (\up ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1) (\p0 ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op2) (\p1 ->
          bind (unsafeCoerce conv_monad) (unsafeCoerce (get_flag CF))
            (\cf1 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (cast_u size1 (opsize (op_override pre) w) cf1))
              (\cfext ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce
                  (arith (opsize (op_override pre) w) Add_op p0 p1)) (\p2 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (arith (opsize (op_override pre) w) Add_op p2 cfext))
                  (\p3 ->
                  bind (unsafeCoerce conv_monad) (set2 seg p3 op1) (\x ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce
                        (test (opsize (op_override pre) w) Lt_op zero2 p0))
                      (\b0 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (test (opsize (op_override pre) w) Lt_op zero2 p1))
                        (\b1 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (test (opsize (op_override pre) w) Lt_op zero2
                              p3)) (\b2 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (arith size1 Xor_op b0 b1)) (\b3 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (arith size1 Xor_op up b3))
                              (\b4 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (arith size1 Xor_op b0 b2))
                                (\b5 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (arith size1 And_op b4 b5))
                                  (\b6 ->
                                  bind (unsafeCoerce conv_monad)
                                    (set_flag OF b6) (\x0 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (test (opsize (op_override pre) w)
                                          Ltu_op p3 p0)) (\b7 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (test (opsize (op_override pre) w)
                                            Ltu_op p3 p1)) (\b8 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (arith size1 Or_op b7 b8))
                                          (\b9 ->
                                          bind (unsafeCoerce conv_monad)
                                            (set_flag CF b9) (\x1 ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (test
                                                  (opsize (op_override pre)
                                                    w) Eq_op p3 zero2))
                                              (\b10 ->
                                              bind (unsafeCoerce conv_monad)
                                                (set_flag ZF b10) (\x2 ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (test
                                                      (opsize
                                                        (op_override pre) w)
                                                      Lt_op p3 zero2))
                                                  (\b11 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (set_flag SF b11) (\x3 ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce
                                                        (compute_parity
                                                          (opsize
                                                            (op_override pre)
                                                            w) p3)) (\b12 ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (set_flag PF b12)
                                                        (\x4 ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (unsafeCoerce
                                                            (cast_u
                                                              (opsize
                                                                (op_override
                                                                  pre) w)
                                                              size4 p0))
                                                          (\n0 ->
                                                          bind
                                                            (unsafeCoerce
                                                              conv_monad)
                                                            (unsafeCoerce
                                                              (cast_u
                                                                (opsize
                                                                  (op_override
                                                                    pre) w)
                                                                size4 p1))
                                                            (\n1 ->
                                                            bind
                                                              (unsafeCoerce
                                                                conv_monad)
                                                              (unsafeCoerce
                                                                (cast_u size1
                                                                  size4 cf1))
                                                              (\cf4 ->
                                                              bind
                                                                (unsafeCoerce
                                                                  conv_monad)
                                                                (unsafeCoerce
                                                                  (arith
                                                                    size4
                                                                    Add_op n0
                                                                    n1))
                                                                (\n2 ->
                                                                bind
                                                                  (unsafeCoerce
                                                                    conv_monad)
                                                                  (unsafeCoerce
                                                                    (arith
                                                                    size4
                                                                    Add_op n2
                                                                    cf4))
                                                                  (\n3 ->
                                                                  bind
                                                                    (unsafeCoerce
                                                                    conv_monad)
                                                                    (unsafeCoerce
                                                                    (test
                                                                    size4
                                                                    Ltu_op n3
                                                                    n0))
                                                                    (\b13 ->
                                                                    bind
                                                                    (unsafeCoerce
                                                                    conv_monad)
                                                                    (unsafeCoerce
                                                                    (test
                                                                    size4
                                                                    Ltu_op n3
                                                                    n1))
                                                                    (\b14 ->
                                                                    bind
                                                                    (unsafeCoerce
                                                                    conv_monad)
                                                                    (unsafeCoerce
                                                                    (arith
                                                                    size1
                                                                    Or_op b13
                                                                    b14))
                                                                    (\b15 ->
                                                                    set_flag
                                                                    AF b15)))))))))))))))))))))))))))))))))))

conv_STC :: Conv Unit
conv_STC =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 (Zpos XH)))
    (\one2 -> set_flag CF one2)

conv_STD :: Conv Unit
conv_STD =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 (Zpos XH)))
    (\one2 -> set_flag DF one2)

conv_CLC :: Conv Unit
conv_CLC =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 Z0)) (\zero2 ->
    set_flag CF zero2)

conv_CLD :: Conv Unit
conv_CLD =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 Z0)) (\zero2 ->
    set_flag DF zero2)

conv_CMC :: Conv Unit
conv_CMC =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 Z0)) (\zero2 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (get_flag CF)) (\p1 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (test size1 Eq_op zero2 p1)) (\p0 -> set_flag CF p0)))

conv_LAHF :: Conv Unit
conv_LAHF =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size8 Z0)) (\dst ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (get_flag SF)) (\fl ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (load_Z size8 (Zpos (XI (XI XH))))) (\pos ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce (cast_u size1 size8 fl))
          (\byt ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (arith size8 Shl_op byt pos)) (\tmp ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (arith size8 Or_op dst tmp)) (\dst0 ->
              bind (unsafeCoerce conv_monad) (unsafeCoerce (get_flag ZF))
                (\fl0 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (load_Z size8 (Zpos (XO (XI XH))))) (\pos0 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (cast_u size1 size8 fl0)) (\byt0 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (arith size8 Shl_op byt0 pos0)) (\tmp0 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (arith size8 Or_op dst0 tmp0))
                        (\dst1 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (get_flag AF)) (\fl1 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (load_Z size8 (Zpos (XO (XO XH)))))
                            (\pos2 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (cast_u size1 size8 fl1))
                              (\byt1 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (arith size8 Shl_op byt1 pos2))
                                (\tmp1 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (arith size8 Or_op dst1 tmp1)) (\dst2 ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce (get_flag PF)) (\fl2 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (load_Z size8 (Zpos (XO XH))))
                                      (\pos3 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (cast_u size1 size8 fl2)) (\byt2 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (arith size8 Shl_op byt2 pos3))
                                          (\tmp2 ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (arith size8 Or_op dst2 tmp2))
                                            (\dst3 ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce (get_flag CF))
                                              (\fl3 ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (load_Z size8 Z0))
                                                (\pos4 ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (cast_u size1 size8 fl3))
                                                  (\byt3 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (arith size8 Shl_op
                                                        byt3 pos4)) (\tmp3 ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce
                                                        (arith size8 Or_op
                                                          dst3 tmp3))
                                                      (\dst4 ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (unsafeCoerce
                                                          (load_Z size8 (Zpos
                                                            XH))) (\fl4 ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (unsafeCoerce
                                                            (load_Z size8
                                                              (Zpos XH)))
                                                          (\pos5 ->
                                                          bind
                                                            (unsafeCoerce
                                                              conv_monad)
                                                            (unsafeCoerce
                                                              (cast_u size8
                                                                size8 fl4))
                                                            (\byt4 ->
                                                            bind
                                                              (unsafeCoerce
                                                                conv_monad)
                                                              (unsafeCoerce
                                                                (arith size8
                                                                  Shl_op byt4
                                                                  pos5))
                                                              (\tmp4 ->
                                                              bind
                                                                (unsafeCoerce
                                                                  conv_monad)
                                                                (unsafeCoerce
                                                                  (arith
                                                                    size8
                                                                    Or_op
                                                                    dst4
                                                                    tmp4))
                                                                (\dst5 ->
                                                                iset_op8 DS
                                                                  dst5
                                                                  (Reg_op
                                                                  ESP))))))))))))))))))))))))))))))))

conv_SAHF :: Conv Unit
conv_SAHF =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size8 (Zpos XH)))
    (\one2 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (iload_op8 DS (Reg_op ESP)))
      (\ah ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (load_Z size8 (Zpos (XI (XI XH))))) (\pos ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size8 Shr_op ah pos)) (\tmp ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (arith size8 And_op tmp one2)) (\tmp0 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (test size8 Eq_op one2 tmp0)) (\b ->
              bind (unsafeCoerce conv_monad) (set_flag SF b) (\x ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (load_Z size8 (Zpos (XO (XI XH))))) (\pos0 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (arith size8 Shr_op ah pos0)) (\tmp1 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (arith size8 And_op tmp1 one2)) (\tmp2 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (test size8 Eq_op one2 tmp2)) (\b0 ->
                        bind (unsafeCoerce conv_monad) (set_flag ZF b0)
                          (\x0 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (load_Z size8 (Zpos (XO (XO XH)))))
                            (\pos2 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (arith size8 Shr_op ah pos2))
                              (\tmp3 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (arith size8 And_op tmp3 one2))
                                (\tmp4 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (test size8 Eq_op one2 tmp4))
                                  (\b1 ->
                                  bind (unsafeCoerce conv_monad)
                                    (set_flag AF b1) (\x1 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (load_Z size8 (Zpos (XO XH))))
                                      (\pos3 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (arith size8 Shr_op ah pos3))
                                        (\tmp5 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (arith size8 And_op tmp5 one2))
                                          (\tmp6 ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (test size8 Eq_op one2 tmp6))
                                            (\b2 ->
                                            bind (unsafeCoerce conv_monad)
                                              (set_flag PF b2) (\x2 ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (load_Z size8 Z0))
                                                (\pos4 ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (arith size8 Shr_op ah
                                                      pos4)) (\tmp7 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (arith size8 And_op
                                                        tmp7 one2)) (\tmp8 ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce
                                                        (test size8 Eq_op
                                                          one2 tmp8)) (\b3 ->
                                                      set_flag CF b3))))))))))))))))))))))))))

conv_ADD :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_ADD pre w op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op2 pre DS op1 op2} in
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce (load_Z (opsize (op_override pre) w) Z0)) (\zero2 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 (Zpos XH)))
      (\up ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1) (\p0 ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op2) (\p1 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (arith (opsize (op_override pre) w) Add_op p0 p1))
            (\p2 ->
            bind (unsafeCoerce conv_monad) (set2 seg p2 op1) (\x ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce
                  (test (opsize (op_override pre) w) Lt_op zero2 p0)) (\b0 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (test (opsize (op_override pre) w) Lt_op zero2 p1))
                  (\b1 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (test (opsize (op_override pre) w) Lt_op zero2 p2))
                    (\b2 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (arith size1 Xor_op b0 b1)) (\b3 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (arith size1 Xor_op up b3)) (\b4 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (arith size1 Xor_op b0 b2)) (\b5 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (arith size1 And_op b4 b5)) (\b6 ->
                            bind (unsafeCoerce conv_monad) (set_flag OF b6)
                              (\x0 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (test (opsize (op_override pre) w) Ltu_op
                                    p2 p0)) (\b7 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (test (opsize (op_override pre) w) Ltu_op
                                      p2 p1)) (\b8 ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce (arith size1 Or_op b7 b8))
                                    (\b9 ->
                                    bind (unsafeCoerce conv_monad)
                                      (set_flag CF b9) (\x1 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (test (opsize (op_override pre) w)
                                            Eq_op p2 zero2)) (\b10 ->
                                        bind (unsafeCoerce conv_monad)
                                          (set_flag ZF b10) (\x2 ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (test
                                                (opsize (op_override pre) w)
                                                Lt_op p2 zero2)) (\b11 ->
                                            bind (unsafeCoerce conv_monad)
                                              (set_flag SF b11) (\x3 ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (compute_parity
                                                    (opsize (op_override pre)
                                                      w) p2)) (\b12 ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (set_flag PF b12) (\x4 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (cast_u
                                                        (opsize
                                                          (op_override pre)
                                                          w) size4 p0))
                                                    (\n0 ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce
                                                        (cast_u
                                                          (opsize
                                                            (op_override pre)
                                                            w) size4 p1))
                                                      (\n1 ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (unsafeCoerce
                                                          (arith size4 Add_op
                                                            n0 n1)) (\n2 ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (unsafeCoerce
                                                            (test size4
                                                              Ltu_op n2 n0))
                                                          (\b13 ->
                                                          bind
                                                            (unsafeCoerce
                                                              conv_monad)
                                                            (unsafeCoerce
                                                              (test size4
                                                                Ltu_op n2 n1))
                                                            (\b14 ->
                                                            bind
                                                              (unsafeCoerce
                                                                conv_monad)
                                                              (unsafeCoerce
                                                                (arith size1
                                                                  Or_op b13
                                                                  b14))
                                                              (\b15 ->
                                                              set_flag AF b15))))))))))))))))))))))))))))))

conv_SUB_CMP_generic :: Bool -> Prefix -> Bool -> Operand -> Operand ->
                        Operand -> Segment_register -> Segment_register ->
                        Segment_register -> Conv Unit
conv_SUB_CMP_generic e pre w dest op1 op2 segdest seg1 seg2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce (load_Z (opsize (op_override pre) w) Z0)) (\zero2 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 (Zpos XH)))
      (\up ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce load seg1 op1) (\p0 ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce load seg2 op2) (\p1 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (arith (opsize (op_override pre) w) Sub_op p0 p1))
            (\p2 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce
                (arith (opsize (op_override pre) w) Sub_op zero2 p1))
              (\negp1 ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce
                  (test (opsize (op_override pre) w) Lt_op zero2 p0)) (\b0 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (test (opsize (op_override pre) w) Lt_op zero2 negp1))
                  (\b1 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (test (opsize (op_override pre) w) Lt_op zero2 p2))
                    (\b2 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (arith size1 Xor_op b0 b1)) (\b3 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (arith size1 Xor_op up b3)) (\b4 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (arith size1 Xor_op b0 b2)) (\b5 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (arith size1 And_op b4 b5)) (\b6 ->
                            bind (unsafeCoerce conv_monad) (set_flag OF b6)
                              (\x ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (test (opsize (op_override pre) w) Ltu_op
                                    p0 p1)) (\b7 ->
                                bind (unsafeCoerce conv_monad)
                                  (set_flag CF b7) (\x0 ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (test (opsize (op_override pre) w)
                                        Eq_op p2 zero2)) (\b8 ->
                                    bind (unsafeCoerce conv_monad)
                                      (set_flag ZF b8) (\x1 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (test (opsize (op_override pre) w)
                                            Lt_op p2 zero2)) (\b9 ->
                                        bind (unsafeCoerce conv_monad)
                                          (set_flag SF b9) (\x2 ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (compute_parity
                                                (opsize (op_override pre) w)
                                                p2)) (\b10 ->
                                            bind (unsafeCoerce conv_monad)
                                              (set_flag PF b10) (\x3 ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (cast_u
                                                    (opsize (op_override pre)
                                                      w) size4 p0)) (\n0 ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (cast_u
                                                      (opsize
                                                        (op_override pre) w)
                                                      size4 p1)) (\n1 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (test
                                                        (opsize
                                                          (op_override pre)
                                                          w) Ltu_op p0 p1))
                                                    (\b11 ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (set_flag AF b11)
                                                      (\x4 ->
                                                      case e of {
                                                       True ->
                                                        set2 segdest p2 dest;
                                                       False -> no_op}))))))))))))))))))))))))))

conv_CMP :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_CMP pre w op1 op2 =
  let {seg = get_segment_op2 pre DS op1 op2} in
  conv_SUB_CMP_generic False pre w op1 op1 op2 seg seg seg

conv_SUB :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_SUB pre w op1 op2 =
  let {seg = get_segment_op2 pre DS op1 op2} in
  conv_SUB_CMP_generic True pre w op1 op1 op2 seg seg seg

conv_NEG :: Prefix -> Bool -> Operand -> Conv Unit
conv_NEG pre w op1 =
  let {seg = get_segment_op pre DS op1} in
  conv_SUB_CMP_generic True pre w op1 (Imm_op
    (zero1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) op1 seg
    seg seg

conv_SBB :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_SBB pre w op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op2 pre DS op1 op2} in
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce (load_Z (opsize (op_override pre) w) Z0)) (\zero2 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 (Zpos XH)))
      (\up ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (get_flag CF)) (\old_cf ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (cast_u size1 (opsize (op_override pre) w) old_cf))
          (\old_cf_ext ->
          bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1) (\p0 ->
            bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op2)
              (\p1 ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce
                  (arith (opsize (op_override pre) w) Sub_op p0 p1))
                (\p2_0 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (arith (opsize (op_override pre) w) Sub_op p2_0
                      old_cf_ext)) (\p2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (arith (opsize (op_override pre) w) Sub_op zero2 p1))
                    (\negp1 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce
                        (test (opsize (op_override pre) w) Lt_op zero2 p0))
                      (\b0 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (test (opsize (op_override pre) w) Lt_op zero2
                            negp1)) (\b1 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (test (opsize (op_override pre) w) Lt_op zero2
                              p2)) (\b2 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (arith size1 Xor_op b0 b1)) (\b3 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (arith size1 Xor_op up b3))
                              (\b4 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (arith size1 Xor_op b0 b2))
                                (\b5 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (arith size1 And_op b4 b5))
                                  (\b6 ->
                                  bind (unsafeCoerce conv_monad)
                                    (set_flag OF b6) (\x ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (test (opsize (op_override pre) w)
                                          Ltu_op p0 p1)) (\b0' ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (test (opsize (op_override pre) w)
                                            Eq_op p0 p1)) (\b0'' ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (arith size1 Or_op b0' b0''))
                                          (\b7 ->
                                          bind (unsafeCoerce conv_monad)
                                            (set_flag CF b7) (\x0 ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (test
                                                  (opsize (op_override pre)
                                                    w) Eq_op p2 zero2))
                                              (\b8 ->
                                              bind (unsafeCoerce conv_monad)
                                                (set_flag ZF b8) (\x1 ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (test
                                                      (opsize
                                                        (op_override pre) w)
                                                      Lt_op p2 zero2))
                                                  (\b9 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (set_flag SF b9) (\x2 ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce
                                                        (compute_parity
                                                          (opsize
                                                            (op_override pre)
                                                            w) p2)) (\b10 ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (set_flag PF b10)
                                                        (\x3 ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (unsafeCoerce
                                                            (cast_u
                                                              (opsize
                                                                (op_override
                                                                  pre) w)
                                                              size4 p0))
                                                          (\n0 ->
                                                          bind
                                                            (unsafeCoerce
                                                              conv_monad)
                                                            (unsafeCoerce
                                                              (cast_u
                                                                (opsize
                                                                  (op_override
                                                                    pre) w)
                                                                size4 p1))
                                                            (\n1 ->
                                                            bind
                                                              (unsafeCoerce
                                                                conv_monad)
                                                              (unsafeCoerce
                                                                (test
                                                                  (opsize
                                                                    (op_override
                                                                    pre) w)
                                                                  Ltu_op p0
                                                                  p1))
                                                              (\b0'0 ->
                                                              bind
                                                                (unsafeCoerce
                                                                  conv_monad)
                                                                (unsafeCoerce
                                                                  (test
                                                                    (opsize
                                                                    (op_override
                                                                    pre) w)
                                                                    Eq_op p0
                                                                    p1))
                                                                (\b0''0 ->
                                                                bind
                                                                  (unsafeCoerce
                                                                    conv_monad)
                                                                  (unsafeCoerce
                                                                    (arith
                                                                    size1
                                                                    Or_op
                                                                    b0'0
                                                                    b0''0))
                                                                  (\b11 ->
                                                                  bind
                                                                    (unsafeCoerce
                                                                    conv_monad)
                                                                    (set_flag
                                                                    AF b11)
                                                                    (\x4 ->
                                                                    set2 seg
                                                                    p2 op1)))))))))))))))))))))))))))))))))

conv_DIV :: Prefix -> Bool -> Operand -> Conv Unit
conv_DIV pre w op =
  let {seg = get_segment_op pre DS op} in
  bind (unsafeCoerce conv_monad) (undef_flag CF) (\x ->
    bind (unsafeCoerce conv_monad) (undef_flag OF) (\x0 ->
      bind (unsafeCoerce conv_monad) (undef_flag SF) (\x1 ->
        bind (unsafeCoerce conv_monad) (undef_flag ZF) (\x2 ->
          bind (unsafeCoerce conv_monad) (undef_flag AF) (\x3 ->
            bind (unsafeCoerce conv_monad) (undef_flag PF) (\x4 ->
              case op_override pre of {
               True ->
                case w of {
                 True ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (iload_op16 seg (Reg_op EAX)))
                    (\dividend_lower ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (iload_op16 seg (Reg_op EDX)))
                      (\dividend_upper ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (cast_u size16 size32 dividend_upper))
                        (\dividend0 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (load_Z size32 (Zpos (XO (XO (XO (XO XH)))))))
                          (\sixteen ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith size32 Shl_op dividend0 sixteen))
                            (\dividend1 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_u size16 size32 dividend_lower))
                              (\dividend_lower_ext ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith size32 Or_op dividend1
                                    dividend_lower_ext)) (\dividend ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (iload_op16 seg op))
                                  (\divisor ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce (load_Z size16 Z0))
                                    (\zero2 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (test size16 Eq_op zero2 divisor))
                                      (\divide_by_zero ->
                                      bind (unsafeCoerce conv_monad)
                                        (if_trap divide_by_zero) (\x5 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (cast_u size16 size32 divisor))
                                          (\divisor_ext ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (arith size32 Divu_op dividend
                                                divisor_ext)) (\quotient ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (load_Z size32 (Zpos (XI (XI
                                                  (XI (XI (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI (XI (XI
                                                  XH))))))))))))))))))
                                              (\max_quotient ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (test size32 Ltu_op
                                                    max_quotient quotient))
                                                (\div_error ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (if_trap div_error) (\x6 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (arith size32 Modu_op
                                                        dividend divisor_ext))
                                                    (\remainder ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce
                                                        (cast_u size32 size16
                                                          quotient))
                                                      (\quotient_trunc ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (unsafeCoerce
                                                          (cast_u size32
                                                            size16 remainder))
                                                        (\remainder_trunc ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (iset_op16 seg
                                                            quotient_trunc
                                                            (Reg_op EAX))
                                                          (\x7 ->
                                                          iset_op16 seg
                                                            remainder_trunc
                                                            (Reg_op EDX)))))))))))))))))))));
                 False ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (iload_op16 seg (Reg_op EAX)))
                    (\dividend ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (iload_op8 seg op)) (\divisor ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (load_Z size8 Z0)) (\zero2 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (test size8 Eq_op zero2 divisor))
                          (\divide_by_zero ->
                          bind (unsafeCoerce conv_monad)
                            (if_trap divide_by_zero) (\x5 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (cast_u size8 size16 divisor))
                              (\divisor_ext ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith size16 Divu_op dividend divisor_ext))
                                (\quotient ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (load_Z size16 (Zpos (XI (XI (XI (XI (XI
                                      (XI (XI XH)))))))))) (\max_quotient ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (test size16 Ltu_op max_quotient
                                        quotient)) (\div_error ->
                                    bind (unsafeCoerce conv_monad)
                                      (if_trap div_error) (\x6 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (arith size16 Modu_op dividend
                                            divisor_ext)) (\remainder ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (cast_u size16 size8 quotient))
                                          (\quotient_trunc ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (cast_u size16 size8 remainder))
                                            (\remainder_trunc ->
                                            bind (unsafeCoerce conv_monad)
                                              (iset_op8 seg quotient_trunc
                                                (Reg_op EAX)) (\x7 ->
                                              iset_op8 seg remainder_trunc
                                                (Reg_op ESP)))))))))))))))};
               False ->
                case w of {
                 True ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (iload_op32 seg (Reg_op EAX)))
                    (\dividend_lower ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (iload_op32 seg (Reg_op EDX)))
                      (\dividend_upper ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (cast_u size32 (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S
                            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                            dividend_upper)) (\dividend0 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (load_Z (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S
                              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                              (Zpos (XO (XO (XO (XO (XO XH))))))))
                          (\thirtytwo ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S
                                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                Shl_op dividend0 thirtytwo)) (\dividend1 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_u size32 (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  dividend_lower)) (\dividend_lower_ext ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S
                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    Or_op dividend1 dividend_lower_ext))
                                (\dividend ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (iload_op32 seg op))
                                  (\divisor ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce (load_Z size32 Z0))
                                    (\zero2 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (test size32 Eq_op zero2 divisor))
                                      (\divide_by_zero ->
                                      bind (unsafeCoerce conv_monad)
                                        (if_trap divide_by_zero) (\x5 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (cast_u size32 (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S
                                              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                              divisor)) (\divisor_ext ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (arith (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S
                                                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                Divu_op dividend divisor_ext))
                                            (\quotient ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (load_Z (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S
                                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                  (Zpos (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI (XI
                                                  XH))))))))))))))))))))))))))))))))))
                                              (\max_quotient ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (test (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                    Ltu_op max_quotient
                                                    quotient)) (\div_error ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (if_trap div_error) (\x6 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (arith (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S
                                                        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                        Modu_op dividend
                                                        divisor_ext))
                                                    (\remainder ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce
                                                        (cast_u (S (S (S (S
                                                          (S (S (S (S (S (S
                                                          (S (S (S (S (S (S
                                                          (S (S (S (S (S (S
                                                          (S (S (S (S (S (S
                                                          (S (S (S (S (S (S
                                                          (S (S (S (S (S (S
                                                          (S (S (S (S (S (S
                                                          (S (S (S (S (S (S
                                                          (S (S (S (S (S (S
                                                          (S (S (S (S (S
                                                          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                          size32 quotient))
                                                      (\quotient_trunc ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (unsafeCoerce
                                                          (cast_u (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S (S
                                                            (S (S (S (S (S
                                                            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                            size32 remainder))
                                                        (\remainder_trunc ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (iset_op32 seg
                                                            quotient_trunc
                                                            (Reg_op EAX))
                                                          (\x7 ->
                                                          iset_op32 seg
                                                            remainder_trunc
                                                            (Reg_op EDX)))))))))))))))))))));
                 False ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (iload_op16 seg (Reg_op EAX)))
                    (\dividend ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (iload_op8 seg op)) (\divisor ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (load_Z size8 Z0)) (\zero2 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (test size8 Eq_op zero2 divisor))
                          (\divide_by_zero ->
                          bind (unsafeCoerce conv_monad)
                            (if_trap divide_by_zero) (\x5 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (cast_u size8 size16 divisor))
                              (\divisor_ext ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith size16 Divu_op dividend divisor_ext))
                                (\quotient ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (load_Z size16 (Zpos (XI (XI (XI (XI (XI
                                      (XI (XI XH)))))))))) (\max_quotient ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (test size16 Ltu_op max_quotient
                                        quotient)) (\div_error ->
                                    bind (unsafeCoerce conv_monad)
                                      (if_trap div_error) (\x6 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (arith size16 Modu_op dividend
                                            divisor_ext)) (\remainder ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (cast_u size16 size8 quotient))
                                          (\quotient_trunc ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (cast_u size16 size8 remainder))
                                            (\remainder_trunc ->
                                            bind (unsafeCoerce conv_monad)
                                              (iset_op8 seg quotient_trunc
                                                (Reg_op EAX)) (\x7 ->
                                              iset_op8 seg remainder_trunc
                                                (Reg_op ESP)))))))))))))))}}))))))

conv_IDIV :: Prefix -> Bool -> Operand -> Conv Unit
conv_IDIV pre w op =
  let {seg = get_segment_op pre DS op} in
  bind (unsafeCoerce conv_monad) (undef_flag CF) (\x ->
    bind (unsafeCoerce conv_monad) (undef_flag OF) (\x0 ->
      bind (unsafeCoerce conv_monad) (undef_flag SF) (\x1 ->
        bind (unsafeCoerce conv_monad) (undef_flag ZF) (\x2 ->
          bind (unsafeCoerce conv_monad) (undef_flag AF) (\x3 ->
            bind (unsafeCoerce conv_monad) (undef_flag PF) (\x4 ->
              case op_override pre of {
               True ->
                case w of {
                 True ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (iload_op16 seg (Reg_op EAX)))
                    (\dividend_lower ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (iload_op16 seg (Reg_op EDX)))
                      (\dividend_upper ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (cast_s size16 size32 dividend_upper))
                        (\dividend0 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (load_Z size32 (Zpos (XO (XO (XO (XO XH)))))))
                          (\sixteen ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith size32 Shl_op dividend0 sixteen))
                            (\dividend1 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_s size16 size32 dividend_lower))
                              (\dividend_lower_ext ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith size32 Or_op dividend1
                                    dividend_lower_ext)) (\dividend ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (iload_op16 seg op))
                                  (\divisor ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce (load_Z size16 Z0))
                                    (\zero2 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (test size16 Eq_op zero2 divisor))
                                      (\divide_by_zero ->
                                      bind (unsafeCoerce conv_monad)
                                        (if_trap divide_by_zero) (\x5 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (cast_s size16 size32 divisor))
                                          (\divisor_ext ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (arith size32 Divs_op dividend
                                                divisor_ext)) (\quotient ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (load_Z size32 (Zpos (XI (XI
                                                  (XI (XI (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI (XI
                                                  XH)))))))))))))))))
                                              (\max_quotient ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (load_Z size32 (Zneg (XO
                                                    (XO (XO (XO (XO (XO (XO
                                                    (XO (XO (XO (XO (XO (XO
                                                    (XO (XO
                                                    XH))))))))))))))))))
                                                (\min_quotient ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (test size32 Lt_op
                                                      max_quotient quotient))
                                                  (\div_error0 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (test size32 Lt_op
                                                        quotient
                                                        min_quotient))
                                                    (\div_error1 ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce
                                                        (arith size1 Or_op
                                                          div_error0
                                                          div_error1))
                                                      (\div_error ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (if_trap div_error)
                                                        (\x6 ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (unsafeCoerce
                                                            (arith size32
                                                              Mods_op
                                                              dividend
                                                              divisor_ext))
                                                          (\remainder ->
                                                          bind
                                                            (unsafeCoerce
                                                              conv_monad)
                                                            (unsafeCoerce
                                                              (cast_s size32
                                                                size16
                                                                quotient))
                                                            (\quotient_trunc ->
                                                            bind
                                                              (unsafeCoerce
                                                                conv_monad)
                                                              (unsafeCoerce
                                                                (cast_s
                                                                  size32
                                                                  size16
                                                                  remainder))
                                                              (\remainder_trunc ->
                                                              bind
                                                                (unsafeCoerce
                                                                  conv_monad)
                                                                (iset_op16
                                                                  seg
                                                                  quotient_trunc
                                                                  (Reg_op
                                                                  EAX))
                                                                (\x7 ->
                                                                iset_op16 seg
                                                                  remainder_trunc
                                                                  (Reg_op
                                                                  EDX))))))))))))))))))))))));
                 False ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (iload_op16 seg (Reg_op EAX)))
                    (\dividend ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (iload_op8 seg op)) (\divisor ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (load_Z size8 Z0)) (\zero2 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (test size8 Eq_op zero2 divisor))
                          (\divide_by_zero ->
                          bind (unsafeCoerce conv_monad)
                            (if_trap divide_by_zero) (\x5 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (cast_s size8 size16 divisor))
                              (\divisor_ext ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith size16 Divs_op dividend divisor_ext))
                                (\quotient ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (load_Z size16 (Zpos (XI (XI (XI (XI (XI
                                      (XI XH))))))))) (\max_quotient ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (load_Z size16 (Zneg (XO (XO (XO (XO
                                        (XO (XO (XO XH))))))))))
                                    (\min_quotient ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (test size16 Lt_op max_quotient
                                          quotient)) (\div_error0 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (test size16 Lt_op quotient
                                            min_quotient)) (\div_error1 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (arith size1 Or_op div_error0
                                              div_error1)) (\div_error ->
                                          bind (unsafeCoerce conv_monad)
                                            (if_trap div_error) (\x6 ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (arith size16 Mods_op
                                                  dividend divisor_ext))
                                              (\remainder ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (cast_s size16 size8
                                                    quotient))
                                                (\quotient_trunc ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (cast_s size16 size8
                                                      remainder))
                                                  (\remainder_trunc ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (iset_op8 seg
                                                      quotient_trunc (Reg_op
                                                      EAX)) (\x7 ->
                                                    iset_op8 seg
                                                      remainder_trunc (Reg_op
                                                      ESP))))))))))))))))))};
               False ->
                case w of {
                 True ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (iload_op32 seg (Reg_op EAX)))
                    (\dividend_lower ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (iload_op32 seg (Reg_op EDX)))
                      (\dividend_upper ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (cast_s size32 (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S
                            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                            dividend_upper)) (\dividend0 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (load_Z (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S
                              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                              (Zpos (XO (XO (XO (XO (XO XH))))))))
                          (\thirtytwo ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S
                                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                Shl_op dividend0 thirtytwo)) (\dividend1 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_s size32 (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  dividend_lower)) (\dividend_lower_ext ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S
                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    Or_op dividend1 dividend_lower_ext))
                                (\dividend ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (iload_op32 seg op))
                                  (\divisor ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce (load_Z size32 Z0))
                                    (\zero2 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (test size32 Eq_op zero2 divisor))
                                      (\divide_by_zero ->
                                      bind (unsafeCoerce conv_monad)
                                        (if_trap divide_by_zero) (\x5 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (cast_s size32 (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S
                                              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                              divisor)) (\divisor_ext ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (arith (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S
                                                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                Divs_op dividend divisor_ext))
                                            (\quotient ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (load_Z (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S (S (S (S (S (S (S (S
                                                  (S (S
                                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                  (Zpos (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI (XI (XI (XI
                                                  (XI (XI (XI (XI
                                                  XH)))))))))))))))))))))))))))))))))
                                              (\max_quotient ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (load_Z (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S
                                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                    (Zneg (XO (XO (XO (XO (XO
                                                    (XO (XO (XO (XO (XO (XO
                                                    (XO (XO (XO (XO (XO (XO
                                                    (XO (XO (XO (XO (XO (XO
                                                    (XO (XO (XO (XO (XO (XO
                                                    (XO (XO
                                                    XH))))))))))))))))))))))))))))))))))
                                                (\min_quotient ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (test (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S
                                                      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                      Lt_op max_quotient
                                                      quotient))
                                                  (\div_error0 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (test (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S (S (S (S (S (S (S
                                                        (S
                                                        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                        Lt_op quotient
                                                        min_quotient))
                                                    (\div_error1 ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce
                                                        (arith size1 Or_op
                                                          div_error0
                                                          div_error1))
                                                      (\div_error ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (if_trap div_error)
                                                        (\x6 ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (unsafeCoerce
                                                            (arith (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              (S (S (S (S (S
                                                              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                              Mods_op
                                                              dividend
                                                              divisor_ext))
                                                          (\remainder ->
                                                          bind
                                                            (unsafeCoerce
                                                              conv_monad)
                                                            (unsafeCoerce
                                                              (cast_s (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S (S (S (S
                                                                (S
                                                                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                size32
                                                                quotient))
                                                            (\quotient_trunc ->
                                                            bind
                                                              (unsafeCoerce
                                                                conv_monad)
                                                              (unsafeCoerce
                                                                (cast_s (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S (S (S (S
                                                                  (S
                                                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                  size32
                                                                  remainder))
                                                              (\remainder_trunc ->
                                                              bind
                                                                (unsafeCoerce
                                                                  conv_monad)
                                                                (iset_op32
                                                                  seg
                                                                  quotient_trunc
                                                                  (Reg_op
                                                                  EAX))
                                                                (\x7 ->
                                                                iset_op32 seg
                                                                  remainder_trunc
                                                                  (Reg_op
                                                                  EDX))))))))))))))))))))))));
                 False ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (iload_op16 seg (Reg_op EAX)))
                    (\dividend ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (iload_op8 seg op)) (\divisor ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (load_Z size8 Z0)) (\zero2 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (test size8 Eq_op zero2 divisor))
                          (\divide_by_zero ->
                          bind (unsafeCoerce conv_monad)
                            (if_trap divide_by_zero) (\x5 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (cast_s size8 size16 divisor))
                              (\divisor_ext ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith size16 Divs_op dividend divisor_ext))
                                (\quotient ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (load_Z size16 (Zpos (XI (XI (XI (XI (XI
                                      (XI XH))))))))) (\max_quotient ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (load_Z size16 (Zneg (XO (XO (XO (XO
                                        (XO (XO (XO XH))))))))))
                                    (\min_quotient ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (test size16 Lt_op max_quotient
                                          quotient)) (\div_error0 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (test size16 Lt_op quotient
                                            min_quotient)) (\div_error1 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (arith size1 Or_op div_error0
                                              div_error1)) (\div_error ->
                                          bind (unsafeCoerce conv_monad)
                                            (if_trap div_error) (\x6 ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (arith size16 Mods_op
                                                  dividend divisor_ext))
                                              (\remainder ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (cast_s size16 size8
                                                    quotient))
                                                (\quotient_trunc ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (cast_s size16 size8
                                                      remainder))
                                                  (\remainder_trunc ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (iset_op8 seg
                                                      quotient_trunc (Reg_op
                                                      EAX)) (\x7 ->
                                                    iset_op8 seg
                                                      remainder_trunc (Reg_op
                                                      ESP))))))))))))))))))}}))))))

conv_IMUL :: Prefix -> Bool -> Operand -> (Option Operand) -> (Option 
             Int32) -> Conv Unit
conv_IMUL pre w op1 opopt2 iopt =
  bind (unsafeCoerce conv_monad) (undef_flag SF) (\x ->
    bind (unsafeCoerce conv_monad) (undef_flag ZF) (\x0 ->
      bind (unsafeCoerce conv_monad) (undef_flag AF) (\x1 ->
        bind (unsafeCoerce conv_monad) (undef_flag PF) (\x2 ->
          case opopt2 of {
           Some op2 ->
            case iopt of {
             Some imm3 ->
              let {load = load_op pre w} in
              let {set2 = set_op pre w} in
              let {seg = get_segment_op2 pre DS op1 op2} in
              bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op2)
                (\p1 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      O))))))))))))))))))))))))))))))) imm3)) (\p2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (cast_s (opsize (op_override pre) w)
                        (minus
                          (mult (S (S O))
                            (plus (opsize (op_override pre) w) (S O))) (S O))
                        p1)) (\p1ext ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce
                        (cast_s (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          O)))))))))))))))))))))))))))))))
                          (minus
                            (mult (S (S O))
                              (plus (opsize (op_override pre) w) (S O))) (S
                            O)) p2)) (\p2ext ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (arith
                            (minus
                              (mult (S (S O))
                                (plus (opsize (op_override pre) w) (S O))) (S
                              O)) Mul_op p1ext p2ext)) (\res ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (cast_s
                              (minus
                                (mult (S (S O))
                                  (plus (opsize (op_override pre) w) (S O)))
                                (S O)) (opsize (op_override pre) w) res))
                          (\lowerhalf ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (cast_s (opsize (op_override pre) w)
                                (minus
                                  (mult (S (S O))
                                    (plus (opsize (op_override pre) w) (S O)))
                                  (S O)) lowerhalf)) (\reextend ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (test
                                  (minus
                                    (mult (S (S O))
                                      (plus (opsize (op_override pre) w) (S
                                        O))) (S O)) Eq_op reextend res))
                              (\b0 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (not0 size1 b0)) (\flag ->
                                bind (unsafeCoerce conv_monad)
                                  (set_flag CF flag) (\x3 ->
                                  bind (unsafeCoerce conv_monad)
                                    (set_flag OF flag) (\x4 ->
                                    set2 seg lowerhalf op1)))))))))));
             None ->
              let {load = load_op pre w} in
              let {set2 = set_op pre w} in
              let {seg = get_segment_op2 pre DS op1 op2} in
              bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1)
                (\p1 ->
                bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op2)
                  (\p2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (cast_s (opsize (op_override pre) w)
                        (minus
                          (mult (S (S O))
                            (plus (opsize (op_override pre) w) (S O))) (S O))
                        p1)) (\p1ext ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce
                        (cast_s (opsize (op_override pre) w)
                          (minus
                            (mult (S (S O))
                              (plus (opsize (op_override pre) w) (S O))) (S
                            O)) p2)) (\p2ext ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (arith
                            (minus
                              (mult (S (S O))
                                (plus (opsize (op_override pre) w) (S O))) (S
                              O)) Mul_op p1ext p2ext)) (\res ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (cast_s
                              (minus
                                (mult (S (S O))
                                  (plus (opsize (op_override pre) w) (S O)))
                                (S O)) (opsize (op_override pre) w) res))
                          (\lowerhalf ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (cast_s (opsize (op_override pre) w)
                                (minus
                                  (mult (S (S O))
                                    (plus (opsize (op_override pre) w) (S O)))
                                  (S O)) lowerhalf)) (\reextend ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (test
                                  (minus
                                    (mult (S (S O))
                                      (plus (opsize (op_override pre) w) (S
                                        O))) (S O)) Eq_op reextend res))
                              (\b0 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (not0 size1 b0)) (\flag ->
                                bind (unsafeCoerce conv_monad)
                                  (set_flag CF flag) (\x3 ->
                                  bind (unsafeCoerce conv_monad)
                                    (set_flag OF flag) (\x4 ->
                                    set2 seg lowerhalf op1)))))))))))};
           None ->
            let {load = load_op pre w} in
            let {seg = get_segment_op pre DS op1} in
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce load seg (Reg_op EAX)) (\p1 ->
              bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1)
                (\p2 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (cast_s (opsize (op_override pre) w)
                      (minus
                        (mult (S (S O))
                          (plus (opsize (op_override pre) w) (S O))) (S O))
                      p1)) (\p1ext ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (cast_s (opsize (op_override pre) w)
                        (minus
                          (mult (S (S O))
                            (plus (opsize (op_override pre) w) (S O))) (S O))
                        p2)) (\p2ext ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce
                        (arith
                          (minus
                            (mult (S (S O))
                              (plus (opsize (op_override pre) w) (S O))) (S
                            O)) Mul_op p1ext p2ext)) (\res ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (cast_s
                            (minus
                              (mult (S (S O))
                                (plus (opsize (op_override pre) w) (S O))) (S
                              O)) (opsize (op_override pre) w) res))
                        (\lowerhalf ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (load_Z
                              (minus
                                (mult (S (S O))
                                  (plus (opsize (op_override pre) w) (S O)))
                                (S O))
                              (of_nat1
                                (plus (opsize (op_override pre) w) (S O)))))
                          (\shift ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith
                                (minus
                                  (mult (S (S O))
                                    (plus (opsize (op_override pre) w) (S O)))
                                  (S O)) Shr_op res shift)) (\res_shifted ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_s
                                  (minus
                                    (mult (S (S O))
                                      (plus (opsize (op_override pre) w) (S
                                        O))) (S O))
                                  (opsize (op_override pre) w) res_shifted))
                              (\upperhalf ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (load_Z (opsize (op_override pre) w) Z0))
                                (\zero2 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (load_Z (opsize (op_override pre) w)
                                      (max_unsigned
                                        (opsize (op_override pre) w))))
                                  (\max2 ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (test (opsize (op_override pre) w)
                                        Eq_op upperhalf zero2)) (\b0 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (test (opsize (op_override pre) w)
                                          Eq_op upperhalf max2)) (\b1 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (arith size1 Or_op b0 b1)) (\b2 ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce (not0 size1 b2))
                                          (\flag ->
                                          bind (unsafeCoerce conv_monad)
                                            (set_flag CF flag) (\x3 ->
                                            bind (unsafeCoerce conv_monad)
                                              (set_flag OF flag) (\x4 ->
                                              case w of {
                                               True ->
                                                let {set2 = set_op pre w} in
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (set2 seg lowerhalf (Reg_op
                                                    EAX)) (\x5 ->
                                                  set2 seg upperhalf (Reg_op
                                                    EDX));
                                               False ->
                                                iset_op16 seg
                                                  (eq_rect
                                                    (minus
                                                      (mult (S (S O))
                                                        (plus
                                                          (opsize
                                                            (op_override pre)
                                                            w) (S O))) (S O))
                                                    res size16) (Reg_op EAX)})))))))))))))))))}))))

conv_MUL :: Prefix -> Bool -> Operand -> Conv Unit
conv_MUL pre w op =
  let {seg = get_segment_op pre DS op} in
  bind (unsafeCoerce conv_monad) (undef_flag SF) (\x ->
    bind (unsafeCoerce conv_monad) (undef_flag ZF) (\x0 ->
      bind (unsafeCoerce conv_monad) (undef_flag AF) (\x1 ->
        bind (unsafeCoerce conv_monad) (undef_flag PF) (\x2 ->
          case op_override pre of {
           True ->
            case w of {
             True ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (iload_op16 seg op)) (\p1 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (iload_op16 seg (Reg_op EAX))) (\p2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (cast_u size16 size32 p1)) (\p1ext ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (cast_u size16 size32 p2)) (\p2ext ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (arith size32 Mul_op p1ext p2ext))
                        (\res ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (cast_u size32 size16 res))
                          (\res_lower ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (load_Z size32 (Zpos (XO (XO (XO (XO XH)))))))
                            (\sixteen ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (arith size32 Shru_op res sixteen))
                              (\res_shifted ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (cast_u size32 size16 res_shifted))
                                (\res_upper ->
                                bind (unsafeCoerce conv_monad)
                                  (iset_op16 seg res_lower (Reg_op EAX))
                                  (\x3 ->
                                  bind (unsafeCoerce conv_monad)
                                    (iset_op16 seg res_upper (Reg_op EDX))
                                    (\x4 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce (load_Z size16 Z0))
                                      (\zero2 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (test size16 Ltu_op zero2
                                            res_upper)) (\cf_test ->
                                        bind (unsafeCoerce conv_monad)
                                          (set_flag CF cf_test) (\x5 ->
                                          set_flag OF cf_test))))))))))))));
             False ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (iload_op8 seg op)) (\p1 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (iload_op8 seg (Reg_op EAX))) (\p2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (cast_u size8 size16 p1)) (\p1ext ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (cast_u size8 size16 p2)) (\p2ext ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (arith size16 Mul_op p1ext p2ext))
                        (\res ->
                        bind (unsafeCoerce conv_monad)
                          (iset_op16 seg res (Reg_op EAX)) (\x3 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (load_Z size16 (Zpos (XI (XI (XI (XI (XI (XI
                                (XI XH)))))))))) (\max2 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (test size16 Ltu_op max2 res))
                              (\cf_test ->
                              bind (unsafeCoerce conv_monad)
                                (set_flag CF cf_test) (\x4 ->
                                set_flag OF cf_test)))))))))};
           False ->
            case w of {
             True ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (iload_op32 seg op)) (\p1 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (iload_op32 seg (Reg_op EAX))) (\p2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (cast_u size32 (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        p1)) (\p1ext ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce
                        (cast_u size32 (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                          p2)) (\p2ext ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (arith (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                            Mul_op p1ext p2ext)) (\res ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (cast_u (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S
                              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                              size32 res)) (\res_lower ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (load_Z (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S
                                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                (Zpos (XO (XO (XO (XO (XO XH))))))))
                            (\thirtytwo ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (arith (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  Shru_op res thirtytwo)) (\res_shifted ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (cast_u (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S
                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    size32 res_shifted)) (\res_upper ->
                                bind (unsafeCoerce conv_monad)
                                  (iset_op32 seg res_lower (Reg_op EAX))
                                  (\x3 ->
                                  bind (unsafeCoerce conv_monad)
                                    (iset_op32 seg res_upper (Reg_op EDX))
                                    (\x4 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce (load_Z size32 Z0))
                                      (\zero2 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (test size32 Ltu_op zero2
                                            res_upper)) (\cf_test ->
                                        bind (unsafeCoerce conv_monad)
                                          (set_flag CF cf_test) (\x5 ->
                                          set_flag OF cf_test))))))))))))));
             False ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (iload_op8 seg op)) (\p1 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (iload_op8 seg (Reg_op EAX))) (\p2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (cast_u size8 size16 p1)) (\p1ext ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (cast_u size8 size16 p2)) (\p2ext ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (arith size16 Mul_op p1ext p2ext))
                        (\res ->
                        bind (unsafeCoerce conv_monad)
                          (iset_op16 seg res (Reg_op EAX)) (\x3 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (load_Z size16 (Zpos (XI (XI (XI (XI (XI (XI
                                (XI XH)))))))))) (\max2 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (test size16 Ltu_op max2 res))
                              (\cf_test ->
                              bind (unsafeCoerce conv_monad)
                                (set_flag CF cf_test) (\x4 ->
                                set_flag OF cf_test)))))))))}}))))

conv_shift :: Bit_vector_op -> Prefix -> Bool -> Operand -> Reg_or_immed ->
              Conv Unit
conv_shift shift pre w op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op pre DS op1} in
  bind (unsafeCoerce conv_monad) (undef_flag OF) (\x ->
    bind (unsafeCoerce conv_monad) (undef_flag CF) (\x0 ->
      bind (unsafeCoerce conv_monad) (undef_flag SF) (\x1 ->
        bind (unsafeCoerce conv_monad) (undef_flag ZF) (\x2 ->
          bind (unsafeCoerce conv_monad) (undef_flag PF) (\x3 ->
            bind (unsafeCoerce conv_monad) (undef_flag AF) (\x4 ->
              bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1)
                (\p1 ->
                bind (unsafeCoerce conv_monad)
                  (case op2 of {
                    Reg_ri r -> unsafeCoerce (iload_op8 seg (Reg_op r));
                    Imm_ri i ->
                     unsafeCoerce (load_int (S (S (S (S (S (S (S O))))))) i)})
                  (\p2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (load_Z size8 (Zpos (XI (XI (XI (XI XH))))))) (\mask ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (arith size8 And_op p2 mask)) (\p3 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (cast_u size8 (opsize (op_override pre) w) p3))
                        (\p2cast ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (arith (opsize (op_override pre) w) shift p1
                              p2cast)) (\p4 -> set2 seg p4 op1))))))))))))

conv_SHL :: Prefix -> Bool -> Operand -> Reg_or_immed -> Conv Unit
conv_SHL pre w op1 op2 =
  conv_shift Shl_op pre w op1 op2

conv_SAR :: Prefix -> Bool -> Operand -> Reg_or_immed -> Conv Unit
conv_SAR pre w op1 op2 =
  conv_shift Shr_op pre w op1 op2

conv_SHR :: Prefix -> Bool -> Operand -> Reg_or_immed -> Conv Unit
conv_SHR pre w op1 op2 =
  conv_shift Shru_op pre w op1 op2

conv_ROR :: Prefix -> Bool -> Operand -> Reg_or_immed -> Conv Unit
conv_ROR pre w op1 op2 =
  conv_shift Ror_op pre w op1 op2

conv_ROL :: Prefix -> Bool -> Operand -> Reg_or_immed -> Conv Unit
conv_ROL pre w op1 op2 =
  conv_shift Rol_op pre w op1 op2

conv_RCL :: Prefix -> Bool -> Operand -> Reg_or_immed -> Conv Unit
conv_RCL pre w op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op pre DS op1} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1) (\p1 ->
    bind (unsafeCoerce conv_monad)
      (case op2 of {
        Reg_ri r -> unsafeCoerce (iload_op8 seg (Reg_op r));
        Imm_ri i -> unsafeCoerce (load_int (S (S (S (S (S (S (S O))))))) i)})
      (\p2 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (load_Z size8 (Zpos (XI (XI (XI (XI XH))))))) (\mask ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size8 And_op p2 mask)) (\p3 ->
          bind (unsafeCoerce conv_monad)
            (case opsize (op_override pre) w of {
              O -> no_op;
              S n ->
               case n of {
                O -> no_op;
                S n0 ->
                 case n0 of {
                  O -> no_op;
                  S n1 ->
                   case n1 of {
                    O -> no_op;
                    S n2 ->
                     case n2 of {
                      O -> no_op;
                      S n3 ->
                       case n3 of {
                        O -> no_op;
                        S n4 ->
                         case n4 of {
                          O -> no_op;
                          S n5 ->
                           case n5 of {
                            O ->
                             bind (unsafeCoerce conv_monad)
                               (unsafeCoerce
                                 (load_Z size8 (Zpos (XI (XO (XO XH))))))
                               (\modmask ->
                               bind (unsafeCoerce conv_monad)
                                 (unsafeCoerce
                                   (arith size8 Modu_op p3 modmask)) (\p4 ->
                                 no_op));
                            S n6 ->
                             case n6 of {
                              O -> no_op;
                              S n7 ->
                               case n7 of {
                                O -> no_op;
                                S n8 ->
                                 case n8 of {
                                  O -> no_op;
                                  S n9 ->
                                   case n9 of {
                                    O -> no_op;
                                    S n10 ->
                                     case n10 of {
                                      O -> no_op;
                                      S n11 ->
                                       case n11 of {
                                        O -> no_op;
                                        S n12 ->
                                         case n12 of {
                                          O -> no_op;
                                          S n13 ->
                                           case n13 of {
                                            O ->
                                             bind (unsafeCoerce conv_monad)
                                               (unsafeCoerce
                                                 (load_Z size8 (Zpos (XI (XO
                                                   (XO (XO XH)))))))
                                               (\modmask ->
                                               bind (unsafeCoerce conv_monad)
                                                 (unsafeCoerce
                                                   (arith size8 Modu_op p3
                                                     modmask)) (\p4 -> no_op));
                                            S n14 -> no_op}}}}}}}}}}}}}}}})
            (\x ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce
                (cast_u size8 (plus (opsize (op_override pre) w) (S O)) p3))
              (\p2cast ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce
                  (cast_u (opsize (op_override pre) w)
                    (plus (opsize (op_override pre) w) (S O)) p1)) (\tmp ->
                bind (unsafeCoerce conv_monad) (unsafeCoerce (get_flag CF))
                  (\cf ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (cast_u size1 (plus (opsize (op_override pre) w) (S O))
                        cf)) (\cf0 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce
                        (load_Z (plus (opsize (op_override pre) w) (S O))
                          (of_nat1 (plus (opsize (op_override pre) w) (S O)))))
                      (\tt ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (arith (plus (opsize (op_override pre) w) (S O))
                            Shl_op cf0 tt)) (\cf1 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (arith (plus (opsize (op_override pre) w) (S O))
                              Or_op tmp cf1)) (\tmp0 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith
                                (plus (opsize (op_override pre) w) (S O))
                                Rol_op tmp0 p2cast)) (\tmp1 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_u
                                  (plus (opsize (op_override pre) w) (S O))
                                  (opsize (op_override pre) w) tmp1)) (\p4 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith
                                    (plus (opsize (op_override pre) w) (S O))
                                    Shr_op tmp1 tt)) (\cf2 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (cast_u
                                      (plus (opsize (op_override pre) w) (S
                                        O)) size1 cf2)) (\cf3 ->
                                  bind (unsafeCoerce conv_monad)
                                    (undef_flag OF) (\x0 ->
                                    bind (unsafeCoerce conv_monad)
                                      (set_flag CF cf3) (\x1 ->
                                      set2 seg p4 op1))))))))))))))))))

conv_RCR :: Prefix -> Bool -> Operand -> Reg_or_immed -> Conv Unit
conv_RCR pre w op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op pre DS op1} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1) (\p1 ->
    bind (unsafeCoerce conv_monad)
      (case op2 of {
        Reg_ri r -> unsafeCoerce (iload_op8 seg (Reg_op r));
        Imm_ri i -> unsafeCoerce (load_int (S (S (S (S (S (S (S O))))))) i)})
      (\p2 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (load_Z size8 (Zpos (XI (XI (XI (XI XH))))))) (\mask ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size8 And_op p2 mask)) (\p3 ->
          bind (unsafeCoerce conv_monad)
            (case opsize (op_override pre) w of {
              O -> no_op;
              S n ->
               case n of {
                O -> no_op;
                S n0 ->
                 case n0 of {
                  O -> no_op;
                  S n1 ->
                   case n1 of {
                    O -> no_op;
                    S n2 ->
                     case n2 of {
                      O -> no_op;
                      S n3 ->
                       case n3 of {
                        O -> no_op;
                        S n4 ->
                         case n4 of {
                          O -> no_op;
                          S n5 ->
                           case n5 of {
                            O ->
                             bind (unsafeCoerce conv_monad)
                               (unsafeCoerce
                                 (load_Z size8 (Zpos (XI (XO (XO XH))))))
                               (\modmask ->
                               bind (unsafeCoerce conv_monad)
                                 (unsafeCoerce
                                   (arith size8 Modu_op p3 modmask)) (\p4 ->
                                 no_op));
                            S n6 ->
                             case n6 of {
                              O -> no_op;
                              S n7 ->
                               case n7 of {
                                O -> no_op;
                                S n8 ->
                                 case n8 of {
                                  O -> no_op;
                                  S n9 ->
                                   case n9 of {
                                    O -> no_op;
                                    S n10 ->
                                     case n10 of {
                                      O -> no_op;
                                      S n11 ->
                                       case n11 of {
                                        O -> no_op;
                                        S n12 ->
                                         case n12 of {
                                          O -> no_op;
                                          S n13 ->
                                           case n13 of {
                                            O ->
                                             bind (unsafeCoerce conv_monad)
                                               (unsafeCoerce
                                                 (load_Z size8 (Zpos (XI (XO
                                                   (XO (XO XH)))))))
                                               (\modmask ->
                                               bind (unsafeCoerce conv_monad)
                                                 (unsafeCoerce
                                                   (arith size8 Modu_op p3
                                                     modmask)) (\p4 -> no_op));
                                            S n14 -> no_op}}}}}}}}}}}}}}}})
            (\x ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce
                (cast_u size8 (plus (opsize (op_override pre) w) (S O)) p3))
              (\p2cast ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce
                  (load_Z (plus (opsize (op_override pre) w) (S O)) (Zpos
                    XH))) (\oneshift ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (cast_u (opsize (op_override pre) w)
                      (plus (opsize (op_override pre) w) (S O)) p1)) (\tmp ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce
                      (arith (plus (opsize (op_override pre) w) (S O)) Shl_op
                        tmp oneshift)) (\tmp0 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (get_flag CF)) (\cf ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (cast_u size1
                            (plus (opsize (op_override pre) w) (S O)) cf))
                        (\cf0 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (arith (plus (opsize (op_override pre) w) (S O))
                              Or_op tmp0 cf0)) (\tmp1 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith
                                (plus (opsize (op_override pre) w) (S O))
                                Ror_op tmp1 p2cast)) (\tmp2 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_u
                                  (plus (opsize (op_override pre) w) (S O))
                                  size1 tmp2)) (\cf1 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith
                                    (plus (opsize (op_override pre) w) (S O))
                                    Shr_op tmp2 oneshift)) (\p4 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (cast_u
                                      (plus (opsize (op_override pre) w) (S
                                        O)) (opsize (op_override pre) w) p4))
                                  (\p5 ->
                                  bind (unsafeCoerce conv_monad)
                                    (undef_flag OF) (\x0 ->
                                    bind (unsafeCoerce conv_monad)
                                      (set_flag CF cf1) (\x1 ->
                                      set2 seg p5 op1))))))))))))))))))

conv_SHLD :: Prefix -> Operand -> Register -> Reg_or_immed -> Conv Unit
conv_SHLD pre op1 r ri =
  let {load = load_op pre True} in
  let {set2 = set_op pre True} in
  let {seg = get_segment_op pre DS op1} in
  bind (unsafeCoerce conv_monad)
    (case ri of {
      Reg_ri r2 -> unsafeCoerce (iload_op8 seg (Reg_op r2));
      Imm_ri i -> unsafeCoerce (load_int (S (S (S (S (S (S (S O))))))) i)})
    (\count ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (load_Z size8 (Zpos (XO (XO (XO (XO (XO XH))))))))
      (\thirtytwo ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith size8 Modu_op count thirtytwo)) (\count0 ->
        bind (unsafeCoerce conv_monad) (undef_flag CF) (\x ->
          bind (unsafeCoerce conv_monad) (undef_flag SF) (\x0 ->
            bind (unsafeCoerce conv_monad) (undef_flag ZF) (\x1 ->
              bind (unsafeCoerce conv_monad) (undef_flag PF) (\x2 ->
                bind (unsafeCoerce conv_monad) (undef_flag AF) (\x3 ->
                  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1)
                    (\p1 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce load seg (Reg_op r)) (\p2 ->
                      bind (unsafeCoerce conv_monad)
                        (case op_override pre of {
                          True ->
                           unsafeCoerce
                             (load_Z (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S
                               O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                               (Zpos (XO (XO (XO (XO XH))))));
                          False ->
                           unsafeCoerce
                             (load_Z (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                               (S (S (S (S (S
                               O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                               (Zpos (XO (XO (XO (XO (XO XH)))))))})
                        (\shiftup ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (cast_u (opsize (op_override pre) True) (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S
                              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                              p1)) (\wide_p1 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S
                                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                Shl_op wide_p1 shiftup)) (\wide_p2 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_u (opsize (op_override pre) True) (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  p2)) (\wide_p3 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S
                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    Or_op wide_p2 wide_p3)) (\combined ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (cast_u size8 (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S (S (S (S (S (S
                                      (S (S
                                      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      count0)) (\wide_count ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (arith (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S
                                        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        Shl_op combined wide_count))
                                    (\shifted ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (arith (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S
                                          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          Shru_op shifted shiftup))
                                      (\shifted0 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (cast_u (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S
                                            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                            (opsize (op_override pre) True)
                                            shifted0)) (\newdest0 ->
                                        bind (unsafeCoerce conv_monad)
                                          (case op_override pre of {
                                            True ->
                                             unsafeCoerce
                                               (load_Z size8 (Zpos (XO (XO
                                                 (XO (XO XH))))));
                                            False ->
                                             unsafeCoerce
                                               (load_Z size8 (Zpos (XO (XO
                                                 (XO (XO (XO XH)))))))})
                                          (\maxcount ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (test size8 Ltu_op maxcount
                                                count0)) (\guard1 ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (test size8 Eq_op maxcount
                                                  count0)) (\guard2 ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (arith size1 Or_op guard1
                                                    guard2)) (\guard ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (choose
                                                      (opsize
                                                        (op_override pre)
                                                        True))) (\newdest1 ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (if_exp
                                                        (opsize
                                                          (op_override pre)
                                                          True) guard
                                                        newdest1 newdest0))
                                                    (\newdest ->
                                                    set2 seg newdest op1)))))))))))))))))))))))))

conv_SHRD :: Prefix -> Operand -> Register -> Reg_or_immed -> Conv Unit
conv_SHRD pre op1 r ri =
  let {load = load_op pre True} in
  let {set2 = set_op pre True} in
  let {seg = get_segment_op pre DS op1} in
  bind (unsafeCoerce conv_monad)
    (case ri of {
      Reg_ri r2 -> unsafeCoerce (iload_op8 seg (Reg_op r2));
      Imm_ri i -> unsafeCoerce (load_int (S (S (S (S (S (S (S O))))))) i)})
    (\count ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (load_Z size8 (Zpos (XO (XO (XO (XO (XO XH))))))))
      (\thirtytwo ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith size8 Modu_op count thirtytwo)) (\count0 ->
        bind (unsafeCoerce conv_monad) (undef_flag CF) (\x ->
          bind (unsafeCoerce conv_monad) (undef_flag SF) (\x0 ->
            bind (unsafeCoerce conv_monad) (undef_flag ZF) (\x1 ->
              bind (unsafeCoerce conv_monad) (undef_flag PF) (\x2 ->
                bind (unsafeCoerce conv_monad) (undef_flag AF) (\x3 ->
                  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1)
                    (\p1 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce load seg (Reg_op r)) (\p2 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce
                          (cast_u (opsize (op_override pre) True) (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S
                            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                            p1)) (\wide_p1 ->
                        bind (unsafeCoerce conv_monad)
                          (case op_override pre of {
                            True ->
                             unsafeCoerce
                               (load_Z (S (S (S (S (S (S (S (S (S (S (S (S (S
                                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                 (S (S (S (S (S
                                 O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                 (Zpos (XO (XO (XO (XO XH))))));
                            False ->
                             unsafeCoerce
                               (load_Z (S (S (S (S (S (S (S (S (S (S (S (S (S
                                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                 (S (S (S (S (S
                                 O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                 (Zpos (XO (XO (XO (XO (XO XH)))))))})
                          (\shiftup ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (cast_u (opsize (op_override pre) True) (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                (S
                                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                p2)) (\wide_p2 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (arith (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  Shl_op wide_p2 shiftup)) (\wide_p3 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S
                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    Or_op wide_p1 wide_p3)) (\combined ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (cast_u size8 (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S (S (S (S (S (S
                                      (S (S (S (S (S (S (S (S (S (S (S (S (S
                                      (S (S
                                      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      count0)) (\wide_count ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (arith (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S
                                        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        Shru_op combined wide_count))
                                    (\shifted ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (cast_u (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S
                                          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          (opsize (op_override pre) True)
                                          shifted)) (\newdest0 ->
                                      bind (unsafeCoerce conv_monad)
                                        (case op_override pre of {
                                          True ->
                                           unsafeCoerce
                                             (load_Z size8 (Zpos (XO (XO (XO
                                               (XO XH))))));
                                          False ->
                                           unsafeCoerce
                                             (load_Z size8 (Zpos (XO (XO (XO
                                               (XO (XO XH)))))))})
                                        (\maxcount ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (test size8 Ltu_op maxcount
                                              count0)) (\guard1 ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (test size8 Eq_op maxcount
                                                count0)) (\guard2 ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (arith size1 Or_op guard1
                                                  guard2)) (\guard ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (choose
                                                    (opsize (op_override pre)
                                                      True))) (\newdest1 ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (if_exp
                                                      (opsize
                                                        (op_override pre)
                                                        True) guard newdest1
                                                      newdest0)) (\newdest ->
                                                  set2 seg newdest op1))))))))))))))))))))))))

get_AH :: Conv Rtl_exp
get_AH =
  iload_op8 DS (Reg_op ESP)

set_AH :: Rtl_exp -> Conv Unit
set_AH v =
  iset_op8 DS v (Reg_op ESP)

get_AL :: Conv Rtl_exp
get_AL =
  iload_op8 DS (Reg_op EAX)

set_AL :: Rtl_exp -> Conv Unit
set_AL v =
  iset_op8 DS v (Reg_op EAX)

conv_AAA_AAS :: Bit_vector_op -> Conv Unit
conv_AAA_AAS op1 =
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce (load_Z size8 (Zpos (XI (XO (XO XH)))))) (\pnine ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (load_Z size8 (Zpos (XI (XI (XI XH)))))) (\p0Fmask ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (get_flag AF)) (\paf ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce get_AL) (\pal ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (arith size8 And_op pal p0Fmask)) (\digit1 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (test size8 Lt_op pnine digit1)) (\cond1 ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (arith size1 Or_op cond1 paf)) (\cond ->
                bind (unsafeCoerce conv_monad) (unsafeCoerce get_AH) (\pah ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (load_Z size1 Z0)) (\pfalse ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (copy_ps size8 pah)) (\v_ah0 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (copy_ps size1 pfalse)) (\v_af0 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (copy_ps size1 pfalse)) (\v_cf0 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (arith size8 And_op pal p0Fmask))
                            (\v_al0 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (load_Z size8 (Zpos (XO (XI XH))))) (\psix ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (load_Z size8 (Zpos XH)))
                                (\pone ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (load_Z size1 (Zpos XH)))
                                  (\ptrue ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce (arith size8 op1 pal psix))
                                    (\pal_c ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (arith size8 And_op pal_c p0Fmask))
                                      (\pal_cmask ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (if_exp size8 cond pal_cmask v_al0))
                                        (\v_al ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce get_AH) (\pah0 ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (arith size8 op1 pah0 pone))
                                            (\pah_c ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (if_exp size8 cond pah_c
                                                  v_ah0)) (\v_ah ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (if_exp size1 cond ptrue
                                                    v_af0)) (\v_af ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (if_exp size1 cond ptrue
                                                      v_cf0)) (\v_cf ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (set_AL v_al) (\x ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (set_AH v_ah) (\x0 ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (set_flag AF v_af)
                                                        (\x1 ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (set_flag CF v_cf)
                                                          (\x2 ->
                                                          bind
                                                            (unsafeCoerce
                                                              conv_monad)
                                                            (undef_flag OF)
                                                            (\x3 ->
                                                            bind
                                                              (unsafeCoerce
                                                                conv_monad)
                                                              (undef_flag SF)
                                                              (\x4 ->
                                                              bind
                                                                (unsafeCoerce
                                                                  conv_monad)
                                                                (undef_flag
                                                                  ZF) (\x5 ->
                                                                undef_flag PF)))))))))))))))))))))))))))))))

conv_AAD :: Conv Unit
conv_AAD =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_AL) (\pal ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce get_AH) (\pah ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (load_Z size8 (Zpos (XO (XI (XO XH)))))) (\pten ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce
            (load_Z size8 (Zpos (XI (XI (XI (XI (XI (XI (XI XH))))))))))
          (\pFF ->
          bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size8 Z0))
            (\pzero ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (arith size8 Mul_op pah pten)) (\tensval ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (arith size8 Add_op pal tensval)) (\pal_c ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (arith size8 And_op pal_c pFF))
                  (\pal_cmask ->
                  bind (unsafeCoerce conv_monad) (set_AL pal_cmask) (\x ->
                    bind (unsafeCoerce conv_monad) (set_AH pzero) (\x0 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (test size8 Eq_op pal_cmask pzero))
                        (\b0 ->
                        bind (unsafeCoerce conv_monad) (set_flag ZF b0)
                          (\x1 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (test size8 Lt_op pal_cmask pzero))
                            (\b1 ->
                            bind (unsafeCoerce conv_monad) (set_flag SF b1)
                              (\x2 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (compute_parity size8 pal_cmask)) (\b2 ->
                                bind (unsafeCoerce conv_monad)
                                  (set_flag PF b2) (\x3 ->
                                  bind (unsafeCoerce conv_monad)
                                    (undef_flag OF) (\x4 ->
                                    bind (unsafeCoerce conv_monad)
                                      (undef_flag AF) (\x5 -> undef_flag CF))))))))))))))))))

conv_AAM :: Conv Unit
conv_AAM =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_AL) (\pal ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (load_Z size8 (Zpos (XO (XI (XO XH)))))) (\pten ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith size8 Divu_op pal pten)) (\digit1 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size8 Modu_op pal pten)) (\digit2 ->
          bind (unsafeCoerce conv_monad) (set_AH digit1) (\x ->
            bind (unsafeCoerce conv_monad) (set_AL digit2) (\x0 ->
              bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size8 Z0))
                (\pzero ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (test size8 Eq_op digit2 pzero)) (\b0 ->
                  bind (unsafeCoerce conv_monad) (set_flag ZF b0) (\x1 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (test size8 Lt_op digit2 pzero)) (\b1 ->
                      bind (unsafeCoerce conv_monad) (set_flag SF b1) (\x2 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (compute_parity size8 digit2))
                          (\b2 ->
                          bind (unsafeCoerce conv_monad) (set_flag PF b2)
                            (\x3 ->
                            bind (unsafeCoerce conv_monad) (undef_flag OF)
                              (\x4 ->
                              bind (unsafeCoerce conv_monad) (undef_flag AF)
                                (\x5 -> undef_flag CF)))))))))))))))

testcarryAdd :: Nat -> Rtl_exp -> Rtl_exp -> Rtl_exp -> Conv Rtl_exp
testcarryAdd s p1 p2 p3 =
  bind (unsafeCoerce conv_monad) (test s Ltu_op p3 p1) (\b0 ->
    bind (unsafeCoerce conv_monad) (test s Ltu_op p3 p2) (\b1 ->
      arith size1 Or_op b0 b1))

testcarrySub :: Nat -> Rtl_exp -> Rtl_exp -> Rtl_exp -> Conv Rtl_exp
testcarrySub s p1 p2 p3 =
  test s Ltu_op p1 p2

conv_DAA_DAS :: Bit_vector_op -> (Rtl_exp -> Rtl_exp -> Rtl_exp -> Conv
                Rtl_exp) -> Conv Unit
conv_DAA_DAS op1 tester =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (choose size8)) (\pal ->
    bind (unsafeCoerce conv_monad) (set_AL pal) (\x ->
      bind (unsafeCoerce conv_monad) (undef_flag CF) (\x0 ->
        bind (unsafeCoerce conv_monad) (undef_flag AF) (\x1 ->
          bind (unsafeCoerce conv_monad) (undef_flag SF) (\x2 ->
            bind (unsafeCoerce conv_monad) (undef_flag ZF) (\x3 ->
              bind (unsafeCoerce conv_monad) (undef_flag PF) (\x4 ->
                undef_flag OF)))))))

conv_logical_op :: Bool -> Bit_vector_op -> Prefix -> Bool -> Operand ->
                   Operand -> Conv Unit
conv_logical_op do_effect b pre w op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op2 pre DS op1 op2} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1) (\p0 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op2) (\p1 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith (opsize (op_override pre) w) b p0 p1)) (\p2 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (load_Z (opsize (op_override pre) w) Z0)) (\zero2 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (test (opsize (op_override pre) w) Eq_op zero2 p2))
            (\zfp ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce
                (test (opsize (op_override pre) w) Lt_op p2 zero2)) (\sfp ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce
                  (compute_parity (opsize (op_override pre) w) p2)) (\pfp ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (load_Z size1 Z0)) (\zero3 ->
                  bind (unsafeCoerce conv_monad) (set_flag OF zero3) (\x ->
                    bind (unsafeCoerce conv_monad) (set_flag CF zero3)
                      (\x0 ->
                      bind (unsafeCoerce conv_monad) (set_flag ZF zfp)
                        (\x1 ->
                        bind (unsafeCoerce conv_monad) (set_flag SF sfp)
                          (\x2 ->
                          bind (unsafeCoerce conv_monad) (set_flag PF pfp)
                            (\x3 ->
                            bind (unsafeCoerce conv_monad) (undef_flag AF)
                              (\x4 ->
                              case do_effect of {
                               True -> set2 seg p2 op1;
                               False -> no_op}))))))))))))))

conv_AND :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_AND p w op1 op2 =
  conv_logical_op True And_op p w op1 op2

conv_OR :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_OR p w op1 op2 =
  conv_logical_op True Or_op p w op1 op2

conv_XOR :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_XOR p w op1 op2 =
  conv_logical_op True Xor_op p w op1 op2

conv_TEST :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_TEST p w op1 op2 =
  conv_logical_op False And_op p w op1 op2

conv_NOT :: Prefix -> Bool -> Operand -> Conv Unit
conv_NOT pre w op =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op pre DS op} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op) (\p0 ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce
        (load_Z (opsize (op_override pre) w) (max_unsigned size32)))
      (\max_unsigned0 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce
          (arith (opsize (op_override pre) w) Xor_op p0 max_unsigned0))
        (\p1 -> set2 seg p1 op)))

conv_POP :: Prefix -> Operand -> Conv Unit
conv_POP pre op =
  let {seg = SS} in
  let {set2 = set_op pre True seg} in
  let {loadmem = load_mem pre True seg} in
  let {
   espoffset = case op_override pre of {
                True -> Zpos (XO XH);
                False -> Zpos (XO (XO XH))}}
  in
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg ESP)) (\oldesp ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce loadmem oldesp) (\value ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size32 espoffset))
        (\offset ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size32 Add_op oldesp offset)) (\newesp ->
          bind (unsafeCoerce conv_monad) (set_reg newesp ESP) (\x ->
            set2 value op)))))

conv_POPA :: Prefix -> Conv Unit
conv_POPA pre =
  let {
   espoffset = case op_override pre of {
                True -> Zpos (XO XH);
                False -> Zpos (XO (XO XH))}}
  in
  let {poprtl = \r -> conv_POP pre (Reg_op r)} in
  bind (unsafeCoerce conv_monad) (poprtl EDI) (\x ->
    bind (unsafeCoerce conv_monad) (poprtl ESI) (\x0 ->
      bind (unsafeCoerce conv_monad) (poprtl EBP) (\x1 ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg ESP))
          (\oldesp ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (load_Z size32 espoffset)) (\offset ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (arith size32 Add_op oldesp offset)) (\newesp ->
              bind (unsafeCoerce conv_monad) (set_reg newesp ESP) (\x2 ->
                bind (unsafeCoerce conv_monad) (poprtl EBX) (\x3 ->
                  bind (unsafeCoerce conv_monad) (poprtl EDX) (\x4 ->
                    bind (unsafeCoerce conv_monad) (poprtl ECX) (\x5 ->
                      poprtl EAX))))))))))

conv_PUSH :: Prefix -> Bool -> Operand -> Conv Unit
conv_PUSH pre w op =
  let {seg = SS} in
  let {load = load_op pre True seg} in
  let {setmem = set_mem pre True seg} in
  let {
   espoffset = case op_override pre of {
                True -> Zpos (XO XH);
                False -> Zpos (XO (XO XH))}}
  in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load op) (\p0 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg ESP)) (\oldesp ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size32 espoffset))
        (\offset ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size32 Sub_op oldesp offset)) (\newesp ->
          bind (unsafeCoerce conv_monad) (setmem p0 newesp) (\x ->
            set_reg newesp ESP)))))

conv_PUSH_pseudo :: Prefix -> Bool -> Rtl_exp -> Conv Unit
conv_PUSH_pseudo pre w pr =
  let {seg = SS} in
  let {setmem = set_mem pre w seg} in
  let {
   espoffset = case op_override pre of {
                True ->
                 case w of {
                  True -> Zpos (XO XH);
                  False -> Zpos XH};
                False ->
                 case w of {
                  True -> Zpos (XO (XO XH));
                  False -> Zpos XH}}}
  in
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg ESP)) (\oldesp ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size32 espoffset))
      (\offset ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith size32 Sub_op oldesp offset)) (\newesp ->
        bind (unsafeCoerce conv_monad) (setmem pr newesp) (\x ->
          set_reg newesp ESP))))

conv_PUSHA :: Prefix -> Conv Unit
conv_PUSHA pre =
  let {load = load_op pre True SS} in
  let {pushrtl = \r -> conv_PUSH pre True (Reg_op r)} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load (Reg_op ESP)) (\oldesp ->
    bind (unsafeCoerce conv_monad) (pushrtl EAX) (\x ->
      bind (unsafeCoerce conv_monad) (pushrtl ECX) (\x0 ->
        bind (unsafeCoerce conv_monad) (pushrtl EDX) (\x1 ->
          bind (unsafeCoerce conv_monad) (pushrtl EBX) (\x2 ->
            bind (unsafeCoerce conv_monad) (conv_PUSH_pseudo pre True oldesp)
              (\x3 ->
              bind (unsafeCoerce conv_monad) (pushrtl EBP) (\x4 ->
                bind (unsafeCoerce conv_monad) (pushrtl ESI) (\x5 ->
                  pushrtl EDI))))))))

get_and_place :: Nat -> Rtl_exp -> Z -> Flag -> Conv Rtl_exp
get_and_place t dst pos fl =
  bind (unsafeCoerce conv_monad) (get_flag fl) (\fl0 ->
    bind (unsafeCoerce conv_monad) (load_Z t pos) (\pos0 ->
      bind (unsafeCoerce conv_monad) (cast_u size1 t fl0) (\byt ->
        bind (unsafeCoerce conv_monad) (arith t Shl_op byt pos0) (\tmp ->
          arith t Or_op dst tmp))))

conv_POP_pseudo :: Prefix -> Conv Rtl_exp
conv_POP_pseudo pre =
  let {seg = SS} in
  let {loadmem = load_mem pre True seg} in
  let {
   espoffset = case op_override pre of {
                True -> Zpos (XO XH);
                False -> Zpos (XO (XO XH))}}
  in
  bind (unsafeCoerce conv_monad) (load_reg ESP) (\oldesp ->
    bind (unsafeCoerce conv_monad) (load_Z size32 espoffset) (\offset ->
      bind (unsafeCoerce conv_monad) (arith size32 Add_op oldesp offset)
        (\newesp ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce (set_reg newesp ESP))
          (\x -> loadmem oldesp))))

extract_and_set :: Nat -> Rtl_exp -> Z -> Flag -> Conv Unit
extract_and_set t value pos fl =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z t (Zpos XH)))
    (\one2 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z t pos)) (\pos0 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith t Shr_op value pos0)) (\tmp ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith t And_op tmp one2)) (\tmp0 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (test t Eq_op one2 tmp0)) (\b -> set_flag fl b)))))

conv_JMP :: Prefix -> Bool -> Bool -> Operand -> (Option Selector) -> Conv
            Unit
conv_JMP pre near absolute op sel =
  let {seg = get_segment_op pre DS op} in
  case near of {
   True ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (iload_op32 seg op))
      (\disp ->
      bind (unsafeCoerce conv_monad)
        (case absolute of {
          True -> unsafeCoerce (load_Z size32 Z0);
          False -> unsafeCoerce get_pc}) (\base ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size32 Add_op base disp)) (\newpc ->
          set_pc0 newpc)));
   False -> raise_error}

conv_Jcc :: Prefix -> Condition_type -> Int32 -> Conv Unit
conv_Jcc pre ct disp =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_cc ct)) (\guard ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce get_pc) (\oldpc ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce
          (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))) disp)) (\pdisp ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size32 Add_op oldpc pdisp)) (\newpc ->
          if_set_loc guard size32 newpc Pc_loc))))

conv_CALL :: Prefix -> Bool -> Bool -> Operand -> (Option Selector) -> Conv
             Unit
conv_CALL pre near absolute op sel =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_pc) (\oldpc ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg ESP)) (\oldesp ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (load_Z size32 (Zpos (XO (XO XH))))) (\four0 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size32 Sub_op oldesp four0)) (\newesp ->
          bind (unsafeCoerce conv_monad) (set_mem32 SS oldpc newesp) (\x ->
            bind (unsafeCoerce conv_monad) (set_reg newesp ESP) (\x0 ->
              conv_JMP pre near absolute op sel))))))

conv_RET :: Prefix -> Bool -> (Option Int16) -> Conv Unit
conv_RET pre same_segment disp =
  case same_segment of {
   True ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg ESP)) (\oldesp ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (load_mem32 SS oldesp))
        (\value ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (load_Z size32 (Zpos (XO (XO XH))))) (\four0 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (arith size32 Add_op oldesp four0)) (\newesp ->
            bind (unsafeCoerce conv_monad)
              (case disp of {
                Some imm ->
                 bind (unsafeCoerce conv_monad)
                   (unsafeCoerce
                     (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O))))))))))))))) imm)) (\imm0 ->
                   bind (unsafeCoerce conv_monad)
                     (unsafeCoerce
                       (cast_u (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         O))))))))))))))) size32 imm0)) (\imm1 ->
                     bind (unsafeCoerce conv_monad)
                       (unsafeCoerce (arith size32 Add_op newesp imm1))
                       (\newesp2 -> set_reg newesp2 ESP)));
                None -> set_reg newesp ESP}) (\x -> set_pc0 value)))));
   False -> raise_error}

conv_LEAVE :: Prefix -> Conv Unit
conv_LEAVE pre =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg EBP)) (\ebp_val ->
    bind (unsafeCoerce conv_monad) (set_reg ebp_val ESP) (\x ->
      conv_POP pre (Reg_op EBP)))

conv_LOOP :: Prefix -> Bool -> Bool -> Int8 -> Conv Unit
conv_LOOP pre flagged testz disp =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 (Zpos XH)))
    (\ptrue ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg ECX)) (\p0 ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size32 (Zpos XH)))
        (\p1 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size32 Sub_op p0 p1)) (\p2 ->
          bind (unsafeCoerce conv_monad) (set_reg p2 ECX) (\x ->
            bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size32 Z0))
              (\pzero ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (test size32 Eq_op p2 pzero)) (\pcz ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (arith size1 Xor_op pcz ptrue)) (\pcnz ->
                  bind (unsafeCoerce conv_monad) (unsafeCoerce (get_flag ZF))
                    (\pzf ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (arith size1 Xor_op pzf ptrue)) (\pnzf ->
                      bind (unsafeCoerce conv_monad)
                        (case flagged of {
                          True ->
                           case testz of {
                            True ->
                             unsafeCoerce (arith size1 And_op pzf pcnz);
                            False ->
                             unsafeCoerce (arith size1 And_op pnzf pcnz)};
                          False -> unsafeCoerce (arith size1 Or_op pcnz pcnz)})
                        (\bcond ->
                        bind (unsafeCoerce conv_monad) (unsafeCoerce get_pc)
                          (\eip0 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (load_int (S (S (S (S (S (S (S O))))))) disp))
                            (\doffset0 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_s (S (S (S (S (S (S (S O))))))) size32
                                  doffset0)) (\doffset1 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (arith size32 Add_op eip0 doffset1))
                                (\eip1 ->
                                bind (unsafeCoerce conv_monad)
                                  (case op_override pre of {
                                    True ->
                                     unsafeCoerce
                                       (load_Z size32 (Zpos (XO (XO (XO (XO
                                         (XO (XO (XO (XO (XO (XO (XO (XO (XO
                                         (XO (XO (XO XH))))))))))))))))));
                                    False ->
                                     unsafeCoerce
                                       (load_Z size32 (opp (Zpos XH)))})
                                  (\eipmask ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (arith size32 And_op eip1 eipmask))
                                    (\eip2 ->
                                    if_set_loc bcond size32 eip2 Pc_loc)))))))))))))))))

conv_BS_aux :: Nat -> Bool -> Nat -> Rtl_exp -> Conv Rtl_exp
conv_BS_aux s d n op =
  let {
   curr_int = case d of {
               True -> repr s (of_nat1 (minus s n));
               False -> repr s (of_nat1 n)}}
  in
  case n of {
   O -> load_int s curr_int;
   S n' ->
    bind (unsafeCoerce conv_monad) (load_int s curr_int) (\bcount ->
      bind (unsafeCoerce conv_monad) (conv_BS_aux s d n' op) (\rec0 ->
        bind (unsafeCoerce conv_monad) (arith s Shru_op op bcount) (\ps ->
          bind (unsafeCoerce conv_monad) (cast_u s size1 ps) (\curr_bit ->
            bind (unsafeCoerce conv_monad) (load_int s curr_int) (\rec1 ->
              if_exp s curr_bit rec1 rec0)))))}

conv_BS :: Bool -> Prefix -> Operand -> Operand -> Conv Unit
conv_BS d pre op1 op2 =
  let {seg = get_segment_op2 pre DS op1 op2} in
  bind (unsafeCoerce conv_monad) (undef_flag AF) (\x ->
    bind (unsafeCoerce conv_monad) (undef_flag CF) (\x0 ->
      bind (unsafeCoerce conv_monad) (undef_flag SF) (\x1 ->
        bind (unsafeCoerce conv_monad) (undef_flag OF) (\x2 ->
          bind (unsafeCoerce conv_monad) (undef_flag PF) (\x3 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (iload_op32 seg op1)) (\des ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (iload_op32 seg op2)) (\src ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (load_Z size32 Z0)) (\zero2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (test size32 Eq_op src zero2)) (\zf ->
                    bind (unsafeCoerce conv_monad) (set_flag ZF zf) (\x4 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (conv_BS_aux size32 d size32 src))
                        (\res0 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (choose size32)) (\res1 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (if_exp size32 zf res1 res0))
                            (\res -> iset_op32 seg res op1)))))))))))))

conv_BSF :: Prefix -> Operand -> Operand -> Conv Unit
conv_BSF p op1 op2 =
  conv_BS True p op1 op2

conv_BSR :: Prefix -> Operand -> Operand -> Conv Unit
conv_BSR p op1 op2 =
  conv_BS False p op1 op2

get_Bit :: Nat -> Rtl_exp -> Rtl_exp -> Conv Rtl_exp
get_Bit s pb poff =
  bind (unsafeCoerce conv_monad) (load_Z s (Zpos XH)) (\omask ->
    bind (unsafeCoerce conv_monad) (arith s Shr_op pb poff) (\shr_pb ->
      bind (unsafeCoerce conv_monad) (arith s And_op shr_pb omask)
        (\mask_pb -> cast_u s size1 mask_pb)))

modify_Bit :: Nat -> Rtl_exp -> Rtl_exp -> Rtl_exp -> Conv Rtl_exp
modify_Bit s value poff bitval =
  bind (unsafeCoerce conv_monad) (load_Z s (Zpos XH)) (\obit ->
    bind (unsafeCoerce conv_monad) (arith s Shl_op obit poff)
      (\one_shifted ->
      bind (unsafeCoerce conv_monad) (not0 s one_shifted)
        (\inv_one_shifted ->
        bind (unsafeCoerce conv_monad) (cast_u size1 s bitval)
          (\bitvalword ->
          bind (unsafeCoerce conv_monad) (arith s Shl_op bitvalword poff)
            (\bit_shifted ->
            bind (unsafeCoerce conv_monad)
              (arith s And_op value inv_one_shifted) (\newval ->
              arith s Or_op newval bit_shifted))))))

set_Bit :: Prefix -> Bool -> Operand -> Rtl_exp -> Rtl_exp -> Conv Unit
set_Bit pre w op poff bitval =
  let {seg = get_segment_op pre DS op} in
  let {load = load_op pre w seg} in
  let {set2 = set_op pre w seg} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load op) (\value ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce
        (modify_Bit (opsize (op_override pre) w) value poff bitval))
      (\newvalue -> set2 newvalue op))

set_Bit_mem :: Prefix -> Bool -> Operand -> Rtl_exp -> Rtl_exp -> Rtl_exp ->
               Conv Unit
set_Bit_mem pre w op addr poff bitval =
  let {seg = get_segment_op pre DS op} in
  let {load = load_mem pre w seg} in
  let {set2 = set_mem pre w seg} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load addr) (\value ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce
        (modify_Bit (opsize (op_override pre) w) value poff bitval))
      (\newvalue ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (copy_ps size32 addr))
        (\newaddr -> set2 newvalue newaddr)))

fbit :: Bool -> Bool -> Rtl_exp -> Conv Rtl_exp
fbit param1 param2 v =
  case param1 of {
   True ->
    case param2 of {
     True -> load_Z size1 (Zpos XH);
     False -> load_Z size1 Z0};
   False ->
    case param2 of {
     True -> copy_ps size1 v;
     False -> not0 size1 v}}

conv_BT :: Bool -> Bool -> Prefix -> Operand -> Operand -> Conv Unit
conv_BT param1 param2 pre op1 regimm =
  let {seg = get_segment_op pre DS op1} in
  let {load = load_op pre True seg} in
  let {lmem0 = load_mem pre True seg} in
  let {opsz = opsize (op_override pre) True} in
  bind (unsafeCoerce conv_monad) (undef_flag OF) (\x ->
    bind (unsafeCoerce conv_monad) (undef_flag SF) (\x0 ->
      bind (unsafeCoerce conv_monad) (undef_flag AF) (\x1 ->
        bind (unsafeCoerce conv_monad) (undef_flag PF) (\x2 ->
          bind (unsafeCoerce conv_monad) (unsafeCoerce load regimm) (\pi0 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (load_Z opsz (add1 (of_nat1 opsz) (Zpos XH))))
              (\popsz ->
              bind (unsafeCoerce conv_monad)
                (case regimm of {
                  Imm_op i ->
                   unsafeCoerce
                     (arith (opsize (op_override pre) True) Modu_op pi0
                       popsz);
                  _ ->
                   unsafeCoerce (copy_ps (opsize (op_override pre) True) pi0)})
                (\rawoffset ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce
                    (load_Z size32
                      (div1 (of_nat1 (plus opsz (S O))) (Zpos (XO (XO (XO
                        XH))))))) (\popsz_bytes ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (load_Z opsz Z0)) (\pzero ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (load_Z size32 (Zneg XH))) (\pneg1 ->
                      let {
                       btmem = \psaddr ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (arith (opsize (op_override pre) True) Mods_op
                              rawoffset popsz)) (\bitoffset ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith (opsize (op_override pre) True) Divs_op
                                rawoffset popsz)) (\wordoffset' ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (cast_s (opsize (op_override pre) True)
                                  size32 wordoffset')) (\wordoffset ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce
                                  (test (opsize (op_override pre) True) Lt_op
                                    bitoffset pzero)) (\isneg ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (copy_ps (opsize (op_override pre) True)
                                      bitoffset)) (\nbitoffset0 ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (copy_ps size32 wordoffset))
                                    (\nwordoffset0 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (arith opsz Add_op popsz bitoffset))
                                      (\negbitoffset ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (arith size32 Add_op pneg1
                                            wordoffset)) (\negwordoffset ->
                                        bind (unsafeCoerce conv_monad)
                                          (unsafeCoerce
                                            (cast_u opsz
                                              (opsize (op_override pre) True)
                                              negbitoffset)) (\nbitoffset1 ->
                                          bind (unsafeCoerce conv_monad)
                                            (unsafeCoerce
                                              (if_exp
                                                (opsize (op_override pre)
                                                  True) isneg nbitoffset1
                                                nbitoffset0)) (\nbitoffset ->
                                            bind (unsafeCoerce conv_monad)
                                              (unsafeCoerce
                                                (cast_u size32 size32
                                                  negwordoffset))
                                              (\nwordoffset1 ->
                                              bind (unsafeCoerce conv_monad)
                                                (unsafeCoerce
                                                  (if_exp size32 isneg
                                                    nwordoffset1
                                                    nwordoffset0))
                                                (\nwordoffset ->
                                                bind
                                                  (unsafeCoerce conv_monad)
                                                  (unsafeCoerce
                                                    (arith size32 Mul_op
                                                      nwordoffset
                                                      popsz_bytes))
                                                  (\newaddrdelta ->
                                                  bind
                                                    (unsafeCoerce conv_monad)
                                                    (unsafeCoerce
                                                      (arith size32 Add_op
                                                        newaddrdelta psaddr))
                                                    (\newaddr ->
                                                    bind
                                                      (unsafeCoerce
                                                        conv_monad)
                                                      (unsafeCoerce lmem0
                                                        newaddr) (\value ->
                                                      bind
                                                        (unsafeCoerce
                                                          conv_monad)
                                                        (unsafeCoerce
                                                          (get_Bit
                                                            (opsize
                                                              (op_override
                                                                pre) True)
                                                            value nbitoffset))
                                                        (\bt ->
                                                        bind
                                                          (unsafeCoerce
                                                            conv_monad)
                                                          (set_flag CF bt)
                                                          (\x3 ->
                                                          bind
                                                            (unsafeCoerce
                                                              conv_monad)
                                                            (unsafeCoerce
                                                              (fbit param1
                                                                param2 bt))
                                                            (\newbt ->
                                                            set_Bit_mem pre
                                                              True op1
                                                              newaddr
                                                              nbitoffset
                                                              newbt))))))))))))))))))}
                      in
                      case op1 of {
                       Imm_op i -> raise_error;
                       Reg_op r2 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce load (Reg_op r2)) (\value ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce
                              (arith (opsize (op_override pre) True) Modu_op
                                rawoffset popsz)) (\bitoffset ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce
                                (get_Bit (opsize (op_override pre) True)
                                  value bitoffset)) (\bt ->
                              bind (unsafeCoerce conv_monad) (set_flag CF bt)
                                (\x3 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce (fbit param1 param2 bt))
                                  (\newbt ->
                                  set_Bit pre True op1 bitoffset newbt)))));
                       Address_op a ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (compute_addr a)) (\psaddr ->
                          btmem psaddr);
                       Offset_op ioff ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce
                            (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                              (S (S O))))))))))))))))))))))))))))))) ioff))
                          (\psaddr -> btmem psaddr)}))))))))))

conv_BSWAP :: Prefix -> Register -> Conv Unit
conv_BSWAP pre r =
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce (load_Z size32 (Zpos (XO (XO (XO XH)))))) (\eight ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_reg r)) (\ps0 ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (cast_u size32 size8 ps0))
        (\b0 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size32 Shru_op ps0 eight)) (\ps1 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (cast_u size32 size8 ps1)) (\b1 ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (cast_u size8 size32 b1)) (\w1 ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (arith size32 Shru_op ps1 eight)) (\ps2 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (cast_u size32 size8 ps2)) (\b2 ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (cast_u size8 size32 b2)) (\w2 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (arith size32 Shru_op ps2 eight))
                      (\ps3 ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (cast_u size32 size8 ps3)) (\b3 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (cast_u size8 size32 b3)) (\w3 ->
                          bind (unsafeCoerce conv_monad)
                            (unsafeCoerce (cast_u size8 size32 b0)) (\res0 ->
                            bind (unsafeCoerce conv_monad)
                              (unsafeCoerce (arith size32 Shl_op res0 eight))
                              (\res1 ->
                              bind (unsafeCoerce conv_monad)
                                (unsafeCoerce (arith size32 Add_op res1 w1))
                                (\res2 ->
                                bind (unsafeCoerce conv_monad)
                                  (unsafeCoerce
                                    (arith size32 Shl_op res2 eight))
                                  (\res3 ->
                                  bind (unsafeCoerce conv_monad)
                                    (unsafeCoerce
                                      (arith size32 Add_op res3 w2))
                                    (\res4 ->
                                    bind (unsafeCoerce conv_monad)
                                      (unsafeCoerce
                                        (arith size32 Shl_op res4 eight))
                                      (\res5 ->
                                      bind (unsafeCoerce conv_monad)
                                        (unsafeCoerce
                                          (arith size32 Add_op res5 w3))
                                        (\res6 -> set_reg res6 r)))))))))))))))))))

conv_CWDE :: Prefix -> Conv Unit
conv_CWDE pre =
  let {seg = get_segment pre DS} in
  case op_override pre of {
   True ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (iload_op8 seg (Reg_op EAX))) (\p1 ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (cast_s size8 size16 p1))
        (\p2 -> iset_op16 seg p2 (Reg_op EAX)));
   False ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (iload_op16 seg (Reg_op EAX))) (\p1 ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (cast_s size16 size32 p1))
        (\p2 -> iset_op32 seg p2 (Reg_op EAX)))}

conv_CDQ :: Prefix -> Conv Unit
conv_CDQ pre =
  let {seg = get_segment pre DS} in
  case op_override pre of {
   True ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (iload_op16 seg (Reg_op EAX))) (\p1 ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (cast_s size16 size32 p1))
        (\p2 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (cast_s size32 size16 p2)) (\p2_bottom ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (load_Z size32 (Zpos (XO (XO (XO (XO XH)))))))
            (\sixteen ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce (arith size32 Shr_op p2 sixteen)) (\p2_top0 ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (cast_s size32 size16 p2_top0)) (\p2_top ->
                bind (unsafeCoerce conv_monad)
                  (iset_op16 seg p2_bottom (Reg_op EAX)) (\x ->
                  iset_op16 seg p2_top (Reg_op EDX))))))));
   False ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (iload_op32 seg (Reg_op EAX))) (\p1 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce
          (cast_s size32 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            p1)) (\p2 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce
            (cast_s (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
              size32 p2)) (\p2_bottom ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce
              (load_Z (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S
                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                (Zpos (XO (XO (XO (XO (XO XH)))))))) (\thirtytwo ->
            bind (unsafeCoerce conv_monad)
              (unsafeCoerce
                (arith (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                  (S (S (S (S (S
                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                  Shr_op p2 thirtytwo)) (\p2_top0 ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce
                  (cast_s (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                    size32 p2_top0)) (\p2_top ->
                bind (unsafeCoerce conv_monad)
                  (iset_op32 seg p2_bottom (Reg_op EAX)) (\x ->
                  iset_op32 seg p2_top (Reg_op EDX))))))))}

conv_MOV :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_MOV pre w op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op2 pre DS op1 op2} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op2) (\res ->
    set2 seg res op1)

conv_CMOV :: Prefix -> Bool -> Condition_type -> Operand -> Operand -> Conv
             Unit
conv_CMOV pre w cc op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op2 pre DS op1 op2} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1) (\tmp0 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op2) (\src ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_cc cc)) (\cc0 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce
            (cast_u (opsize (op_override pre) w) (opsize (op_override pre) w)
              src)) (\tmp1 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce
              (if_exp (opsize (op_override pre) w) cc0 tmp1 tmp0)) (\tmp ->
            set2 seg tmp op1)))))

conv_MOV_extend :: (Nat -> Nat -> Rtl_exp -> Conv Rtl_exp) -> Prefix -> Bool
                   -> Operand -> Operand -> Conv Unit
conv_MOV_extend extend_op pre w op1 op2 =
  let {seg = get_segment_op2 pre DS op1 op2} in
  case op_override pre of {
   True ->
    case w of {
     True ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (iload_op16 seg op2))
        (\p1 -> iset_op16 seg p1 op1);
     False ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (iload_op8 seg op2))
        (\p1 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce extend_op size8 size16 p1) (\p2 ->
          iset_op16 seg p2 op1))};
   False ->
    case w of {
     True ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (iload_op16 seg op2))
        (\p1 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce extend_op size16 size32 p1) (\p2 ->
          iset_op32 seg p2 op1));
     False ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (iload_op8 seg op2))
        (\p1 ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce extend_op size8 size32 p1) (\p2 ->
          iset_op32 seg p2 op1))}}

conv_MOVZX :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_MOVZX pre w op1 op2 =
  conv_MOV_extend cast_u pre w op1 op2

conv_MOVSX :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_MOVSX pre w op1 op2 =
  conv_MOV_extend cast_s pre w op1 op2

conv_XCHG :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_XCHG pre w op1 op2 =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg = get_segment_op2 pre DS op1 op2} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op1) (\p1 ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce load seg op2) (\p2 ->
      bind (unsafeCoerce conv_monad) (set2 seg p2 op1) (\x ->
        set2 seg p1 op2)))

conv_XADD :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_XADD pre w op1 op2 =
  bind (unsafeCoerce conv_monad) (conv_XCHG pre w op1 op2) (\x ->
    conv_ADD pre w op1 op2)

conv_CMPXCHG :: Prefix -> Bool -> Operand -> Operand -> Conv Unit
conv_CMPXCHG pre w op1 op2 =
  bind (unsafeCoerce conv_monad) (conv_CMP pre w (Reg_op EAX) op1) (\x ->
    bind (unsafeCoerce conv_monad) (conv_CMOV pre w E_ct op1 op2) (\x0 ->
      conv_CMOV pre w NE_ct (Reg_op EAX) op1))

string_op_reg_shift :: Register -> Prefix -> Bool -> Conv Unit
string_op_reg_shift reg pre w =
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce
      (load_Z size32
        (case op_override pre of {
          True ->
           case w of {
            True -> Zpos (XO XH);
            False -> Zpos XH};
          False ->
           case w of {
            True -> Zpos (XO (XO XH));
            False -> Zpos XH}}))) (\offset ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (get_flag DF)) (\df ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (iload_op32 DS (Reg_op reg))) (\old_reg ->
        bind (unsafeCoerce conv_monad)
          (unsafeCoerce (arith size32 Add_op old_reg offset)) (\new_reg1 ->
          bind (unsafeCoerce conv_monad)
            (unsafeCoerce (arith size32 Sub_op old_reg offset)) (\new_reg2 ->
            bind (unsafeCoerce conv_monad) (set_reg new_reg1 reg) (\x ->
              if_set_loc df size32 new_reg2 (Reg_loc reg)))))))

conv_MOVS :: Prefix -> Bool -> Conv Unit
conv_MOVS pre w =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  let {seg_load = get_segment pre DS} in
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce load seg_load (Address_op (MkAddress
      (zero1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) (Some
      ESI) None))) (\p1 ->
    bind (unsafeCoerce conv_monad)
      (set2 ES p1 (Address_op (MkAddress
        (zero1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
        (Some EDI) None))) (\x ->
      bind (unsafeCoerce conv_monad) (string_op_reg_shift EDI pre w) (\x0 ->
        string_op_reg_shift ESI pre w)))

conv_STOS :: Prefix -> Bool -> Conv Unit
conv_STOS pre w =
  let {load = load_op pre w} in
  let {set2 = set_op pre w} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce load DS (Reg_op EAX)) (\p1 ->
    bind (unsafeCoerce conv_monad)
      (set2 ES p1 (Address_op (MkAddress
        (zero1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
        (Some EDI) None))) (\x -> string_op_reg_shift EDI pre w))

conv_CMPS :: Prefix -> Bool -> Conv Unit
conv_CMPS pre w =
  let {seg1 = get_segment pre DS} in
  let {
   op1 = Address_op (MkAddress
    (zero1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) (Some ESI)
    None)}
  in
  let {
   op2 = Address_op (MkAddress
    (zero1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) (Some EDI)
    None)}
  in
  bind (unsafeCoerce conv_monad)
    (conv_SUB_CMP_generic False pre w op1 op2 op2 seg1 seg1 ES) (\x ->
    bind (unsafeCoerce conv_monad) (string_op_reg_shift EDI pre w) (\x0 ->
      string_op_reg_shift ESI pre w))

conv_LEA :: Prefix -> Operand -> Operand -> Conv Unit
conv_LEA pre op1 op2 =
  let {seg = get_segment_op pre DS op1} in
  case op2 of {
   Address_op a ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a)) (\r ->
      iset_op32 seg r op1);
   _ -> raise_error}

conv_HLT :: Prefix -> Conv Unit
conv_HLT pre =
  raise_trap

conv_SETcc :: Prefix -> Condition_type -> Operand -> Conv Unit
conv_SETcc pre ct op =
  let {seg = get_segment_op pre DS op} in
  bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_cc ct)) (\ccval ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (cast_u size1 size8 ccval))
      (\ccext -> iset_op8 seg ccext op))

check_prefix :: Prefix -> Conv Unit
check_prefix p =
  case addr_override p of {
   True -> raise_error;
   False -> no_op}

int_to_bin32 :: Int -> Binary32
int_to_bin32 i =
  b32_of_bits (intval size32 i)

bin32_to_int :: Binary32 -> Int
bin32_to_int b =
  repr size32 (bits_of_b32 b)

int_to_bin64 :: Int -> Binary64
int_to_bin64 i =
  b64_of_bits (intval size64 i)

bin64_to_int :: Binary64 -> Int
bin64_to_int b =
  repr size64 (bits_of_b64 b)

int_to_de_float :: Int -> De_float
int_to_de_float i =
  de_float_of_bits (intval size80 i)

de_float_to_int :: De_float -> Int
de_float_to_int b =
  repr size80 (bits_of_de_float b)

string_to_de_float :: String -> De_float
string_to_de_float s =
  let {intval0 = string_to_int size80 s} in int_to_de_float intval0

s2bf :: String -> De_float
s2bf s =
  string_to_de_float s

s2int80 :: String -> Int0
s2int80 s =
  string_to_int size80 s

integer_to_de_float :: Int -> De_float
integer_to_de_float i =
  let {bin = int_to_de_float i} in
  case bin of {
   B754_finite s m e ->
    let {mant_val = intval size80 i} in
    case shr0 (Build_shr_record mant_val False False) mant_val (Zpos XH) of {
     Pair rec shifted_m ->
      let {exp_val = of_nat1 size80} in
      let {
       joined = join_bits (Zpos (XO (XO (XO (XO (XO (XO XH))))))) (Zpos (XO
                  (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
                  XH))))))))))))))) s (sub1 shifted_m (Zpos XH)) exp_val}
      in
      de_float_of_bits joined};
   x -> x}

enc_rounding_mode :: Rounding_mode -> Z
enc_rounding_mode rm =
  case rm of {
   Mode_ZR -> Zpos (XI XH);
   Mode_DN -> Zpos XH;
   Mode_UP -> Zpos (XO XH);
   _ -> Z0}

data Fpu_precision_control =
   PC_single
 | PC_reserved
 | PC_double
 | PC_double_extended

fpu_precision_control_rect :: a1 -> a1 -> a1 -> a1 -> Fpu_precision_control
                              -> a1
fpu_precision_control_rect f f0 f1 f2 f3 =
  case f3 of {
   PC_single -> f;
   PC_reserved -> f0;
   PC_double -> f1;
   PC_double_extended -> f2}

fpu_precision_control_rec :: a1 -> a1 -> a1 -> a1 -> Fpu_precision_control ->
                             a1
fpu_precision_control_rec =
  fpu_precision_control_rect

enc_fpu_precision_control :: Fpu_precision_control -> Z
enc_fpu_precision_control pc0 =
  case pc0 of {
   PC_single -> Z0;
   PC_reserved -> Zpos XH;
   PC_double -> Zpos (XO XH);
   PC_double_extended -> Zpos (XI XH)}

data Fpu_tag_mode =
   TM_valid
 | TM_zero
 | TM_special
 | TM_empty

fpu_tag_mode_rect :: a1 -> a1 -> a1 -> a1 -> Fpu_tag_mode -> a1
fpu_tag_mode_rect f f0 f1 f2 f3 =
  case f3 of {
   TM_valid -> f;
   TM_zero -> f0;
   TM_special -> f1;
   TM_empty -> f2}

fpu_tag_mode_rec :: a1 -> a1 -> a1 -> a1 -> Fpu_tag_mode -> a1
fpu_tag_mode_rec =
  fpu_tag_mode_rect

enc_fpu_tag_mode :: Fpu_tag_mode -> Z
enc_fpu_tag_mode tm =
  case tm of {
   TM_valid -> Z0;
   TM_zero -> Zpos XH;
   TM_special -> Zpos (XO XH);
   TM_empty -> Zpos (XI XH)}

get_stktop :: Conv Rtl_exp
get_stktop =
  read_loc size3 Fpu_stktop_loc

get_fpu_rctrl :: Conv Rtl_exp
get_fpu_rctrl =
  read_loc size2 Fpu_rctrl_loc

get_fpu_reg :: Rtl_exp -> Conv Rtl_exp
get_fpu_reg i =
  read_array size3 size80 Fpu_datareg i

get_fpu_tag :: Rtl_exp -> Conv Rtl_exp
get_fpu_tag i =
  read_array size3 size2 Fpu_tag i

set_stktop :: Rtl_exp -> Conv Unit
set_stktop t =
  write_loc size3 t Fpu_stktop_loc

set_stktop_const :: Z -> Conv Unit
set_stktop_const t =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size3 t)) (\r ->
    set_stktop r)

set_fpu_flag :: Fpu_flag -> Rtl_exp -> Conv Unit
set_fpu_flag fl r =
  write_loc size1 r (Fpu_flag_loc fl)

set_fpu_flag_const :: Fpu_flag -> Z -> Conv Unit
set_fpu_flag_const fl bit =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 bit)) (\r ->
    set_fpu_flag fl r)

set_fpu_ctrl :: Fpu_ctrl_flag -> Rtl_exp -> Conv Unit
set_fpu_ctrl cf r =
  write_loc size1 r (Fpu_ctrl_flag_loc cf)

set_fpu_ctrl_const :: Fpu_ctrl_flag -> Z -> Conv Unit
set_fpu_ctrl_const cf bit =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 bit)) (\r ->
    set_fpu_ctrl cf r)

set_fpu_rctrl :: Rtl_exp -> Conv Unit
set_fpu_rctrl r =
  write_loc size2 r Fpu_rctrl_loc

set_fpu_rctrl_const :: Mode -> Conv Unit
set_fpu_rctrl_const rm =
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce (load_Z size2 (enc_rounding_mode rm))) (\r ->
    set_fpu_rctrl r)

set_fpu_pctrl :: Rtl_exp -> Conv Unit
set_fpu_pctrl r =
  write_loc size2 r Fpu_pctrl_loc

set_fpu_pctrl_const :: Fpu_precision_control -> Conv Unit
set_fpu_pctrl_const pc0 =
  bind (unsafeCoerce conv_monad)
    (unsafeCoerce (load_Z size2 (enc_fpu_precision_control pc0))) (\r ->
    set_fpu_pctrl r)

set_fpu_lastInstrPtr :: Rtl_exp -> Conv Unit
set_fpu_lastInstrPtr r =
  write_loc size48 r Fpu_lastInstrPtr_loc

set_fpu_lastInstrPtr_const :: Z -> Conv Unit
set_fpu_lastInstrPtr_const v =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size48 v)) (\r ->
    set_fpu_lastInstrPtr r)

set_fpu_lastDataPtr :: Rtl_exp -> Conv Unit
set_fpu_lastDataPtr r =
  write_loc size48 r Fpu_lastDataPtr_loc

set_fpu_lastDataPtr_const :: Z -> Conv Unit
set_fpu_lastDataPtr_const v =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size48 v)) (\r ->
    set_fpu_lastDataPtr r)

set_fpu_lastOpcode :: Rtl_exp -> Conv Unit
set_fpu_lastOpcode r =
  write_loc size11 r Fpu_lastOpcode_loc

set_fpu_lastOpcode_const :: Z -> Conv Unit
set_fpu_lastOpcode_const v =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size11 v)) (\r ->
    set_fpu_lastOpcode r)

set_fpu_reg :: Rtl_exp -> Rtl_exp -> Conv Unit
set_fpu_reg i v =
  write_array size3 size80 Fpu_datareg i v

set_fpu_tag :: Rtl_exp -> Rtl_exp -> Conv Unit
set_fpu_tag i v =
  write_array size3 size2 Fpu_tag i v

set_fpu_tag_const :: Z -> Fpu_tag_mode -> Conv Unit
set_fpu_tag_const loc tm =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size3 loc)) (\i ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (load_Z size2 (enc_fpu_tag_mode tm))) (\v ->
      set_fpu_tag i v))

inc_stktop :: Conv Unit
inc_stktop =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\st ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size3 (Zpos XH)))
      (\one2 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith size3 Add_op st one2)) (\newst ->
        set_stktop newst)))

dec_stktop :: Conv Unit
dec_stktop =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\st ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size3 (Zpos XH)))
      (\one2 ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (arith size3 Sub_op st one2)) (\newst ->
        set_stktop newst)))

stk_push :: Rtl_exp -> Conv Unit
stk_push f =
  bind (unsafeCoerce conv_monad) dec_stktop (\x ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\topp ->
      set_fpu_reg topp f))

freg_of_offset :: Int3 -> Conv Rtl_exp
freg_of_offset offset =
  bind (unsafeCoerce conv_monad) get_stktop (\topp ->
    bind (unsafeCoerce conv_monad) (load_Z size3 (unsigned (S (S O)) offset))
      (\ri -> arith size3 Add_op topp ri))

undef_fpu_flag :: Fpu_flag -> Conv Unit
undef_fpu_flag f =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (choose size1)) (\v ->
    set_fpu_flag f v)

is_empty_tag :: Rtl_exp -> Conv Rtl_exp
is_empty_tag i =
  bind (unsafeCoerce conv_monad) (get_fpu_tag i) (\tag ->
    bind (unsafeCoerce conv_monad) (load_Z size2 (Zpos (XI XH)))
      (\empty_tag -> test size2 Eq_op tag empty_tag))

is_nonempty_tag :: Rtl_exp -> Conv Rtl_exp
is_nonempty_tag i =
  bind (unsafeCoerce conv_monad) (is_empty_tag i) (\isempty ->
    not0 size1 isempty)

test_pos_zero :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_pos_zero ew mw f =
  bind (unsafeCoerce conv_monad) (load_Z (plus (to_nat ew) (to_nat mw)) Z0)
    (\poszero -> test (plus (to_nat ew) (to_nat mw)) Eq_op f poszero)

test_neg_zero :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_neg_zero ew mw f =
  bind (unsafeCoerce conv_monad)
    (load_Z (plus (to_nat ew) (to_nat mw))
      (two_power_nat (plus (to_nat mw) (to_nat ew)))) (\negzero ->
    test (plus (to_nat ew) (to_nat mw)) Eq_op f negzero)

test_zero :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_zero ew mw f =
  bind (unsafeCoerce conv_monad) (test_pos_zero ew mw f) (\isposzero ->
    bind (unsafeCoerce conv_monad) (test_neg_zero ew mw f) (\isnegzero ->
      arith size1 Or_op isposzero isnegzero))

test_pos_inf :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_pos_inf ew mw f =
  bind (unsafeCoerce conv_monad)
    (load_Z (plus (to_nat ew) (to_nat mw))
      (mul1 (two_power_nat (to_nat mw))
        (sub1 (two_power_nat (to_nat ew)) (Zpos XH)))) (\posinf ->
    test (plus (to_nat ew) (to_nat mw)) Eq_op f posinf)

test_neg_inf :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_neg_inf ew mw f =
  bind (unsafeCoerce conv_monad)
    (load_Z (plus (to_nat ew) (to_nat mw))
      (mul1 (two_power_nat (to_nat mw))
        (sub1 (two_power_nat (plus (to_nat ew) (S O))) (Zpos XH))))
    (\neginf -> test (plus (to_nat ew) (to_nat mw)) Eq_op f neginf)

test_inf :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_inf ew mw f =
  bind (unsafeCoerce conv_monad) (test_pos_inf ew mw f) (\isposinf ->
    bind (unsafeCoerce conv_monad) (test_neg_inf ew mw f) (\isneginf ->
      arith size1 Or_op isposinf isneginf))

test_qnan :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_qnan ew mw f =
  bind (unsafeCoerce conv_monad)
    (load_Z (plus (to_nat ew) (to_nat mw))
      (mul1 (two_power_nat (minus (to_nat mw) (S O)))
        (sub1 (two_power_nat (plus (to_nat ew) (S O))) (Zpos XH)))) (\mask ->
    bind (unsafeCoerce conv_monad)
      (arith (plus (to_nat ew) (to_nat mw)) And_op f mask) (\maskRes ->
      test (plus (to_nat ew) (to_nat mw)) Eq_op maskRes mask))

test_snan :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_snan ew mw f =
  bind (unsafeCoerce conv_monad) (test_inf ew mw f) (\isinf ->
    bind (unsafeCoerce conv_monad) (not0 size1 isinf) (\isnotinf ->
      bind (unsafeCoerce conv_monad)
        (load_Z (plus (to_nat ew) (to_nat mw))
          (mul1 (two_power_nat (minus (to_nat mw) (S O)))
            (sub1 (two_power_nat (plus (to_nat ew) (S O))) (Zpos XH))))
        (\mask ->
        bind (unsafeCoerce conv_monad)
          (arith (plus (to_nat ew) (to_nat mw)) And_op f mask) (\maskRes ->
          bind (unsafeCoerce conv_monad)
            (load_Z (plus (to_nat ew) (to_nat mw))
              (mul1 (two_power_nat (to_nat mw))
                (sub1 (two_power_nat (to_nat ew)) (Zpos XH)))) (\expected ->
            bind (unsafeCoerce conv_monad)
              (test (plus (to_nat ew) (to_nat mw)) Eq_op maskRes expected)
              (\is_snan -> arith size1 And_op isnotinf is_snan))))))

test_nan :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_nan ew mw f =
  bind (unsafeCoerce conv_monad) (test_qnan ew mw f) (\isqnan ->
    bind (unsafeCoerce conv_monad) (test_snan ew mw f) (\issnan ->
      arith size1 Or_op isqnan issnan))

test_denormal :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_denormal ew mw f =
  bind (unsafeCoerce conv_monad) (test_zero ew mw f) (\iszero ->
    bind (unsafeCoerce conv_monad) (not0 size1 iszero) (\isnotzero ->
      bind (unsafeCoerce conv_monad)
        (load_Z (plus (to_nat ew) (to_nat mw))
          (mul1 (two_power_nat (to_nat mw))
            (sub1 (two_power_nat (to_nat ew)) (Zpos XH)))) (\mask ->
        bind (unsafeCoerce conv_monad)
          (arith (plus (to_nat ew) (to_nat mw)) And_op f mask) (\maskRes ->
          bind (unsafeCoerce conv_monad)
            (load_Z (plus (to_nat ew) (to_nat mw)) Z0) (\zero2 ->
            bind (unsafeCoerce conv_monad)
              (test (plus (to_nat ew) (to_nat mw)) Eq_op maskRes zero2)
              (\expZero -> arith size1 And_op isnotzero expZero))))))

test_normal_fin :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_normal_fin ew mw f =
  bind (unsafeCoerce conv_monad)
    (load_Z (plus (to_nat ew) (to_nat mw))
      (mul1 (two_power_nat (to_nat mw))
        (sub1 (two_power_nat (to_nat ew)) (Zpos XH)))) (\mask ->
    bind (unsafeCoerce conv_monad)
      (arith (plus (to_nat ew) (to_nat mw)) And_op f mask) (\maskRes ->
      bind (unsafeCoerce conv_monad)
        (load_Z (plus (to_nat ew) (to_nat mw)) Z0) (\zero2 ->
        bind (unsafeCoerce conv_monad)
          (test (plus (to_nat ew) (to_nat mw)) Eq_op maskRes zero2)
          (\iszero ->
          bind (unsafeCoerce conv_monad) (not0 size1 iszero) (\notzero ->
            bind (unsafeCoerce conv_monad)
              (test (plus (to_nat ew) (to_nat mw)) Eq_op maskRes mask)
              (\maxexpo ->
              bind (unsafeCoerce conv_monad) (not0 size1 maxexpo)
                (\notmaxexpo -> arith size1 And_op notzero notmaxexpo)))))))

test_fin :: Positive -> Positive -> Rtl_exp -> Conv Rtl_exp
test_fin ew mw f =
  bind (unsafeCoerce conv_monad) (test_denormal ew mw f) (\isdefin ->
    bind (unsafeCoerce conv_monad) (test_normal_fin ew mw f) (\isnorfin ->
      arith size1 Or_op isdefin isnorfin))

size63 :: Nat
size63 =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

de_float_of_float79 :: Rtl_exp -> Conv Rtl_exp
de_float_of_float79 f =
  bind (unsafeCoerce conv_monad) (first_bits size16 size79 f)
    (\signAndExpo ->
    bind (unsafeCoerce conv_monad) (last_bits size63 size79 f) (\mantissa ->
      bind (unsafeCoerce conv_monad)
        (test_inf (XI (XI (XI (XI (XI XH))))) (XI (XI (XI XH))) f) (\isInf ->
        bind (unsafeCoerce conv_monad)
          (test_normal_fin (XI (XI (XI (XI (XI XH))))) (XI (XI (XI XH))) f)
          (\isNorFin ->
          bind (unsafeCoerce conv_monad) (arith size1 Or_op isInf isNorFin)
            (\intSig ->
            bind (unsafeCoerce conv_monad)
              (concat_bits size1 size63 intSig mantissa) (\r ->
              concat_bits size16 (plus (plus size1 size63) (S O)) signAndExpo
                r))))))

float79_of_de_float :: Rtl_exp -> Conv Rtl_exp
float79_of_de_float f =
  bind (unsafeCoerce conv_monad) (first_bits size16 size80 f)
    (\signAndExpo ->
    bind (unsafeCoerce conv_monad) (last_bits size63 size80 f) (\mantissa ->
      concat_bits size16 size63 signAndExpo mantissa))

de_float_of_float32 :: Rtl_exp -> Rtl_exp -> Conv Rtl_exp
de_float_of_float32 f rm =
  bind (unsafeCoerce conv_monad)
    (fcast (XO (XO (XO XH))) (XI (XI (XI (XO XH)))) (XI (XI (XI XH))) (XI (XI
      (XI (XI (XI XH))))) rm f) (\f' -> de_float_of_float79 f')

de_float_of_float64 :: Rtl_exp -> Rtl_exp -> Conv Rtl_exp
de_float_of_float64 f rm =
  bind (unsafeCoerce conv_monad)
    (fcast (XI (XI (XO XH))) (XO (XO (XI (XO (XI XH))))) (XI (XI (XI XH)))
      (XI (XI (XI (XI (XI XH))))) rm f) (\f' -> de_float_of_float79 f')

float32_of_de_float :: Rtl_exp -> Rtl_exp -> Conv Rtl_exp
float32_of_de_float f rm =
  bind (unsafeCoerce conv_monad) (float79_of_de_float f) (\f' ->
    fcast (XI (XI (XI XH))) (XI (XI (XI (XI (XI XH))))) (XO (XO (XO XH))) (XI
      (XI (XI (XO XH)))) rm f')

float64_of_de_float :: Rtl_exp -> Rtl_exp -> Conv Rtl_exp
float64_of_de_float f rm =
  bind (unsafeCoerce conv_monad) (float79_of_de_float f) (\f' ->
    fcast (XI (XI (XI XH))) (XI (XI (XI (XI (XI XH))))) (XI (XI (XO XH))) (XO
      (XO (XI (XO (XI XH))))) rm f')

enc_tag :: Rtl_exp -> Conv Rtl_exp
enc_tag f =
  bind (unsafeCoerce conv_monad) (float79_of_de_float f) (\nf ->
    bind (unsafeCoerce conv_monad)
      (test_zero (XI (XI (XI XH))) (XI (XI (XI (XI (XI XH))))) nf)
      (\iszero ->
      bind (unsafeCoerce conv_monad)
        (test_normal_fin (XI (XI (XI XH))) (XI (XI (XI (XI (XI XH))))) nf)
        (\isnorfin ->
        bind (unsafeCoerce conv_monad)
          (load_Z size2 (enc_fpu_tag_mode TM_valid)) (\enc_valid ->
          bind (unsafeCoerce conv_monad)
            (load_Z size2 (enc_fpu_tag_mode TM_zero)) (\enc_zero ->
            bind (unsafeCoerce conv_monad)
              (load_Z size2 (enc_fpu_tag_mode TM_special)) (\enc_special ->
              bind (unsafeCoerce conv_monad)
                (if_exp size2 iszero enc_zero enc_special) (\z_or_s ->
                if_exp size2 isnorfin enc_valid z_or_s)))))))

load_ifp_op :: Prefix -> Segment_register -> Operand -> Conv Rtl_exp
load_ifp_op pre seg op =
  case op of {
   Imm_op i ->
    load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))) i;
   Reg_op r -> load_reg r;
   Address_op a ->
    bind (unsafeCoerce conv_monad) (compute_addr a) (\p1 ->
      load_mem32 seg p1);
   Offset_op off ->
    bind (unsafeCoerce conv_monad)
      (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))
        off) (\p1 -> load_mem32 seg p1)}

load_fp_op :: Prefix -> Segment_register -> Fp_operand -> Conv Rtl_exp
load_fp_op pre seg op =
  let {sr = get_segment pre seg} in
  bind (unsafeCoerce conv_monad) get_fpu_rctrl (\rm ->
    case op of {
     FPS_op i ->
      bind (unsafeCoerce conv_monad) (freg_of_offset i) (\fi ->
        get_fpu_reg fi);
     FPM16_op a ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce raise_error) (\x ->
        choose size80);
     FPM32_op a ->
      bind (unsafeCoerce conv_monad) (compute_addr a) (\addr ->
        bind (unsafeCoerce conv_monad) (load_mem32 sr addr) (\val ->
          de_float_of_float32 val rm));
     FPM64_op a ->
      bind (unsafeCoerce conv_monad) (compute_addr a) (\addr ->
        bind (unsafeCoerce conv_monad) (load_mem64 sr addr) (\val ->
          de_float_of_float64 val rm));
     FPM80_op a ->
      bind (unsafeCoerce conv_monad) (compute_addr a) (\addr ->
        load_mem80 sr addr)})

conv_FNCLEX :: Conv Unit
conv_FNCLEX =
  bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_PE Z0) (\x ->
    bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_UE Z0) (\x0 ->
      bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_OE Z0) (\x1 ->
        bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_ZE Z0) (\x2 ->
          bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_DE Z0) (\x3 ->
            bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_IE Z0)
              (\x4 ->
              bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_ES Z0)
                (\x5 -> set_fpu_flag_const F_Busy Z0)))))))

init_control_word :: Conv Unit
init_control_word =
  bind (unsafeCoerce conv_monad) (set_fpu_ctrl_const F_Res15 Z0) (\x ->
    bind (unsafeCoerce conv_monad) (set_fpu_ctrl_const F_Res14 Z0) (\x0 ->
      bind (unsafeCoerce conv_monad) (set_fpu_ctrl_const F_Res13 Z0) (\x1 ->
        bind (unsafeCoerce conv_monad) (set_fpu_ctrl_const F_IC Z0) (\x2 ->
          bind (unsafeCoerce conv_monad) (set_fpu_rctrl_const Mode_NE)
            (\x3 ->
            bind (unsafeCoerce conv_monad)
              (set_fpu_pctrl_const PC_double_extended) (\x4 ->
              bind (unsafeCoerce conv_monad) (set_fpu_ctrl_const F_Res6 Z0)
                (\x5 ->
                bind (unsafeCoerce conv_monad)
                  (set_fpu_ctrl_const F_Res7 (Zpos XH)) (\x6 ->
                  bind (unsafeCoerce conv_monad)
                    (set_fpu_ctrl_const F_PM (Zpos XH)) (\x7 ->
                    bind (unsafeCoerce conv_monad)
                      (set_fpu_ctrl_const F_UM (Zpos XH)) (\x8 ->
                      bind (unsafeCoerce conv_monad)
                        (set_fpu_ctrl_const F_OM (Zpos XH)) (\x9 ->
                        bind (unsafeCoerce conv_monad)
                          (set_fpu_ctrl_const F_ZM (Zpos XH)) (\x10 ->
                          bind (unsafeCoerce conv_monad)
                            (set_fpu_ctrl_const F_DM (Zpos XH)) (\x11 ->
                            set_fpu_ctrl_const F_IM (Zpos XH))))))))))))))

init_status_word :: Conv Unit
init_status_word =
  bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_Busy Z0) (\x ->
    bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C3 Z0) (\x0 ->
      bind (unsafeCoerce conv_monad) (set_stktop_const Z0) (\x1 ->
        bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C2 Z0) (\x2 ->
          bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C1 Z0) (\x3 ->
            bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C0 Z0)
              (\x4 ->
              bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_ES Z0)
                (\x5 ->
                bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_SF Z0)
                  (\x6 ->
                  bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_PE Z0)
                    (\x7 ->
                    bind (unsafeCoerce conv_monad)
                      (set_fpu_flag_const F_UE Z0) (\x8 ->
                      bind (unsafeCoerce conv_monad)
                        (set_fpu_flag_const F_OE Z0) (\x9 ->
                        bind (unsafeCoerce conv_monad)
                          (set_fpu_flag_const F_ZE Z0) (\x10 ->
                          bind (unsafeCoerce conv_monad)
                            (set_fpu_flag_const F_DE Z0) (\x11 ->
                            set_fpu_flag_const F_IE Z0)))))))))))))

init_tag_word :: Conv Unit
init_tag_word =
  bind (unsafeCoerce conv_monad) (set_fpu_tag_const Z0 TM_empty) (\x ->
    bind (unsafeCoerce conv_monad) (set_fpu_tag_const (Zpos XH) TM_empty)
      (\x0 ->
      bind (unsafeCoerce conv_monad)
        (set_fpu_tag_const (Zpos (XO XH)) TM_empty) (\x1 ->
        bind (unsafeCoerce conv_monad)
          (set_fpu_tag_const (Zpos (XI XH)) TM_empty) (\x2 ->
          bind (unsafeCoerce conv_monad)
            (set_fpu_tag_const (Zpos (XO (XO XH))) TM_empty) (\x3 ->
            bind (unsafeCoerce conv_monad)
              (set_fpu_tag_const (Zpos (XI (XO XH))) TM_empty) (\x4 ->
              bind (unsafeCoerce conv_monad)
                (set_fpu_tag_const (Zpos (XO (XI XH))) TM_empty) (\x5 ->
                set_fpu_tag_const (Zpos (XI (XI XH))) TM_empty)))))))

init_last_ptrs :: Conv Unit
init_last_ptrs =
  bind (unsafeCoerce conv_monad) (set_fpu_lastInstrPtr_const Z0) (\x ->
    bind (unsafeCoerce conv_monad) (set_fpu_lastDataPtr_const Z0) (\x0 ->
      set_fpu_lastOpcode_const Z0))

conv_FNINIT :: Conv Unit
conv_FNINIT =
  bind (unsafeCoerce conv_monad) init_control_word (\x ->
    bind (unsafeCoerce conv_monad) init_status_word (\x0 ->
      bind (unsafeCoerce conv_monad) init_tag_word (\x1 -> init_last_ptrs)))

conv_FINCSTP :: Conv Unit
conv_FINCSTP =
  bind (unsafeCoerce conv_monad) inc_stktop (\x ->
    bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C1 Z0) (\x0 ->
      bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C0) (\x1 ->
        bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C2) (\x2 ->
          undef_fpu_flag F_C3))))

conv_FDECSTP :: Conv Unit
conv_FDECSTP =
  bind (unsafeCoerce conv_monad) dec_stktop (\x ->
    bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C1 Z0) (\x0 ->
      bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C0) (\x1 ->
        bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C2) (\x2 ->
          undef_fpu_flag F_C3))))

stk_push_and_set_tag :: Rtl_exp -> Conv Rtl_exp
stk_push_and_set_tag f =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (stk_push f)) (\x ->
    bind (unsafeCoerce conv_monad) get_stktop (\topp ->
      bind (unsafeCoerce conv_monad) (enc_tag f) (\tag ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce (set_fpu_tag topp tag))
          (\x0 -> is_nonempty_tag topp))))

conv_FLD :: Prefix -> Fp_operand -> Conv Unit
conv_FLD pre op =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_fp_op pre DS op)) (\v ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (stk_push_and_set_tag v))
      (\overflow ->
      bind (unsafeCoerce conv_monad) (set_fpu_flag F_C1 overflow) (\x ->
        bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C0) (\x0 ->
          bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C2) (\x1 ->
            undef_fpu_flag F_C3)))))

conv_FILD :: Prefix -> Fp_operand -> Conv Unit
conv_FILD pre op =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_fp_op pre DS op)) (\v ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (stk_push_and_set_tag v))
      (\overflow ->
      bind (unsafeCoerce conv_monad) (set_fpu_flag F_C1 overflow) (\x ->
        bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C0) (\x0 ->
          bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C2) (\x1 ->
            undef_fpu_flag F_C3)))))

load_stktop :: Conv Rtl_exp
load_stktop =
  bind (unsafeCoerce conv_monad) get_stktop (\topp -> get_fpu_reg topp)

conv_FST :: Prefix -> Fp_operand -> Conv Unit
conv_FST pre op =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\topp ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (get_fpu_reg topp)) (\v ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (is_empty_tag topp))
        (\underflow ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce get_fpu_rctrl) (\rm ->
          let {sr = get_segment pre DS} in
          bind (unsafeCoerce conv_monad)
            (case op of {
              FPS_op i ->
               bind (unsafeCoerce conv_monad)
                 (unsafeCoerce (freg_of_offset i)) (\fi -> set_fpu_reg fi v);
              FPM16_op a -> raise_error;
              FPM32_op a ->
               bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a))
                 (\addr ->
                 bind (unsafeCoerce conv_monad)
                   (unsafeCoerce (float32_of_de_float v rm)) (\f32 ->
                   set_mem32 sr f32 addr));
              FPM64_op a ->
               bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a))
                 (\addr ->
                 bind (unsafeCoerce conv_monad)
                   (unsafeCoerce (float64_of_de_float v rm)) (\f64 ->
                   set_mem64 sr f64 addr));
              FPM80_op a ->
               bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a))
                 (\addr -> set_mem80 sr v addr)}) (\x ->
            bind (unsafeCoerce conv_monad) (unsafeCoerce (choose size1))
              (\v0 ->
              bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 Z0))
                (\zero2 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (if_exp size1 underflow zero2 v0)) (\c1 ->
                  bind (unsafeCoerce conv_monad) (set_fpu_flag F_C1 c1)
                    (\x0 ->
                    bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C0)
                      (\x1 ->
                      bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C2)
                        (\x2 -> undef_fpu_flag F_C3)))))))))))

conv_FIST :: Prefix -> Fp_operand -> Conv Unit
conv_FIST pre op =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\topp ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (get_fpu_reg topp)) (\v ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (is_empty_tag topp))
        (\underflow ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce get_fpu_rctrl) (\rm ->
          let {sr = get_segment pre DS} in
          bind (unsafeCoerce conv_monad)
            (case op of {
              FPS_op i ->
               bind (unsafeCoerce conv_monad)
                 (unsafeCoerce (freg_of_offset i)) (\fi -> set_fpu_reg fi v);
              FPM16_op a -> raise_error;
              FPM32_op a ->
               bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a))
                 (\addr ->
                 bind (unsafeCoerce conv_monad)
                   (unsafeCoerce (float32_of_de_float v rm)) (\f32 ->
                   set_mem32 sr f32 addr));
              FPM64_op a ->
               bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a))
                 (\addr ->
                 bind (unsafeCoerce conv_monad)
                   (unsafeCoerce (float64_of_de_float v rm)) (\f64 ->
                   set_mem64 sr f64 addr));
              FPM80_op a ->
               bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr a))
                 (\addr -> set_mem80 sr v addr)}) (\x ->
            bind (unsafeCoerce conv_monad) (unsafeCoerce (choose size1))
              (\v0 ->
              bind (unsafeCoerce conv_monad) (unsafeCoerce (load_Z size1 Z0))
                (\zero2 ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (if_exp size1 underflow zero2 v0)) (\c1 ->
                  bind (unsafeCoerce conv_monad) (set_fpu_flag F_C1 c1)
                    (\x0 ->
                    bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C0)
                      (\x1 ->
                      bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C2)
                        (\x2 -> undef_fpu_flag F_C3)))))))))))

stk_pop_and_set_tag :: Conv Unit
stk_pop_and_set_tag =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\topp ->
    bind (unsafeCoerce conv_monad)
      (unsafeCoerce (load_Z size2 (enc_fpu_tag_mode TM_empty))) (\tag_emp ->
      bind (unsafeCoerce conv_monad) (set_fpu_tag topp tag_emp) (\x ->
        inc_stktop)))

conv_FSTP :: Prefix -> Fp_operand -> Conv Unit
conv_FSTP pre op =
  bind (unsafeCoerce conv_monad) (conv_FST pre op) (\x ->
    stk_pop_and_set_tag)

conv_FISTP :: Prefix -> Fp_operand -> Conv Unit
conv_FISTP pre op =
  bind (unsafeCoerce conv_monad) (conv_FIST pre op) (\x ->
    stk_pop_and_set_tag)

pos1 :: Int0
pos1 =
  s2int80
    (append (String0 (Ascii False False False False True True False False)
      (String0 (Ascii False False False False True True False False) (String0
      (Ascii True False False False True True False False) (String0 (Ascii
      True False False False True True False False) (String0 (Ascii True
      False False False True True False False) (String0 (Ascii True False
      False False True True False False) (String0 (Ascii True False False
      False True True False False) (String0 (Ascii True False False False
      True True False False) EmptyString))))))))
      (append (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        EmptyString))))))))
        (append (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          EmptyString))))))))
          (append (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) EmptyString))))))))
            (append (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) EmptyString))))))))
              (append (String0 (Ascii False False False False True True False
                False) (String0 (Ascii False False False False True True
                False False) (String0 (Ascii False False False False True
                True False False) (String0 (Ascii False False False False
                True True False False) (String0 (Ascii False False False
                False True True False False) (String0 (Ascii False False
                False False True True False False) (String0 (Ascii False
                False False False True True False False) (String0 (Ascii
                False False False False True True False False)
                EmptyString))))))))
                (append (String0 (Ascii False False False False True True
                  False False) (String0 (Ascii False False False False True
                  True False False) (String0 (Ascii False False False False
                  True True False False) (String0 (Ascii False False False
                  False True True False False) (String0 (Ascii False False
                  False False True True False False) (String0 (Ascii False
                  False False False True True False False) (String0 (Ascii
                  False False False False True True False False) (String0
                  (Ascii False False False False True True False False)
                  EmptyString))))))))
                  (append (String0 (Ascii False False False False True True
                    False False) (String0 (Ascii False False False False True
                    True False False) (String0 (Ascii False False False False
                    True True False False) (String0 (Ascii False False False
                    False True True False False) (String0 (Ascii False False
                    False False True True False False) (String0 (Ascii False
                    False False False True True False False) (String0 (Ascii
                    False False False False True True False False) (String0
                    (Ascii False False False False True True False False)
                    EmptyString))))))))
                    (append (String0 (Ascii False False False False True True
                      False False) (String0 (Ascii False False False False
                      True True False False) (String0 (Ascii False False
                      False False True True False False) (String0 (Ascii
                      False False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii False False False False True True False
                      False) (String0 (Ascii False False False False True
                      True False False) (String0 (Ascii False False False
                      False True True False False) EmptyString))))))))
                      (String0 (Ascii False False False False True True False
                      False) (String0 (Ascii False False False False True
                      True False False) (String0 (Ascii False False False
                      False True True False False) (String0 (Ascii False
                      False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii False False False False True True False
                      False) (String0 (Ascii False False False False True
                      True False False) (String0 (Ascii False False False
                      False True True False False) EmptyString)))))))))))))))))

log2_10 :: Int0
log2_10 =
  s2int80
    (append (String0 (Ascii False False False False True True False False)
      (String0 (Ascii True False False False True True False False) (String0
      (Ascii False False False False True True False False) (String0 (Ascii
      False False False False True True False False) (String0 (Ascii False
      False False False True True False False) (String0 (Ascii False False
      False False True True False False) (String0 (Ascii False False False
      False True True False False) (String0 (Ascii False False False False
      True True False False) EmptyString))))))))
      (append (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        EmptyString))))))))
        (append (String0 (Ascii True False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          EmptyString))))))))
          (append (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) EmptyString))))))))
            (append (String0 (Ascii False False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) EmptyString))))))))
              (append (String0 (Ascii False False False False True True False
                False) (String0 (Ascii True False False False True True False
                False) (String0 (Ascii False False False False True True
                False False) (String0 (Ascii False False False False True
                True False False) (String0 (Ascii True False False False True
                True False False) (String0 (Ascii False False False False
                True True False False) (String0 (Ascii True False False False
                True True False False) (String0 (Ascii True False False False
                True True False False) EmptyString))))))))
                (append (String0 (Ascii True False False False True True
                  False False) (String0 (Ascii True False False False True
                  True False False) (String0 (Ascii False False False False
                  True True False False) (String0 (Ascii False False False
                  False True True False False) (String0 (Ascii True False
                  False False True True False False) (String0 (Ascii True
                  False False False True True False False) (String0 (Ascii
                  False False False False True True False False) (String0
                  (Ascii True False False False True True False False)
                  EmptyString))))))))
                  (append (String0 (Ascii False False False False True True
                    False False) (String0 (Ascii False False False False True
                    True False False) (String0 (Ascii False False False False
                    True True False False) (String0 (Ascii True False False
                    False True True False False) (String0 (Ascii True False
                    False False True True False False) (String0 (Ascii False
                    False False False True True False False) (String0 (Ascii
                    True False False False True True False False) (String0
                    (Ascii True False False False True True False False)
                    EmptyString))))))))
                    (append (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii False False False False
                      True True False False) (String0 (Ascii False False
                      False False True True False False) (String0 (Ascii
                      False False False False True True False False) (String0
                      (Ascii True False False False True True False False)
                      (String0 (Ascii False False False False True True False
                      False) (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii False False False False
                      True True False False) EmptyString)))))))) (String0
                      (Ascii True False False False True True False False)
                      (String0 (Ascii True False False False True True False
                      False) (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii True False False False
                      True True False False) (String0 (Ascii True False False
                      False True True False False) (String0 (Ascii True False
                      False False True True False False) (String0 (Ascii True
                      False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      EmptyString)))))))))))))))))

log2_e :: Int0
log2_e =
  s2int80
    (append (String0 (Ascii False False False False True True False False)
      (String0 (Ascii False False False False True True False False) (String0
      (Ascii True False False False True True False False) (String0 (Ascii
      True False False False True True False False) (String0 (Ascii True
      False False False True True False False) (String0 (Ascii True False
      False False True True False False) (String0 (Ascii True False False
      False True True False False) (String0 (Ascii True False False False
      True True False False) EmptyString))))))))
      (append (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        EmptyString))))))))
        (append (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          EmptyString))))))))
          (append (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) EmptyString))))))))
            (append (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) EmptyString))))))))
              (append (String0 (Ascii False False False False True True False
                False) (String0 (Ascii False False False False True True
                False False) (String0 (Ascii True False False False True True
                False False) (String0 (Ascii False False False False True
                True False False) (String0 (Ascii True False False False True
                True False False) (String0 (Ascii False False False False
                True True False False) (String0 (Ascii False False False
                False True True False False) (String0 (Ascii True False False
                False True True False False) EmptyString))))))))
                (append (String0 (Ascii False False False False True True
                  False False) (String0 (Ascii True False False False True
                  True False False) (String0 (Ascii False False False False
                  True True False False) (String0 (Ascii True False False
                  False True True False False) (String0 (Ascii True False
                  False False True True False False) (String0 (Ascii True
                  False False False True True False False) (String0 (Ascii
                  False False False False True True False False) (String0
                  (Ascii False False False False True True False False)
                  EmptyString))))))))
                  (append (String0 (Ascii False False False False True True
                    False False) (String0 (Ascii False False False False True
                    True False False) (String0 (Ascii False False False False
                    True True False False) (String0 (Ascii True False False
                    False True True False False) (String0 (Ascii False False
                    False False True True False False) (String0 (Ascii True
                    False False False True True False False) (String0 (Ascii
                    True False False False True True False False) (String0
                    (Ascii True False False False True True False False)
                    EmptyString))))))))
                    (append (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii True False False False
                      True True False False) (String0 (Ascii True False False
                      False True True False False) (String0 (Ascii True False
                      False False True True False False) (String0 (Ascii
                      False False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii False False False False True True False
                      False) (String0 (Ascii False False False False True
                      True False False) EmptyString)))))))) (String0 (Ascii
                      True False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii True False False False True True False
                      False) (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii True False False False
                      True True False False) (String0 (Ascii True False False
                      False True True False False) (String0 (Ascii False
                      False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      EmptyString)))))))))))))))))

pi :: Int0
pi =
  s2int80
    (append (String0 (Ascii False False False False True True False False)
      (String0 (Ascii True False False False True True False False) (String0
      (Ascii False False False False True True False False) (String0 (Ascii
      False False False False True True False False) (String0 (Ascii False
      False False False True True False False) (String0 (Ascii False False
      False False True True False False) (String0 (Ascii False False False
      False True True False False) (String0 (Ascii False False False False
      True True False False) EmptyString))))))))
      (append (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        EmptyString))))))))
        (append (String0 (Ascii True False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          EmptyString))))))))
          (append (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) EmptyString))))))))
            (append (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) EmptyString))))))))
              (append (String0 (Ascii True False False False True True False
                False) (String0 (Ascii False False False False True True
                False False) (String0 (Ascii True False False False True True
                False False) (String0 (Ascii False False False False True
                True False False) (String0 (Ascii False False False False
                True True False False) (String0 (Ascii False False False
                False True True False False) (String0 (Ascii True False False
                False True True False False) (String0 (Ascii False False
                False False True True False False) EmptyString))))))))
                (append (String0 (Ascii False False False False True True
                  False False) (String0 (Ascii False False False False True
                  True False False) (String0 (Ascii True False False False
                  True True False False) (String0 (Ascii False False False
                  False True True False False) (String0 (Ascii False False
                  False False True True False False) (String0 (Ascii False
                  False False False True True False False) (String0 (Ascii
                  False False False False True True False False) (String0
                  (Ascii True False False False True True False False)
                  EmptyString))))))))
                  (append (String0 (Ascii False False False False True True
                    False False) (String0 (Ascii True False False False True
                    True False False) (String0 (Ascii True False False False
                    True True False False) (String0 (Ascii False False False
                    False True True False False) (String0 (Ascii True False
                    False False True True False False) (String0 (Ascii False
                    False False False True True False False) (String0 (Ascii
                    False False False False True True False False) (String0
                    (Ascii False False False False True True False False)
                    EmptyString))))))))
                    (append (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii True False False False
                      True True False False) (String0 (Ascii False False
                      False False True True False False) (String0 (Ascii
                      False False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii False False False False True True False
                      False) (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii False False False False
                      True True False False) EmptyString)))))))) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii False False False False True True False
                      False) (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii True False False False
                      True True False False) (String0 (Ascii False False
                      False False True True False False) (String0 (Ascii True
                      False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii True False False False True True False
                      False) EmptyString)))))))))))))))))

log10_2 :: Int0
log10_2 =
  s2int80
    (append (String0 (Ascii False False False False True True False False)
      (String0 (Ascii False False False False True True False False) (String0
      (Ascii True False False False True True False False) (String0 (Ascii
      True False False False True True False False) (String0 (Ascii True
      False False False True True False False) (String0 (Ascii True False
      False False True True False False) (String0 (Ascii True False False
      False True True False False) (String0 (Ascii True False False False
      True True False False) EmptyString))))))))
      (append (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        EmptyString))))))))
        (append (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          EmptyString))))))))
          (append (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) EmptyString))))))))
            (append (String0 (Ascii True False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) EmptyString))))))))
              (append (String0 (Ascii True False False False True True False
                False) (String0 (Ascii False False False False True True
                False False) (String0 (Ascii False False False False True
                True False False) (String0 (Ascii False False False False
                True True False False) (String0 (Ascii False False False
                False True True False False) (String0 (Ascii True False False
                False True True False False) (String0 (Ascii False False
                False False True True False False) (String0 (Ascii False
                False False False True True False False) EmptyString))))))))
                (append (String0 (Ascii True False False False True True
                  False False) (String0 (Ascii True False False False True
                  True False False) (String0 (Ascii True False False False
                  True True False False) (String0 (Ascii True False False
                  False True True False False) (String0 (Ascii True False
                  False False True True False False) (String0 (Ascii False
                  False False False True True False False) (String0 (Ascii
                  True False False False True True False False) (String0
                  (Ascii True False False False True True False False)
                  EmptyString))))))))
                  (append (String0 (Ascii True False False False True True
                    False False) (String0 (Ascii True False False False True
                    True False False) (String0 (Ascii False False False False
                    True True False False) (String0 (Ascii False False False
                    False True True False False) (String0 (Ascii True False
                    False False True True False False) (String0 (Ascii True
                    False False False True True False False) (String0 (Ascii
                    True False False False True True False False) (String0
                    (Ascii True False False False True True False False)
                    EmptyString))))))))
                    (append (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii True False False False
                      True True False False) (String0 (Ascii True False False
                      False True True False False) (String0 (Ascii True False
                      False False True True False False) (String0 (Ascii
                      False False False False True True False False) (String0
                      (Ascii True False False False True True False False)
                      (String0 (Ascii True False False False True True False
                      False) (String0 (Ascii True False False False True True
                      False False) EmptyString)))))))) (String0 (Ascii True
                      False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii False False False False True True False
                      False) (String0 (Ascii True False False False True True
                      False False) (String0 (Ascii True False False False
                      True True False False) (String0 (Ascii False False
                      False False True True False False) (String0 (Ascii
                      False False False False True True False False) (String0
                      (Ascii True False False False True True False False)
                      EmptyString)))))))))))))))))

loge_2 :: Int0
loge_2 =
  s2int80
    (append (String0 (Ascii False False False False True True False False)
      (String0 (Ascii False False False False True True False False) (String0
      (Ascii True False False False True True False False) (String0 (Ascii
      True False False False True True False False) (String0 (Ascii True
      False False False True True False False) (String0 (Ascii True False
      False False True True False False) (String0 (Ascii True False False
      False True True False False) (String0 (Ascii True False False False
      True True False False) EmptyString))))))))
      (append (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii True False False False True True False False)
        (String0 (Ascii False False False False True True False False)
        EmptyString))))))))
        (append (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii False False False False True True False False)
          (String0 (Ascii True False False False True True False False)
          EmptyString))))))))
          (append (String0 (Ascii False False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) (String0 (Ascii True False False False True True False
            False) (String0 (Ascii False False False False True True False
            False) EmptyString))))))))
            (append (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii False False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) (String0 (Ascii True False False False True True False
              False) EmptyString))))))))
              (append (String0 (Ascii True False False False True True False
                False) (String0 (Ascii True False False False True True False
                False) (String0 (Ascii True False False False True True False
                False) (String0 (Ascii True False False False True True False
                False) (String0 (Ascii False False False False True True
                False False) (String0 (Ascii True False False False True True
                False False) (String0 (Ascii True False False False True True
                False False) (String0 (Ascii True False False False True True
                False False) EmptyString))))))))
                (append (String0 (Ascii True False False False True True
                  False False) (String0 (Ascii True False False False True
                  True False False) (String0 (Ascii False False False False
                  True True False False) (String0 (Ascii True False False
                  False True True False False) (String0 (Ascii False False
                  False False True True False False) (String0 (Ascii False
                  False False False True True False False) (String0 (Ascii
                  False False False False True True False False) (String0
                  (Ascii True False False False True True False False)
                  EmptyString))))))))
                  (append (String0 (Ascii True False False False True True
                    False False) (String0 (Ascii True False False False True
                    True False False) (String0 (Ascii False False False False
                    True True False False) (String0 (Ascii False False False
                    False True True False False) (String0 (Ascii True False
                    False False True True False False) (String0 (Ascii True
                    False False False True True False False) (String0 (Ascii
                    True False False False True True False False) (String0
                    (Ascii True False False False True True False False)
                    EmptyString))))))))
                    (append (String0 (Ascii False False False False True True
                      False False) (String0 (Ascii True False False False
                      True True False False) (String0 (Ascii True False False
                      False True True False False) (String0 (Ascii True False
                      False False True True False False) (String0 (Ascii True
                      False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii False False False False True True False
                      False) (String0 (Ascii True False False False True True
                      False False) EmptyString)))))))) (String0 (Ascii True
                      False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      (String0 (Ascii True False False False True True False
                      False) (String0 (Ascii False False False False True
                      True False False) (String0 (Ascii True False False
                      False True True False False) (String0 (Ascii True False
                      False False True True False False) (String0 (Ascii
                      False False False False True True False False) (String0
                      (Ascii False False False False True True False False)
                      EmptyString)))))))))))))))))

conv_load_fpconstant :: Int0 -> Conv Unit
conv_load_fpconstant c =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_int size80 c)) (\r ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (stk_push_and_set_tag r))
      (\overflow ->
      bind (unsafeCoerce conv_monad) (set_fpu_flag F_C1 overflow) (\x ->
        bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C0) (\x0 ->
          bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C2) (\x1 ->
            undef_fpu_flag F_C3)))))

conv_FLDZ :: Conv Unit
conv_FLDZ =
  conv_load_fpconstant (repr size80 Z0)

conv_FLD1 :: Conv Unit
conv_FLD1 =
  conv_load_fpconstant pos1

conv_FLDPI :: Conv Unit
conv_FLDPI =
  conv_load_fpconstant pi

conv_FLDL2T :: Conv Unit
conv_FLDL2T =
  conv_load_fpconstant log2_10

conv_FLDL2E :: Conv Unit
conv_FLDL2E =
  conv_load_fpconstant log2_e

conv_FLDLG2 :: Conv Unit
conv_FLDLG2 =
  conv_load_fpconstant log10_2

conv_FLDLN2 :: Conv Unit
conv_FLDLN2 =
  conv_load_fpconstant loge_2

farith_de :: Float_arith_op -> Rtl_exp -> Rtl_exp -> Rtl_exp -> Conv Rtl_exp
farith_de op rm e1 e2 =
  bind (unsafeCoerce conv_monad) (float79_of_de_float e1) (\e1' ->
    bind (unsafeCoerce conv_monad) (float79_of_de_float e2) (\e2' ->
      bind (unsafeCoerce conv_monad) (farith_float79 op rm e1' e2') (\res ->
        de_float_of_float79 res)))

conv_ifarith :: Float_arith_op -> Bool -> Prefix -> Bool -> Operand -> Conv
                Unit
conv_ifarith fop noreverse pre zerod op =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_ifp_op pre DS op))
    (\iopv ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce get_fpu_rctrl) (\rm ->
      bind (unsafeCoerce conv_monad)
        (unsafeCoerce (de_float_of_float32 iopv rm)) (\opv ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\topp ->
          bind (unsafeCoerce conv_monad) (unsafeCoerce (get_fpu_reg topp))
            (\st0 ->
            bind (unsafeCoerce conv_monad) (unsafeCoerce (is_empty_tag topp))
              (\underflow ->
              bind (unsafeCoerce conv_monad)
                (case zerod of {
                  True ->
                   case noreverse of {
                    True -> unsafeCoerce (farith_de fop rm st0 opv);
                    False -> unsafeCoerce (farith_de fop rm opv st0)};
                  False ->
                   case noreverse of {
                    True -> unsafeCoerce (farith_de fop rm opv st0);
                    False -> unsafeCoerce (farith_de fop rm st0 opv)}})
                (\res ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (float32_of_de_float res rm)) (\ires ->
                  bind (unsafeCoerce conv_monad)
                    (case op of {
                      Imm_op i -> raise_error;
                      Reg_op r -> set_reg ires r;
                      Address_op a ->
                       bind (unsafeCoerce conv_monad)
                         (unsafeCoerce (compute_addr a)) (\addr ->
                         set_mem32 DS ires addr);
                      Offset_op off ->
                       bind (unsafeCoerce conv_monad)
                         (unsafeCoerce
                           (load_int (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                             (S (S O))))))))))))))))))))))))))))))) off))
                         (\addr -> set_mem32 DS ires addr)}) (\x ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (choose size1)) (\v ->
                      bind (unsafeCoerce conv_monad)
                        (unsafeCoerce (load_Z size1 Z0)) (\zero2 ->
                        bind (unsafeCoerce conv_monad)
                          (unsafeCoerce (if_exp size1 underflow zero2 v))
                          (\c1 ->
                          bind (unsafeCoerce conv_monad)
                            (set_fpu_flag F_C1 c1) (\x0 ->
                            bind (unsafeCoerce conv_monad)
                              (undef_fpu_flag F_C0) (\x1 ->
                              bind (unsafeCoerce conv_monad)
                                (undef_fpu_flag F_C2) (\x2 ->
                                undef_fpu_flag F_C3)))))))))))))))

conv_farith :: Float_arith_op -> Bool -> Prefix -> Bool -> Fp_operand -> Conv
               Unit
conv_farith fop noreverse pre zerod op =
  bind (unsafeCoerce conv_monad) (unsafeCoerce (load_fp_op pre DS op))
    (\opv ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\topp ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce (get_fpu_reg topp))
        (\st0 ->
        bind (unsafeCoerce conv_monad) (unsafeCoerce (is_empty_tag topp))
          (\underflow ->
          bind (unsafeCoerce conv_monad) (unsafeCoerce get_fpu_rctrl) (\rm ->
            bind (unsafeCoerce conv_monad)
              (case zerod of {
                True ->
                 case noreverse of {
                  True -> unsafeCoerce (farith_de fop rm st0 opv);
                  False -> unsafeCoerce (farith_de fop rm opv st0)};
                False ->
                 case noreverse of {
                  True -> unsafeCoerce (farith_de fop rm opv st0);
                  False -> unsafeCoerce (farith_de fop rm st0 opv)}})
              (\res ->
              bind (unsafeCoerce conv_monad)
                (case zerod of {
                  True ->
                   case op of {
                    FPM16_op a -> raise_error;
                    FPM80_op a -> raise_error;
                    _ -> set_fpu_reg topp res};
                  False ->
                   case op of {
                    FPS_op i ->
                     bind (unsafeCoerce conv_monad)
                       (unsafeCoerce (freg_of_offset i)) (\fi ->
                       set_fpu_reg fi res);
                    _ -> raise_error}}) (\x ->
                bind (unsafeCoerce conv_monad) (unsafeCoerce (choose size1))
                  (\v ->
                  bind (unsafeCoerce conv_monad)
                    (unsafeCoerce (load_Z size1 Z0)) (\zero2 ->
                    bind (unsafeCoerce conv_monad)
                      (unsafeCoerce (if_exp size1 underflow zero2 v)) (\c1 ->
                      bind (unsafeCoerce conv_monad) (set_fpu_flag F_C1 c1)
                        (\x0 ->
                        bind (unsafeCoerce conv_monad) (undef_fpu_flag F_C0)
                          (\x1 ->
                          bind (unsafeCoerce conv_monad)
                            (undef_fpu_flag F_C2) (\x2 ->
                            undef_fpu_flag F_C3)))))))))))))

conv_farith_and_pop :: Float_arith_op -> Bool -> Prefix -> Fp_operand -> Conv
                       Unit
conv_farith_and_pop fop noreverse pre op =
  case op of {
   FPS_op i ->
    bind (unsafeCoerce conv_monad) (conv_farith fop noreverse pre False op)
      (\x -> stk_pop_and_set_tag);
   _ -> raise_error}

conv_FADD :: Prefix -> Bool -> Fp_operand -> Conv Unit
conv_FADD =
  conv_farith Fadd_op True

conv_FSUB :: Prefix -> Bool -> Fp_operand -> Conv Unit
conv_FSUB =
  conv_farith Fsub_op True

conv_FMUL :: Prefix -> Bool -> Fp_operand -> Conv Unit
conv_FMUL =
  conv_farith Fmul_op True

conv_FDIV :: Prefix -> Bool -> Fp_operand -> Conv Unit
conv_FDIV =
  conv_farith Fdiv_op True

conv_FIADD :: Prefix -> Bool -> Operand -> Conv Unit
conv_FIADD =
  conv_ifarith Fadd_op True

conv_FISUB :: Prefix -> Bool -> Operand -> Conv Unit
conv_FISUB =
  conv_ifarith Fsub_op True

conv_FIMUL :: Prefix -> Bool -> Operand -> Conv Unit
conv_FIMUL =
  conv_ifarith Fmul_op True

conv_FIDIV :: Prefix -> Bool -> Operand -> Conv Unit
conv_FIDIV =
  conv_ifarith Fdiv_op True

conv_FADDP :: Prefix -> Fp_operand -> Conv Unit
conv_FADDP =
  conv_farith_and_pop Fadd_op True

conv_FSUBP :: Prefix -> Fp_operand -> Conv Unit
conv_FSUBP =
  conv_farith_and_pop Fsub_op True

conv_FMULP :: Prefix -> Fp_operand -> Conv Unit
conv_FMULP =
  conv_farith_and_pop Fmul_op True

conv_FDIVP :: Prefix -> Fp_operand -> Conv Unit
conv_FDIVP =
  conv_farith_and_pop Fdiv_op True

conv_FSUBR :: Prefix -> Bool -> Fp_operand -> Conv Unit
conv_FSUBR =
  conv_farith Fsub_op False

conv_FDIVR :: Prefix -> Bool -> Fp_operand -> Conv Unit
conv_FDIVR =
  conv_farith Fdiv_op False

conv_FISUBR :: Prefix -> Bool -> Operand -> Conv Unit
conv_FISUBR =
  conv_ifarith Fsub_op False

conv_FIDIVR :: Prefix -> Bool -> Operand -> Conv Unit
conv_FIDIVR =
  conv_ifarith Fdiv_op False

conv_FSUBRP :: Prefix -> Fp_operand -> Conv Unit
conv_FSUBRP =
  conv_farith_and_pop Fsub_op False

conv_FDIVRP :: Prefix -> Fp_operand -> Conv Unit
conv_FDIVRP =
  conv_farith_and_pop Fdiv_op False

float_compare :: De_float -> De_float -> Comparison
float_compare a b =
  let {
   aR = b2R (Zpos (XO (XO (XO (XO (XO (XO XH))))))) (Zpos (XO (XO (XO (XO (XO
          (XO (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))))))) a}
  in
  let {
   bR = b2R (Zpos (XO (XO (XO (XO (XO (XO XH))))))) (Zpos (XO (XO (XO (XO (XO
          (XO (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))))))) b}
  in
  rcompare aR bR

set_CC_flags :: Comparison -> Conv Unit
set_CC_flags comp =
  case comp of {
   Eq ->
    bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C3 (Zpos XH)) (\x ->
      bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C2 Z0) (\x0 ->
        set_fpu_flag_const F_C0 Z0));
   Lt ->
    bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C3 Z0) (\x ->
      bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C2 Z0) (\x0 ->
        set_fpu_flag_const F_C0 (Zpos XH)));
   Gt ->
    bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C3 Z0) (\x ->
      bind (unsafeCoerce conv_monad) (set_fpu_flag_const F_C2 Z0) (\x0 ->
        set_fpu_flag_const F_C0 Z0))}

conv_FCOM :: (Option Fp_operand) -> Conv Unit
conv_FCOM op1 =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\topp ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (get_fpu_reg topp)) (\st0 ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce get_fpu_rctrl) (\rm ->
        case op1 of {
         Some op ->
          case op of {
           FPM32_op adr ->
            bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr adr))
              (\addr ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (load_mem32 DS addr)) (\val ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (de_float_of_float32 val rm)) (\d_val ->
                  undef_fpu_flag F_C3)));
           FPM64_op adr ->
            bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr adr))
              (\addr ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (load_mem64 DS addr)) (\val ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (de_float_of_float64 val rm)) (\d_val ->
                  undef_fpu_flag F_C3)));
           _ -> undef_fpu_flag F_C3};
         None -> undef_fpu_flag F_C3})))

conv_FICOM :: (Option Fp_operand) -> Conv Unit
conv_FICOM op1 =
  bind (unsafeCoerce conv_monad) (unsafeCoerce get_stktop) (\topp ->
    bind (unsafeCoerce conv_monad) (unsafeCoerce (get_fpu_reg topp)) (\st0 ->
      bind (unsafeCoerce conv_monad) (unsafeCoerce get_fpu_rctrl) (\rm ->
        case op1 of {
         Some op ->
          case op of {
           FPM32_op adr ->
            bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr adr))
              (\addr ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (load_mem32 DS addr)) (\val ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (de_float_of_float32 val rm)) (\d_val ->
                  undef_fpu_flag F_C3)));
           FPM64_op adr ->
            bind (unsafeCoerce conv_monad) (unsafeCoerce (compute_addr adr))
              (\addr ->
              bind (unsafeCoerce conv_monad)
                (unsafeCoerce (load_mem64 DS addr)) (\val ->
                bind (unsafeCoerce conv_monad)
                  (unsafeCoerce (de_float_of_float64 val rm)) (\d_val ->
                  undef_fpu_flag F_C3)));
           _ -> undef_fpu_flag F_C3};
         None -> undef_fpu_flag F_C3})))

conv_FCOMP :: (Option Fp_operand) -> Conv Unit
conv_FCOMP op1 =
  bind (unsafeCoerce conv_monad) (conv_FCOM op1) (\x -> stk_pop_and_set_tag)

conv_FCOMPP :: Conv Unit
conv_FCOMPP =
  bind (unsafeCoerce conv_monad) (conv_FCOMP None) (\x ->
    stk_pop_and_set_tag)

conv_FICOMP :: (Option Fp_operand) -> Conv Unit
conv_FICOMP op1 =
  bind (unsafeCoerce conv_monad) (conv_FICOM op1) (\x -> stk_pop_and_set_tag)

conv_FICOMPP :: Conv Unit
conv_FICOMPP =
  bind (unsafeCoerce conv_monad) (conv_FICOMP None) (\x ->
    stk_pop_and_set_tag)

instr_to_rtl :: Prefix -> Instr -> List Rtl_instr
instr_to_rtl pre i =
  runConv
    (bind (unsafeCoerce conv_monad) (check_prefix pre) (\x ->
      case i of {
       AAA -> conv_AAA_AAS Add_op;
       AAD -> conv_AAD;
       AAM -> conv_AAM;
       AAS -> conv_AAA_AAS Sub_op;
       ADC w op1 op2 -> conv_ADC pre w op1 op2;
       ADD w op1 op2 -> conv_ADD pre w op1 op2;
       AND w op1 op2 -> conv_AND pre w op1 op2;
       BOUND op1 op2 -> raise_trap;
       BSF op1 op2 -> conv_BSF pre op1 op2;
       BSR op1 op2 -> conv_BSR pre op1 op2;
       BSWAP r -> conv_BSWAP pre r;
       BT op1 op2 -> conv_BT False True pre op1 op2;
       BTC op1 op2 -> conv_BT False False pre op1 op2;
       BTR op1 op2 -> conv_BT True False pre op1 op2;
       BTS op1 op2 -> conv_BT True True pre op1 op2;
       CALL near abs0 op1 sel -> conv_CALL pre near abs0 op1 sel;
       CDQ -> conv_CDQ pre;
       CLC -> conv_CLC;
       CLD -> conv_CLD;
       CLI -> raise_trap;
       CLTS -> raise_trap;
       CMC -> conv_CMC;
       CMOVcc ct op1 op2 -> conv_CMOV pre True ct op1 op2;
       CMP w op1 op2 -> conv_CMP pre w op1 op2;
       CMPS w -> conv_CMPS pre w;
       CMPXCHG w op1 op2 -> conv_CMPXCHG pre w op1 op2;
       CPUID -> raise_trap;
       CWDE -> conv_CWDE pre;
       DAA -> conv_DAA_DAS Add_op (testcarryAdd size8);
       DAS -> conv_DAA_DAS Sub_op (testcarrySub size8);
       DEC w op1 -> conv_DEC pre w op1;
       DIV w op -> conv_DIV pre w op;
       HLT -> conv_HLT pre;
       IDIV w op -> conv_IDIV pre w op;
       IMUL w op1 op2 i0 -> conv_IMUL pre w op1 op2 i0;
       INC w op1 -> conv_INC pre w op1;
       Jcc ct disp -> conv_Jcc pre ct disp;
       JMP near abs0 op1 sel -> conv_JMP pre near abs0 op1 sel;
       LAHF -> conv_LAHF;
       LAR op1 op2 -> raise_trap;
       LEA op1 op2 -> conv_LEA pre op1 op2;
       LEAVE -> conv_LEAVE pre;
       LGS op1 op2 -> raise_trap;
       LOOP disp -> conv_LOOP pre False False disp;
       LOOPZ disp -> conv_LOOP pre True True disp;
       LOOPNZ disp -> conv_LOOP pre True False disp;
       MOV w op1 op2 -> conv_MOV pre w op1 op2;
       MOVCR direction cr r -> raise_trap;
       MOVDR direction dr r -> raise_trap;
       MOVSR direction sr op1 -> raise_trap;
       MOVBE op1 op2 -> raise_trap;
       MOVS w -> conv_MOVS pre w;
       MOVSX w op1 op2 -> conv_MOVSX pre w op1 op2;
       MOVZX w op1 op2 -> conv_MOVZX pre w op1 op2;
       MUL w op -> conv_MUL pre w op;
       NEG w op1 -> conv_NEG pre w op1;
       NOP op -> return (unsafeCoerce conv_monad) Tt;
       NOT w op1 -> conv_NOT pre w op1;
       OR w op1 op2 -> conv_OR pre w op1 op2;
       POP op -> conv_POP pre op;
       POPA -> conv_POPA pre;
       POPF -> raise_trap;
       PUSH w op -> conv_PUSH pre w op;
       PUSHSR sr -> raise_trap;
       PUSHA -> conv_PUSHA pre;
       PUSHF -> raise_trap;
       RCL w op1 op2 -> conv_RCL pre w op1 op2;
       RCR w op1 op2 -> conv_RCR pre w op1 op2;
       RDMSR -> raise_trap;
       RDPMC -> raise_trap;
       RDTSC -> raise_trap;
       RDTSCP -> raise_trap;
       RET ss disp -> conv_RET pre ss disp;
       ROL w op1 op2 -> conv_ROL pre w op1 op2;
       ROR w op1 op2 -> conv_ROR pre w op1 op2;
       RSM -> raise_trap;
       SAHF -> conv_SAHF;
       SAR w op1 op2 -> conv_SAR pre w op1 op2;
       SBB w op1 op2 -> conv_SBB pre w op1 op2;
       SCAS w -> raise_trap;
       SETcc ct op -> conv_SETcc pre ct op;
       SGDT op1 -> raise_trap;
       SHL w op1 op2 -> conv_SHL pre w op1 op2;
       SHLD op1 op2 ri -> conv_SHLD pre op1 op2 ri;
       SHR w op1 op2 -> conv_SHR pre w op1 op2;
       SHRD op1 op2 ri -> conv_SHRD pre op1 op2 ri;
       SIDT op1 -> raise_trap;
       SLDT op1 -> raise_trap;
       SMSW op1 -> raise_trap;
       STC -> conv_STC;
       STD -> conv_STD;
       STI -> raise_trap;
       STOS w -> conv_STOS pre w;
       STR op1 -> raise_trap;
       SUB w op1 op2 -> conv_SUB pre w op1 op2;
       TEST w op1 op2 -> conv_TEST pre w op1 op2;
       WBINVD -> raise_trap;
       XADD w op1 op2 -> conv_XADD pre w op1 op2;
       XCHG w op1 op2 -> conv_XCHG pre w op1 op2;
       XOR w op1 op2 -> conv_XOR pre w op1 op2;
       _ -> raise_error}))

rTL_step_list :: (List Rtl_instr) -> RTL Unit
rTL_step_list l =
  case l of {
   Nil -> return (unsafeCoerce rTL_monad) Tt;
   Cons i l' ->
    bind (unsafeCoerce rTL_monad) (interp_rtl i) (\x -> rTL_step_list l')}

bii :: Nat -> Nat
bii =
  id

empty_mem :: T6 Int8
empty_mem =
  Pair (zero1 (bii (S (S (S (S (S (S (S O))))))))) empty

empty_reg :: Fmap Register Int32
empty_reg reg =
  zero1
    (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))

empty_seg :: Fmap Segment_register Int32
empty_seg seg =
  zero1
    (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))

pc :: Int
pc =
  zero1
    (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))

empty_oracle :: Oracle
empty_oracle =
  Build_oracle (\a b -> zero1 (bii a)) Z0

init_machine :: Core_state
init_machine =
  Build_core_state empty_reg empty_seg (\seg_reg ->
    repr
      (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
      (max_unsigned
        (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))
    (\f -> zero1 (bii O)) (\c ->
    zero1
      (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) (\d ->
    zero1
      (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) pc

empty_fpu_machine :: Fpu_state
empty_fpu_machine =
  Build_fpu_state (\fpr ->
    zero1
      (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (zero1
      (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))
    (zero1
      (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))
    (\t -> zero1 (bii (S O)))
    (zero1
      (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))
    (zero1
      (bii (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))
    (zero1 (bii (S (S (S (S (S (S (S (S (S (S O))))))))))))

init_full_machine :: Mach_state
init_full_machine =
  Build_mach init_machine empty_fpu_machine

init_rtl_state :: Rtl_state
init_rtl_state =
  Build_rtl_state empty_oracle init_full_machine empty_mem

no_prefix :: Prefix
no_prefix =
  MkPrefix None None False False

four :: Int32
four =
  Zpos (XO (XO XH))

six :: Int32
six =
  Zpos (XO (XI XH))

eax_plus :: Int32 -> List Rtl_instr
eax_plus n =
  instr_to_rtl no_prefix (ADD False (Reg_op EAX) (Imm_op n))

add3 :: Int32 -> Int32 -> List Rtl_instr
add3 n m =
  app (eax_plus n) (eax_plus m)

run :: (List Rtl_instr) -> Prod (RTL_ans Unit) Rtl_state
run p =
  rTL_step_list p init_rtl_state

four_plus_six :: Prod (RTL_ans Unit) Int32
four_plus_six =
  let {s = run (add3 four six)} in
  Pair (fst s) (gp_regs (core (rtl_mach_state (snd s))) EAX)

main :: Prelude.IO ()
main = Prelude.print four_plus_six



