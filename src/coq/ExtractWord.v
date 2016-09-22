Require Import Bits.
Import Word.
Require Import SpaceSearch.
Require Import Rosette.

Extract Constant Word.repr => "word-mkint".
Extract Constant Word.zero => "word-zero".
Extract Constant Word.one => "word-one".
Extract Constant Word.mone => "word-mone".
Extract Constant Word.eq => "word-eq".
Extract Constant Word.lt => "word-lt".
Extract Constant Word.ltu => "word-ltu".

Extract Constant Word.unsigned => "(lambdas (_) (error 'unsigned))".
Extract Constant Word.signed => "(lambdas (_) (error 'signed))".

Extract Constant Word.add => "word-add".
Extract Constant Word.sub => "(lambdas (_) (error 'sub))".
Extract Constant Word.mul => "(lambdas (_) (error 'mul))".
Extract Constant Word.divs => "(lambdas (_) (error 'divs))".
Extract Constant Word.divu => "(lambdas (_) (error 'divu))".
Extract Constant Word.modu => "(lambdas (_) (error 'modu))".
Extract Constant Word.mods => "(lambdas (_) (error 'mods))".
Extract Constant Word.and => "word-and".
Extract Constant Word.or => "word-or".
Extract Constant Word.xor => "word-xor".
Extract Constant Word.shl => "word-shl".
Extract Constant Word.shr => "word-shr".
Extract Constant Word.shru => "word-shru".
Extract Constant Word.ror => "(lambdas (_) (error 'ror))".
Extract Constant Word.rol => "(lambdas (_) (error 'rol))".

Parameter freeIntSpace : forall n, Space (int n).
Axiom freeIntSpaceOk : forall n (a : int n), contains a (freeIntSpace n). 
Extract Constant freeIntSpace => "word-free".

Instance freeInt n : @Free rosette (int n) := {| 
  free := freeIntSpace n; 
  freeOk := freeIntSpaceOk n 
|}.

Notation "# n" := (mkint _ n _) (at level 45).

Arguments Word.mone {_}.
