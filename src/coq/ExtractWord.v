Require Import Bits.
Import Word.
Require Import SpaceSearch.
Require Import Rosette.
Require Import Full.

Extract Constant Word.repr => "word-mkint".
Extract Constant Word.zero => "word-zero".
Extract Constant Word.one => "word-one".
Extract Constant Word.mone => "word-mone".
Extract Constant Word.eq => "word-eq".
Extract Constant Word.lt => "word-lt".
Extract Constant Word.ltu => "word-ltu".
Extract Constant Word.add => "word-add".
Extract Constant Word.sub => "word-sub".
Extract Constant Word.mul => "word-mul".
Extract Constant Word.divs => "word-divs".
Extract Constant Word.divu => "word-divu".
Extract Constant Word.modu => "word-divu".
Extract Constant Word.mods => "word-mods".
Extract Constant Word.and => "word-and".
Extract Constant Word.or => "word-or".
Extract Constant Word.xor => "word-xor".
Extract Constant Word.shl => "word-shl".
Extract Constant Word.shr => "word-shr".
Extract Constant Word.shru => "word-shru".
Extract Constant Word.ror => "word-ror".
Extract Constant Word.rol => "word-rol".

Extract Constant Word.unsigned => "(lambdas (_) (error 'unsigned))".
Extract Constant Word.signed => "(lambdas (_) (error 'signed))".

Parameter fullIntSpace : forall n, Space (int n).
Axiom fullIntSpaceOk : forall n, ⟦ fullIntSpace n ⟧ = Full_set (int n).

Extract Constant fullIntSpace => "word-free".

Instance fullInt n : @Full rosette (int n) := {| 
  full := fullIntSpace n; 
  denoteFullOk := fullIntSpaceOk n
|}.

Notation "# n" := (mkint _ n _) (at level 45).

Arguments Word.mone {_}.
