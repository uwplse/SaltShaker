Require Import X86.
Require Import Rosette.

(* Perform extraction *)
Extraction Language Scheme.

Extraction "x86sem" four_plus_six.

Existing Instance rosette.

Definition inputs : Space (int32).
  refine (single four).
Defined.

Definition verification : option (int32 * int32 * (RTL_ans unit + int32)).
  refine (search _).
  refine (bind inputs (fun n => _)).
  refine (bind inputs (fun m => _)).
  refine (let s := run (add n m) in _).
  refine (match (fst s) with 
  | Okay_ans _ => _
  | a => single (n,n,inl a)
  end).
  refine (let r := gp_regs (core (rtl_mach_state (snd s))) EAX in _).
  refine (if Word.eq (Word.add n m) r then empty else single (n,m,inr r)).
Defined.

(* they use the stdlib module ExtrOcamlZBigInt to extract Z to Ocaml's big_int *)
Extraction "x86sem" verification.

