Require Import X86Semantics.
Import X86_RTL.
Import X86_Compile.
Import X86_MACHINE.
Require Import Maps.
Import PTree.
Require Import Bits.
Require Import List.
Import ListNotations.
Require Import SpaceSearch.
Require Import Rosette.
Require Import X86.
Import BinNums.
Import Word.

Extraction Language Scheme.

(* Existing Instance listSpaceSearch. *)
Existing Instance rosette.

Definition threehundred : int32.
  compute.
  refine {| Word.intval := 300 |}.
  compute.
  intuition congruence.
Defined.

Definition zero : int32.
  refine {| Word.intval := 0 |}.
  compute.
  intuition congruence.
Defined.

Fixpoint positives (n:nat) : Space positive.
  refine (match n with
  | 0 => single xH
  | S n => let i := positives n in _
  end).
  refine (union (single xH) _).
  refine (bind i (fun x => (union (single (xI x)) (single (xO x))))).
Defined.

Axiom ADMIT : forall A, A.

Definition int32s (n:nat) : Space int32.
  refine (union (single zero) _).
  refine (bind (positives n) (fun x => _)).
  refine (single {| intval := Zpos x |}).
  intuition.
  apply ADMIT.
Defined.

Definition verification : option (int32 * int32 * (RTL_ans unit + int32)).
  refine (let p := 3 in _).
  refine (search _).
  refine (bind (int32s p) (fun n => _)).
  refine (bind (int32s p) (fun m => _)).
  refine (let s := run (X86.add n m) in _).
  refine (match (fst s) with 
  | Okay_ans _ => _
  | a => single (n,m,inl a)
  end).
  refine (let r := gp_regs (core (rtl_mach_state (snd s))) EAX in _).
  refine (if Word.eq (Word.add n m) r then empty else single (n,m,inr r)).
Defined.

(* they use the stdlib module ExtrOcamlZBigInt to extract Z to Ocaml's big_int *)
Extraction "x86sem" verification.

