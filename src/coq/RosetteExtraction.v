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

(* Perform extraction *)
Extraction Language Scheme.

Existing Instance rosette.

Definition threehundred : int32.
  compute.
  refine {| Word.intval := 300 |}.
  compute.
  intuition congruence.
Defined.

Definition zero : int32.
  compute.
  refine {| Word.intval := 0 |}.
  compute.
  intuition congruence.
Defined.

Definition inputs : Space (int32).
  refine (union (single zero) (single threehundred)).
(* 
  refine (single threehundred).
  refine (union (union (single four) (single six)) (single threehundred)). *)
Defined.

Definition verification : option (int32 * int32 * (RTL_ans unit + int32)).
  refine (search _).
  refine (bind inputs (fun n => _)).
  refine (bind inputs (fun m => _)).
  refine (let s := run (add n m) in _).
  refine (match (fst s) with 
  | Okay_ans _ => _
  | a => single (n,m,inl a)
  end).
  refine (let r := gp_regs (core (rtl_mach_state (snd s))) EAX in _).
  refine (if Word.eq (Word.add n m) r then empty else single (n,m,inr r)).
Defined.

(* they use the stdlib module ExtrOcamlZBigInt to extract Z to Ocaml's big_int *)
Extraction "x86sem" verification.

