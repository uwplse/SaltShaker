Require Import X86Semantics.
Import X86_RTL.
Import X86_Compile.
Import X86_MACHINE.
Require Import Maps.
Import PTree.
Require Import Bits.
Require Import List.
Import ListNotations.
Require Import Rosette.
Require Import SpaceSearch.
Import BinNums.
Import Word.
Require Import Coq.PArith.BinPos.
Import Pos.

(* initialize state, inspired by see simulator/test.ml *)

Definition mkint := Word.mkint.
Notation "# n" := (mkint _ n _) (at level 45).

Lemma maxIntIsInt bits : 
   BinInt.Z.le 0 (max_unsigned bits) /\
   BinInt.Z.lt (max_unsigned bits) (modulus bits).
Proof.
  unfold max_unsigned.
  split.
  - compute; congruence.
  - omega.
Qed.

Definition maxInt bits : int bits.
  refine (# (Word.max_unsigned bits)).
  apply maxIntIsInt.
Defined.

Definition bii := id (A:=nat).

Definition empty_mem : AddrMap.t int8 := (@Word.zero (bii 7), PTree.empty _).
Definition empty_reg : fmap register int32 := (fun reg => @Word.zero (bii 31)).
Definition empty_seg : fmap segment_register int32 := (fun seg => @Word.zero (bii 31)).
Definition pc := @Word.zero (bii 31).

Definition empty_oracle : oracle.
  refine {|
    oracle_bits := (fun a b => @Word.zero (bii a)); (* originally: zero_big_int) *)
    oracle_offset := 0 (* originally: zero_big_int  *)
  |}.
Defined.

Definition init_machine : core_state. 
  refine {|
    gp_regs := empty_reg;
    seg_regs_starts := empty_seg;
    seg_regs_limits := (fun seg_reg=>maxInt (bii 31));
    flags_reg := (fun f => @Word.zero (bii 0));
    control_regs := (fun c => @Word.zero (bii 31));
    debug_regs :=  (fun d => @Word.zero (bii 31));
    pc_reg := pc
  |}.
Defined.

Definition empty_fpu_machine : fpu_state.
refine {|
  fpu_data_regs := (fun fpr => (* @Word.repr(bii 2) *) (@Word.zero(bii 79)));
  fpu_status := @Word.zero(bii 15);
  fpu_control := @Word.zero(bii 15);
  fpu_tags := (fun t => (* @Word.repr(bii 2) *) (@Word.zero(bii 1)));
  fpu_lastInstrPtr := @Word.zero(bii 47);
  fpu_lastDataPtr := @Word.zero(bii 47);
  fpu_lastOpcode := @Word.zero(bii 10) (* originally: (bii 2) *)
|}.
Defined.

Definition init_full_machine : mach_state.
  refine {|
   core := init_machine;
   fpu := empty_fpu_machine
  |}.
Defined.

Definition init_rtl_state : rtl_state.
  refine {|
    rtl_oracle := empty_oracle;
    rtl_mach_state := init_full_machine;
    rtl_memory := empty_mem
  |}.
Defined.


(* Define an instruction *)

(*
Finally, an instruction can have one instruction prefixes from each of the four groups: (1) lock and repeat prefixes, (2) segment override prefixes, (3) operand-size override prefix, and (4) address-size override prefix. In 64-bit mode, REX prefixes are used for specifying GPRs and SSE registers, 64-bit operand size, and extended control registers. Each instruction can have only one REX prefix at a time.

http://penberg.blogspot.com/2010/04/short-introduction-to-x86-instruction.
*)
Definition no_prefix : prefix := mkPrefix None None false false.

Definition four : int32. 
  refine (#4).
  compute.
  constructor; congruence.
Defined.

Definition six : int32. 
  refine (#6).
  compute.
  constructor; congruence.
Defined.

(* Imm_op = Immediate operand = constant *)
Definition eax_plus n := instr_to_rtl no_prefix (ADD false (Reg_op EAX) (Imm_op n)).

Definition fast_eax_plus (n:int32) := [set_loc_rtl 
  (cast_u_rtl_exp 31
    (arith_rtl_exp add_op
      (cast_u_rtl_exp 7 (get_loc_rtl_exp (reg_loc EAX)))
      (cast_u_rtl_exp 7 (imm_rtl_exp n)))) 
  (reg_loc EAX)].

Definition nofast_eax_plus (n:int32) := [set_loc_rtl 
  (cast_u_rtl_exp 31
    (arith_rtl_exp add_op
      (cast_u_rtl_exp 7 (get_loc_rtl_exp (reg_loc EAX)))
      (cast_u_rtl_exp 7 (imm_rtl_exp n)))) 
  (reg_loc EAX)].

Definition add n m := fast_eax_plus n ++ fast_eax_plus m.

Definition run p := RTL_step_list p init_rtl_state.

Definition natId (n:int32) := 
  let s := run [set_loc_rtl 
  (arith_rtl_exp add_op
    (get_loc_rtl_exp (reg_loc EAX))
    (imm_rtl_exp n))
  (reg_loc EAX)] in
    gp_regs (core (rtl_mach_state (snd s))) EAX.

(* Run the instruction *)
Definition four_plus_six :=
  let s := run (add four six) in
    (fst s, gp_regs (core (rtl_mach_state (snd s))) EAX).

Compute four_plus_six.

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

(* 
Translate a positive number to the following binary number:

xI (xO (xI (xO (xH))))
|   |   |   |   |
v   v   v   v   v
1   0   1   0   1 0 0 0 0 0 ...
^
'- least significant

1   2   4   8  16

= 1 + 4 + 16 = 21
*)

Definition boolSpace `{SpaceSearch} : Space bool :=
  union (single true) (single false).

(* efficient representation of all lists of length n *)
Fixpoint listSpace `{SpaceSearch} {A} (s:Space A) (n:nat) : Space (list A) :=
  match n with
  | 0%nat => single []
  | S n => bind (listSpace s n) (fun l => 
          bind s (fun a => single (a :: l)))
  end.

Compute @listSpace listSpaceSearch bool boolSpace 2.

(* creates an efficient space of all the positive numbers with n bits followed by xH *)
Fixpoint positiveSpace `{SpaceSearch} (n:nat) : Space positive.
  refine (match n with
  | 0%nat => single xH
  | S n => bind (positiveSpace _ n)
               (fun x => (union (single (xO x)) (single (xI x))))
  end).
Defined.

(* creates an efficient space of all the positive numbers with n bits *)
Fixpoint positiveSpace' `{SpaceSearch} (n:nat) : Space positive.
  refine (match n with
  | 0%nat => empty
  | S n => union (positiveSpace' _ n) (positiveSpace n)
  end).
Defined.

Compute @positiveSpace' listSpaceSearch 0.
Compute @positiveSpace' listSpaceSearch 1.
Compute @positiveSpace' listSpaceSearch 2.
Compute @positiveSpace' listSpaceSearch 3.
Compute @positiveSpace' listSpaceSearch 4.

Search (positive -> positive -> bool).

(* this is fast for reasonable p :) *)
Definition constructPositiveSpace (p:nat) : Space positive :=
  positiveSpace p.

(* this takes ages for reasonable p :( *)
Definition trivialPositiveVerification (p:nat) : option positive.
  refine (search _).
  refine (bind (positiveSpace p) (fun n => _)).
  refine (if eqb n n then empty else single n).
Defined.

(*
they use the stdlib module ExtrOcamlZBigInt to extract Z to Ocaml's big_int 

https://github.com/maximedenes/native-coq/blob/master/plugins/extraction/ExtrOcamlZBigInt.v

Extract Constant Z.add => "Big.add".
Extract Constant Z.succ => "Big.succ".
Extract Constant Z.pred => "Big.pred".
Extract Constant Z.sub => "Big.sub".
Extract Constant Z.mul => "Big.mult".
Extract Constant Z.opp => "Big.opp".
Extract Constant Z.abs => "Big.abs".
Extract Constant Z.min => "Big.min".
Extract Constant Z.max => "Big.max".
Extract Constant Z.compare => "Big.compare_case Eq Lt Gt".

Extract Constant Z.of_N => "fun p -> p".
Extract Constant Z.abs_N => "Big.abs".
*)

Extraction Language Scheme.

Print Word.int.

Print cast_unsigned.

(* Extract Inductive Word.int => "integer" [ "word-mkint" ]. *)
Extract Constant mkint => "word-mkint".
Extract Constant Word.zero => "word-zero".
Extract Constant Word.one => "word-one".
Extract Constant Word.add => "word-add".
Extract Constant Word.eq => "word-eq".
Extract Constant Word.repr => "word-mkint".
Extract Constant cast_unsigned => "word-unsigned-cast".
Extract Constant cast_signed => "(lambdas (bits n) (error 'signed-cast))".
Extract Constant Word.unsigned => "(lambdas (bits n) (error 'unsigned))".
Extract Constant Word.signed => "(lambdas (bits n) (error 'signed))".

Parameter freeIntSpace : forall n, Space (int n).
Axiom freeIntSpaceOk : forall n (a : int n), contains a (freeIntSpace n). 
Extract Constant freeIntSpace => "word-free".

Instance freeInt n : @Free rosette (int n) := {| 
  free := freeIntSpace n; 
  freeOk := freeIntSpaceOk n 
|}.

Compute (maxInt 31).

Definition findWordProposition (bits:nat) (x:int bits) : option (int bits).
  refine (if Word.eq x (maxInt bits) then Some x else None).
Defined.

Definition verifyForall {A} {B} `{Free A} (p:A -> option B) : option B.
  refine (search _).
  refine (bind (free A) (fun a => _)).
  refine (match p a with Some b => single b | None => empty end).
Defined.

Definition findWord (bits:nat) : option (int bits) :=
  verifyForall (findWordProposition bits).

Definition wordVerification (bits:nat) : option (int bits * int bits).
  refine (search _).
  refine (bind (free (int bits)) (fun x => _)).
  refine (bind (free (int bits)) (fun y => _)).
  refine (if Word.eq (Word.add x y) (Word.add y x) 
          then empty
          else single (x, y)).
Defined.

Definition initRTLState (_:unit) := init_rtl_state.

Definition instructionVerificationProposition (nm:int32 * int32) : option (int32 * int32 * int32 * int32).
  refine (let n := fst nm in _).
  refine (let m := snd nm in _).
  refine (let s := run (add n m) in _).
  refine (let r' := Word.add n m in _).
  refine (let r := gp_regs (core (rtl_mach_state (snd s))) EAX in _).
  refine (match fst s with 
  | Okay_ans _ => _
  | _ => Some (n,m,r,r')
  end).
  refine (if Word.eq r r' then None else Some (n,m,r,r')).
Defined.

(*
Goal forall nm, instructionVerificationProposition nm = None.
  intros [n m].
  unfold instructionVerificationProposition.
  unfold run.
  unfold RTL_step_list.

  match goal with |- (if ?A then _ else _) = None => destruct A eqn:h end.
  simpl.
  reflexivity.
  exfalso.

  Check unsigned.
  

  break_match.
*)

Existing Instance freeProd.

Definition instructionVerification (_:unit) := verifyForall instructionVerificationProposition.

Extraction "x86sem" constructPositiveSpace wordVerification instructionVerification trivialPositiveVerification findWord findWordProposition instructionVerificationProposition initRTLState.
