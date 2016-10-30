Require Import X86Semantics.
Import X86_RTL.
Import X86_Compile.
Import X86_MACHINE.
Require Import Maps.
Require Import Bits.
Require Import List.
Require Import Coq.PArith.BinPos.
Require Import Bool.
Import ListNotations.
Import PTree.
Import Pos.
Import BinNums.
Import Word.
Require Import Basic.
Require Import Rosette.Unquantified.
Require Import Precise.
Require Import Full.
Require Import ExtractWord.
Require Import InitState.
Require Import SharedState.
Require Import JamesTactics.
Require Import Coq.Logic.Classical_Pred_Type.

Extract Constant cast_unsigned => "word-castu".
Extract Constant cast_signed => "word-casts".

Existing Instance rosetteBasic.
Existing Instance rosetteSearch.

Extraction Language Scheme.

(*
Finally, an instruction can have one instruction prefixes from each of the four groups: (1) lock and repeat prefixes, (2) segment override prefixes, (3) operand-size override prefix, and (4) address-size override prefix. In 64-bit mode, REX prefixes are used for specifying GPRs and SSE registers, 64-bit operand size, and extended control registers. Each instruction can have only one REX prefix at a time.

Imm_op = Immediate operand = constant

http://penberg.blogspot.com/2010/04/short-introduction-to-x86-instruction.
*)
Definition testSharedState : SharedState := {| 
  eax := repr 129786124931; ecx := repr 456123421348; 
  edx := repr 982483124977; ebx := repr 123497821934; 
  esp := repr 321497821397; ebp := repr 194378923143;
  esi := repr 102394758154; edi := repr 195263126789;
  cf := repr 1; pf := repr 0; zf := repr 0; 
  sf := repr 1; of := repr 0
|}.

Set Printing Width 78.

(*
(Pair (MkPrefix (None) (None) (True) (False)) (IMUL (True) (Reg_op (ECX)) (Some (Reg_op (EBX))) (Some (bv 65504 32))))

*)

(* Debug an instruction in here: *)
Goal False.
  refine (let p := mkPrefix None None true false in _).
  refine (let i : instr := IMUL true (Reg_op ECX) (Some (Reg_op EBX)) (Some (repr 65504)) in _).
  (* refine (let i : instr := BSF (Reg_op EAX) (Reg_op EBX) in _). *)
  refine (let r := instr_to_rtl p i in _).
  unfold instr_to_rtl, runConv in r; simpl in r.
  refine (let s : SharedState := {| 
    eax := repr 0; ecx := repr 0; 
    edx := repr 0; ebx := repr 1024;
    esp := repr 0; ebp := repr 0;
    esi := repr 0; edi := repr 0;
    cf := repr 0; pf := repr 0; zf := repr 0; 
    sf := repr 0; of := repr 0
  |} in _).
(*  refine (let s := testSharedState in _). *)
  refine (let s' := RTL_step_list (instr_to_rtl p i) (shared_rtl_state empty_oracle s) in _).
  refine (let gpr := gp_regs (core (rtl_mach_state (snd s'))) in _).
  refine (let fgs := flags_reg (core (rtl_mach_state (snd s'))) in _).
  Compute (gpr EAX).
  Compute (fgs CF).
  Compute (fgs OF).
Abort.

Definition instrToRTL (pi:prefix * instr) : list rtl_instr :=
  instr_to_rtl (fst pi) (snd pi).

Definition runRocksalt' (pi:prefix * instr) (o:oracle) (s:SharedState) : option SharedState.
  refine (let r := RTL_step_list (instrToRTL pi) (shared_rtl_state o s) in _).
  refine (match r with 
  | (Okay_ans tt, s') => Some (rtl_state_shared s')
  | _ => None
  end).
Defined.

Parameter existsWord : forall {n:nat}, (int n -> bool) -> bool.
Extract Constant existsWord => "(lambdas (n f) 
  (define-symbolic existentially-quantified (bitvector (word-bits->bv-bits n)))
  (if (exists (list existentially-quantified) 
    (match (f existentially-quantified)
      ((True)  #t)
      ((False) #f))) '(True) '(False)))".

Axiom existsWordOk : forall n f, existsWord f = true <-> exists w : Word.int n, f w = true.

Section Instr.

Variable uninterpretedBitsSpec : nat.
Variable runX86Spec : Word.int uninterpretedBitsSpec -> SharedState -> option SharedState.
Variable rocksaltInstr : prefix * instr. 

Definition runRocksalt o s := runRocksalt' rocksaltInstr o s. 

Section InstrEq.

Variable eq:SharedState -> SharedState -> bool.

Definition instrEq (u:Word.int uninterpretedBitsSpec) (o:oracle) (s:SharedState) : option (SharedState * option SharedState * option SharedState).
  refine (let s0 := runX86Spec u s in _).
  refine (let s1 := runRocksalt o s in _).
  refine (let error := Some (s, s0, s1) in _).
  refine (match s0,s1 with 
  | None, None => None
  | Some s0', Some s1' => _
  | _,_ => error
  end).
  refine (if eq s0' s1' then None else error).
Defined.

Definition testInstrEq : option (SharedState * option SharedState * option SharedState).
  exact (instrEq Word.zero empty_oracle testSharedState).
Defined.

Definition someOracle (f:Word.int 5) (r:Word.int 15) : oracle. 
  refine {|
    oracle_bits s z := match s with 
                       | 0%nat => cast_unsigned (Word.shr f (repr z))
                       | 15%nat => r
                       | _ => Word.zero 
                       end;
    oracle_offset := 0
  |}.
Defined.

Definition spaceInstrEq : Space (SharedState * option SharedState * option SharedState).
  refine (all (fun u : Word.int uninterpretedBitsSpec => _)).
  refine (all (fun s : SharedState => _)).
  refine (if (_:bool) then empty else single _).
  - refine (existsWord (fun f => _)).
    refine (match instrEq u (someOracle f (cast_unsigned u)) s with 
    | Some r => false (* non-equal *)
    | None =>   true  (* equal *)
    end).
  - refine (match instrEq u (someOracle Word.zero (cast_unsigned u)) s with 
    | Some r => r
    | None => (s, Some s, Some s) (* this should never happen *)
    end).
Defined.

Definition verifyInstrEq : option (SharedState * option SharedState * option SharedState).
  refine (match Precise.search spaceInstrEq with 
          | uninhabited => None 
          | solution a => Some a 
          end).
Defined.

End InstrEq.

Set Implicit Arguments.

Section Specification.
  Variable A B : Type.

  Class Specification := {
    specification : A -> B -> Type
  }.
  
  Context `{Specification}.
  Definition spec := specification.

  Class Implementation := {
    implementation : A -> B;
    implementsSpecification : forall a, spec a (implementation a)
  }.

  Context `{Implementation}.
  Definition impl := implementation.
End Specification.

Arguments Implementation {_ _} _.

Instance X86 : Specification SharedState (option SharedState) := {| 
  specification s s' := {u : _ & runX86Spec u s = s'}
|}.

Require Import FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.
Axiom prop_ext : prop_extensionality. 

Lemma emptyNot {A s} : s = Empty_set A -> (forall a, ~(s a)).
  rewrite emptyIsFalse.
  intros h a.
  rewrite h.
  intuition.
Qed.

Definition verifyInstrProp : 
  (SharedState * option SharedState * option SharedState) +
  (forall s0 (P:_ -> Prop) (h:forall o, P (runRocksalt o s0)) (cpu:Implementation X86), P (impl s0)).
Proof.
  destruct (verifyInstrEq (fun s0 s1 => if shared_state_eq_dec s0 s1 then true else false)) as [s'|] eqn:eq.
  - left.
    exact s'.
  - right.
    intros.
    destruct cpu as [cpu cpuSpec].
    simpl in *.
    specialize (cpuSpec s0).
    destruct cpuSpec as [u cpuSpec].
    rewrite <- cpuSpec.
    clear cpuSpec cpu.
    unfold verifyInstrEq in eq.
    break_match; [congruence|].
    clear eq; rename Heqr into eq.
    apply searchUninhabited in eq.
    unfold spaceInstrEq in eq.
    rewrite denoteAllOk in eq.
    eapply emptyNot in eq.
    apply not_ex_all_not with (n := u) in eq.
    refine ((fun h' => _) (@denoteAllOk)).
    rewrite h' in eq; clear h'.
    apply not_ex_all_not with (n := s0) in eq.
    break_match; revgoals. {
      exfalso.
      apply eq; clear eq.
      refine ((fun h' => _) (@denoteSingleOk)).
      rewrite h'; clear h'.
      rewrite singletonIsEqual.
      reflexivity.
    } 
    clear eq; rename Heqb into eq.
    rewrite existsWordOk in eq.
    destruct eq as [w eq].
    break_match; [congruence|].
    clear eq; rename Heqo into eq.
    unfold instrEq in eq.
    break_match; revgoals; clear Heqo.
    + (* returned invalid state *)
      break_match; [congruence|].
      clear eq; rename Heqo into eq.
      rewrite <- eq.
      apply h.
    + (* returned valid state *)
      break_match; [|congruence].
      rename Heqo into eq'.
      break_match; [|congruence].
      break_match; [|congruence].
      subst.
      rewrite <- eq'.
      apply h.
Defined.

End Instr.

Extraction "x86sem" instrEq testInstrEq spaceInstrEq verifyInstrEq 
  runRocksalt instrToRTL
  shared_state_eq eax ecx edx ebx esp ebp esi edi cf pf zf sf of.
