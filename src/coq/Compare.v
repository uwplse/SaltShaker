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
Require Import SpaceSearch.
Require Import Rosette.
Require Import Full.
Require Import ExtractWord.
Require Import InitState.
Require Import SharedState.

Extract Constant cast_unsigned => "word-unsigned-cast".
Extract Constant cast_signed => "(lambdas (srcBits dstBits x) (error 'signed-cast))".

Existing Instance rosette.

Extraction Language Scheme.

(*
Finally, an instruction can have one instruction prefixes from each of the four groups: (1) lock and repeat prefixes, (2) segment override prefixes, (3) operand-size override prefix, and (4) address-size override prefix. In 64-bit mode, REX prefixes are used for specifying GPRs and SSE registers, 64-bit operand size, and extended control registers. Each instruction can have only one REX prefix at a time.

Imm_op = Immediate operand = constant

The boolean passed to instructions toggels betweeen 8bit (false) and 32bit (true)

http://penberg.blogspot.com/2010/04/short-introduction-to-x86-instruction.
*)
Definition no_prefix : prefix := mkPrefix None None false false.

(* Debug an instruction in here: *)
Goal False.
  refine (let p := no_prefix in _).
  refine (let i : instr := ADD true (Reg_op EAX) (Reg_op EBX) in _).
  refine (let r := instr_to_rtl p i in _).
  unfold instr_to_rtl, runConv in r; simpl in r.
  refine (let s : SharedState := {| 
    eax := one;    ecx := repr 0; 
    edx := repr 0; ebx := mone;
    esp := repr 0; ebp := repr 0;
    esi := repr 0; edi := repr 0;
    cf := repr 0; pf := repr 0; af := repr 0;
    zf := repr 0; sf := repr 0; of := repr 0
  |} in _).
  refine (let s' := RTL_step_list (instr_to_rtl p i) (shared_rtl_state s) in _).
  refine (let gpr := gp_regs (core (rtl_mach_state (snd s'))) in _).
  refine (let fgs := flags_reg (core (rtl_mach_state (snd s'))) in _).
  Compute (gpr EAX).
  Compute (fgs ZF).
Abort.



(* Debug an instruction in here: *)
Goal False.
  refine (let p := no_prefix in _).
  refine (let i : instr := SUB true (Reg_op EAX) (Reg_op EBX) in _).
  refine (let r := instr_to_rtl p i in _).
  unfold instr_to_rtl, runConv in r; simpl in r.
  refine (let s : SharedState := {| 
    eax := repr 2147483645; ecx := repr 0; 
    edx := repr 0; ebx := repr 2147483648;
    esp := repr 0; ebp := repr 0;
    esi := repr 0; edi := repr 0;
    cf := repr 0; pf := repr 0; af := repr 0;
    zf := repr 0; sf := repr 0; of := repr 0
  |} in _).
  refine (let s' := RTL_step_list (instr_to_rtl p i) (shared_rtl_state s) in _).
  refine (let gpr := gp_regs (core (rtl_mach_state (snd s'))) in _).
  refine (let fgs := flags_reg (core (rtl_mach_state (snd s'))) in _).
  Compute (gpr EAX).
  Compute (fgs OF).
Abort.

Definition runRocksalt (p:prefix) (i:instr) (s:SharedState) : option SharedState.
  refine (let r := RTL_step_list (instr_to_rtl p i) (shared_rtl_state s) in _).
  refine (match r with 
  | (Okay_ans tt, s') => Some (rtl_state_shared s')
  | _ => None
  end).
Defined.

Section InstrEq.

Variable eq:SharedState -> SharedState -> bool.
Variable run0 run1 : SharedState -> option SharedState.

Definition instrEq (s:SharedState) : option (SharedState * option SharedState * option SharedState).
  refine (let s0 := run0 s in _).
  refine (let s1 := run1 s in _).
  refine (let error := Some (s, s0, s1) in _).
  refine (match s0 with None =>  error | Some s0' => _ end).
  refine (match s1 with None =>  error | Some s1' => _ end).
  refine (if eq s0' s1' then None else error).
Defined.

Definition testSharedState : SharedState := {| 
  eax := repr 129786124931; ecx := repr 456123421348; 
  edx := repr 982483124977; ebx := repr 123497821934; 
  esp := repr 321497821397; ebp := repr 194378923143;
  esi := repr 102394758154; edi := repr 195263126789;
  cf := repr 1; pf := repr 0; af := repr 1;
  zf := repr 0; sf := repr 1; of := repr 0
|}.

Definition testInstrEq : option (SharedState * option SharedState * option SharedState).
  exact (instrEq testSharedState).
Defined.

Definition spaceInstrEq : Space (SharedState * option SharedState * option SharedState).
  refine (bind symbolicSharedState (fun s => _)).
  refine (match instrEq s with Some r => single r | None => empty end).
Defined.

Definition listToOption {A} (l:list A) : option A :=
  match l with [] => None | a::_ => Some a end.

Definition verifyInstrEq : option (SharedState * option SharedState * option SharedState).
  refine (listToOption (search spaceInstrEq)).
Defined.

End InstrEq.

Extraction "x86sem" instrEq testInstrEq spaceInstrEq verifyInstrEq 
  runRocksalt no_prefix 
  shared_state_eq eax ecx edx ebx esp ebp esi edi cf pf af zf sf of.
