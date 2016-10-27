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

Extract Constant cast_unsigned => "word-castu".
Extract Constant cast_signed => "word-casts".

Existing Instance rosetteBasic.
Existing Instance rosetteSearch.

Extraction Language Scheme.

(*
Finally, an instruction can have one instruction prefixes from each of the four groups: (1) lock and repeat prefixes, (2) segment override prefixes, (3) operand-size override prefix, and (4) address-size override prefix. In 64-bit mode, REX prefixes are used for specifying GPRs and SSE registers, 64-bit operand size, and extended control registers. Each instruction can have only one REX prefix at a time.

Imm_op = Immediate operand = constant

The boolean passed to instructions toggels betweeen 8bit (false) and 32bit (true)

http://penberg.blogspot.com/2010/04/short-introduction-to-x86-instruction.
*)
Definition no_prefix : prefix := mkPrefix None None false false.

Definition testSharedState : SharedState := {| 
  eax := repr 129786124931; ecx := repr 456123421348; 
  edx := repr 982483124977; ebx := repr 123497821934; 
  esp := repr 321497821397; ebp := repr 194378923143;
  esi := repr 102394758154; edi := repr 195263126789;
  cf := repr 1; pf := repr 0; zf := repr 0; 
  sf := repr 1; of := repr 0
|}.

Set Printing Width 78.
Check empty_oracle.


(* Debug an instruction in here: *)
Goal False.
  refine (let p := no_prefix in _).
  refine (let i : instr := LEAVE in _).
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
  refine (let s := testSharedState in _).
  refine (let s' := RTL_step_list (instr_to_rtl p i) (shared_rtl_state empty_oracle s) in _).
  refine (let gpr := gp_regs (core (rtl_mach_state (snd s'))) in _).
  refine (let fgs := flags_reg (core (rtl_mach_state (snd s'))) in _).
  Compute (gpr EAX).
  Compute (fgs ZF).
Abort.

Definition instrToRTL (pi:prefix * instr) : list rtl_instr :=
  instr_to_rtl (fst pi) (snd pi).

Definition runRocksalt (pi:prefix * instr) (o:oracle) (s:SharedState) : option SharedState.
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

Section InstrEq.

Variable eq:SharedState -> SharedState -> bool.
Variable uninterpretedBitsSpec : nat.
Variable runSpec : Word.int uninterpretedBitsSpec -> SharedState -> option SharedState.
Variable runRocksalt' : oracle -> SharedState -> option SharedState.

Definition instrEq (u:Word.int uninterpretedBitsSpec) (o:oracle) (s:SharedState) : option (SharedState * option SharedState * option SharedState).
  refine (let s0 := runSpec u s in _).
  refine (let s1 := runRocksalt' o s in _).
  refine (let error := Some (s, s0, s1) in _).
  refine (match s0 with None =>  error | Some s0' => _ end).
  refine (match s1 with None =>  error | Some s1' => _ end).
  refine (if eq s0' s1' then None else error).
Defined.

Definition testInstrEq : option (SharedState * option SharedState * option SharedState).
  exact (instrEq Word.zero empty_oracle testSharedState).
Defined.

Definition someOracle (o1:Word.int 5) : oracle. 
  refine {|
    oracle_bits s z := match s with 
                       | O => cast_unsigned (Word.shr o1 (repr z))
                       | _ => Word.zero 
                       end;
    oracle_offset := 0
  |}.
Defined.

Definition spaceInstrEq : Space (SharedState * option SharedState * option SharedState).
  refine (bind full (fun u : Word.int uninterpretedBitsSpec => _)).
  refine (bind symbolicSharedState (fun s => _)).
  refine (if existsWord (fun o1 => _)
          then empty
          else _).
  - refine (match instrEq u (someOracle o1) s with 
    | Some r => false (* non-equal *)
    | None =>   true  (* equal *)
    end).
  - refine (match instrEq u (someOracle Word.zero) s with 
    | Some r => single r
    | None => empty (* this should never happen *)
    end).
(*
  refine (match Precise.search _ with 
          | uninhabited => 
          | solution _ => empty
          end).
  (* refine (bind full (fun o1 : Word.int 16 => _)). *)
  refine (let o1 : Word.int 0 := Word.zero in _ ).
  refine (match instrEq u (someOracle o1) s with 
    | Some r => (* uninhabited *) empty     (* non-equal *)
    | None => (* solution tt *) single tt   (* equal *)
    end). *)
Defined.

Definition verifyInstrEq : option (SharedState * option SharedState * option SharedState).
  refine (match Precise.search spaceInstrEq with 
          | uninhabited => None 
          | solution a => Some a 
          end).
Defined.

End InstrEq.

Extraction "x86sem" instrEq testInstrEq spaceInstrEq verifyInstrEq 
  runRocksalt instrToRTL
  shared_state_eq eax ecx edx ebx esp ebp esi edi cf pf zf sf of.
