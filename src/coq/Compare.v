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
Require Import ExtractWord.
Require Import InitState.
Require Import SharedState.

Extract Constant cast_unsigned => "word-unsigned-cast".
Extract Constant cast_signed => "(lambdas (srcBits dstBits x) (error 'signed-cast))".

Existing Instance freeProd.

Arguments free {_ _ _}.
Arguments mone {_}.

Existing Instance rosette.

Extraction Language Scheme.

(*
Finally, an instruction can have one instruction prefixes from each of the four groups: (1) lock and repeat prefixes, (2) segment override prefixes, (3) operand-size override prefix, and (4) address-size override prefix. In 64-bit mode, REX prefixes are used for specifying GPRs and SSE registers, 64-bit operand size, and extended control registers. Each instruction can have only one REX prefix at a time.

Imm_op = Immediate operand = constant

The boolean passed to instructions toggels betweeen 8bit (false) and 32bit (true)

http://penberg.blogspot.com/2010/04/short-introduction-to-x86-instruction.
*)
Definition no_prefix : prefix := mkPrefix None None false false.

(*
Parameter Instruction : Type.
Extract Constant Instruction => "__".
Parameter toRocksaltInstruction : Instruction -> (prefix * instr).
Extract Constant toRocksaltInstruction => "rocksalt-instruction".
Parameter runStoke : Instruction -> SharedState -> SharedState.
Extract Constant runStoke => "run-stoke".
*)

Definition runRocksalt (p:prefix) (i:instr) (s:SharedState) : option SharedState.
  refine (let r := RTL_step_list (instr_to_rtl p i) (shared_rtl_state s) in _).
  refine (match r with 
  | (Okay_ans tt, s') => Some (rtl_state_shared s')
  | _ => None
  end).
Defined.

Definition instrEq (run0 run1 : SharedState -> option SharedState) (s:SharedState) : option (SharedState * option SharedState * option SharedState).
  refine (let s0 := run0 s in _).
  refine (let s1 := run1 s in _).
  refine (let error := Some (s, s0, s1) in _).
  refine (match s0 with None =>  error | Some s0' => _ end).
  refine (match s1 with None =>  error | Some s1' => _ end).
  refine (if shared_state_eq s0' s1' then None else error).
Defined.

Definition instrEqSpace (run0 run1 : SharedState -> option SharedState) : Space (SharedState * option SharedState * option SharedState).
  refine (bind symbolicSharedState (fun s => _)).
  refine (match instrEq run0 run1 s with Some r => single r | None => empty end).
Defined.

Definition verifyInstrEq (run0 run1 : SharedState -> option SharedState) : option (SharedState * option SharedState * option SharedState).
  refine (search (instrEqSpace run0 run1)).
Defined.

Definition andEaxEbx : instr := AND true (Reg_op EAX) (Reg_op EBX).
Definition notEax : instr := NOT true (Reg_op EAX).

Extraction "x86sem" instrEq instrEqSpace verifyInstrEq andEaxEbx runRocksalt notEax no_prefix.