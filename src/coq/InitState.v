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

Arguments mone {_}.

(* 
initialized state construction, inspired by:
x86model/semantics_trace/simulator/test.ml
*)

Definition empty_mem : AddrMap.t int8 := (Word.zero, PTree.empty _).
Definition empty_reg : fmap register int32 := (fun reg => Word.zero).
Definition empty_seg : fmap segment_register int32 := (fun seg => Word.zero).
Definition empty_flags : fmap flag int1 := fun f => Word.zero.
Definition init_pc : int32 := Word.zero.

Definition empty_oracle : oracle.
  refine {|
    oracle_bits := (fun a b => Word.zero);
    oracle_offset := 0
  |}.
Defined.

Definition init_machine : core_state. 
  refine {|
    gp_regs := empty_reg;
    seg_regs_starts := empty_seg;
    seg_regs_limits := (fun seg_reg => Word.mone);
    flags_reg := empty_flags;
    control_regs := (fun c => Word.zero);
    debug_regs :=  (fun d => Word.zero);
    pc_reg := init_pc
  |}.
Defined.

Definition empty_fpu_machine : fpu_state.
refine {|
  fpu_data_regs := (fun fpr => (* @Word.repr(bii 2) *) Word.zero);
  fpu_status := Word.zero;
  fpu_control := Word.zero;
  fpu_tags := (fun t => (* @Word.repr(bii 2) *) Word.zero);
  fpu_lastInstrPtr := Word.zero;
  fpu_lastDataPtr := Word.zero;
  fpu_lastOpcode := Word.zero (* originally: (bii 2) *)
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
    rtl_env := empty_env;
    rtl_mach_state := init_full_machine;
    rtl_memory := empty_mem
  |}.
Defined.

