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
Require Import Full.
Require Import Rosette.
Require Import ExtractWord.
Require Import InitState.

(*
Shared state between Rocksalt and Stoke.

### General Purpose Registers

Rocksalt (see `register` type) and Stoke have all GRPs:

    rax rcx rdx rbx rsp rbp rsi rdi

### Flags

Rocksalt (see `flag` type) has a superset of Stoke's flags. They share:

    cf pf af zf sf of

But only Rocksalt has:

    ID | VIP | VIF | AC | VM | RF | NT | IOPL | DF | IF_flag | TF 

### Other

Only Rocksalt has `segment_register`, `control_register`, 

Only Stoke has the 64bit registers:

    r8 r9 r10 r11 r12 r13 r14 r15

Only Stoke has the SIMD registers:

    ymm0 ymm1 ymm2 ymm3 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 
    ymm10 ymm11 ymm12 ymm13 ymm14 ymm15

*)

Record SharedState := sharedState { 
  eax : int32;
  ecx : int32; 
  edx : int32; 
  ebx : int32; 
  esp : int32;
  ebp : int32;
  esi : int32;
  edi : int32;

  cf : int1; 
  pf : int1; 
  af : int1;
  zf : int1;
  sf : int1;
  of : int1
}.

Definition symbolicSharedState : Space SharedState.
  refine (bind full (fun eax' => _)).
  refine (bind full (fun ecx' => _)).
  refine (bind full (fun edx' => _)).
  refine (bind full (fun ebx' => _)).
  refine (bind full (fun esp' => _)).
  refine (bind full (fun ebp' => _)).
  refine (bind full (fun esi' => _)).
  refine (bind full (fun edi' => _)).
  refine (bind full (fun cf' => _)).
  refine (bind full (fun pf' => _)).
  refine (bind full (fun af' => _)).
  refine (bind full (fun zf' => _)).
  refine (bind full (fun sf' => _)).
  refine (bind full (fun of' => _)). 
  refine (single {| 
    eax := eax';
    ecx := ecx'; 
    edx := edx'; 
    ebx := ebx'; 
    esp := esp';
    ebp := ebp';
    esi := esi';
    edi := edi';
    cf := cf'; 
    pf := pf'; 
    af := af';
    zf := zf';
    sf := sf';
    of := of'
  |}).
Defined.

Section SharedState.
  Variable (s:SharedState).

  Definition shared_reg : fmap register int32 :=
    fun r => match r with
    | EAX => eax s
    | ECX => ecx s
    | EDX => edx s
    | EBX => ebx s
    | ESP => esp s
    | EBP => ebp s
    | ESI => esi s
    | EDI => edi s
    end.

  Definition shared_flags : fmap flag int1 :=
    fun f => match f with
    | OF => of s
    | SF => sf s
    | ZF => zf s
    | AF => af s
    | PF => pf s
    | CF => cf s
    | _ => Word.zero
    end.

  Definition shared_machine : core_state. 
    refine {|
      gp_regs := shared_reg;
      seg_regs_starts := empty_seg;
      seg_regs_limits := (fun seg_reg=>Word.mone);
      flags_reg := shared_flags;
      control_regs := (fun c => Word.zero);
      debug_regs :=  (fun d => Word.zero);
      pc_reg := init_pc
    |}.
  Defined.

  Definition shared_full_machine : mach_state.
    refine {|
     core := shared_machine;
     fpu := empty_fpu_machine
    |}.
  Defined.
 
  Definition shared_rtl_state : rtl_state.
    refine {|
      rtl_oracle := empty_oracle;
      rtl_mach_state := shared_full_machine;
      rtl_memory := empty_mem
    |}.
  Defined.
End SharedState.

Definition rtl_state_shared (s:rtl_state) : SharedState.
  refine (let gpr := gp_regs (core (rtl_mach_state s)) in _).
  refine (let fgs := flags_reg (core (rtl_mach_state s)) in _).
  refine (
  {| 
    eax := gpr EAX;
    ecx := gpr ECX; 
    edx := gpr EDX; 
    ebx := gpr EBX; 
    esp := gpr ESP;
    ebp := gpr EBP;
    esi := gpr ESI;
    edi := gpr EDI;
    cf := fgs CF; 
    pf := fgs PF; 
    af := fgs AF;
    zf := fgs ZF;
    sf := fgs SF;
    of := fgs OF
  |}).
Defined.

Definition shared_state_eq (l:list {n : nat & SharedState -> int n}) (s0 s1:SharedState) : bool.
  refine (forallb (fun nf => Word.eq _ _) l).
  refine ((projT2 nf) s0).
  refine ((projT2 nf) s1).
Defined.
