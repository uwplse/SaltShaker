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

Arguments mone {_}.
Arguments free {_ _ _}.

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
  refine (bind free (fun eax' => _)).
  refine (bind free (fun ecx' => _)).
  refine (bind free (fun edx' => _)).
  refine (bind free (fun ebx' => _)).
  refine (bind free (fun esp' => _)).
  refine (bind free (fun ebp' => _)).
  refine (bind free (fun esi' => _)).
  refine (bind free (fun edi' => _)).
  refine (bind free (fun cf' => _)).
  refine (bind free (fun pf' => _)).
  refine (bind free (fun af' => _)).
  refine (bind free (fun zf' => _)).
  refine (bind free (fun sf' => _)).
  refine (bind free (fun of' => _)). 
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

Definition shared_state_eq (s0 s1:SharedState) : bool.
  refine (Word.eq (eax s0) (eax s1) && _).
  refine (Word.eq (ecx s0) (ecx s1) && _).
  refine (Word.eq (edx s0) (edx s1) && _).
  refine (Word.eq (ebx s0) (ebx s1) && _).
  refine (Word.eq (esp s0) (esp s1) && _).
  refine (Word.eq (ebp s0) (ebp s1) && _).
  refine (Word.eq (esi s0) (esi s1) && _).
  refine (Word.eq (edi s0) (edi s1) && _).
  refine (Word.eq (cf s0) (cf s1) && _).
  refine (Word.eq (pf s0) (pf s1) && _).
  refine (Word.eq (af s0) (af s1) && _).
  refine (Word.eq (zf s0) (zf s1) && _).
  refine (Word.eq (sf s0) (sf s1) && _).
  refine (Word.eq (of s0) (of s1) && _).
  exact true.
Defined.
