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

Require Import Rosette.
Require Import SpaceSearch.

Notation "# n" := (mkint _ n _) (at level 45).

Parameter freeIntSpace : forall n, Space (int n).
Axiom freeIntSpaceOk : forall n (a : int n), contains a (freeIntSpace n). 
Extract Constant freeIntSpace => "word-free".

Instance freeInt n : @Free rosette (int n) := {| 
  free := freeIntSpace n; 
  freeOk := freeIntSpaceOk n 
|}.

Arguments free {_ _ _}.

Existing Instance freeProd.

Arguments Word.mone {_}.

(* 
initialize state, inspired by see 
x86model/semantics_trace/simulator/test.ml
*)

Definition empty_mem : AddrMap.t int8 := (Word.zero, PTree.empty _).
Definition empty_reg : fmap register int32 := (fun reg => Word.zero).
Definition empty_seg : fmap segment_register int32 := (fun seg => Word.zero).
Definition pc : int32 := Word.zero.

Definition empty_flags : fmap flag int1 := fun f => Word.zero.

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
    seg_regs_limits := (fun seg_reg=>Word.mone);
    flags_reg := empty_flags;
    control_regs := (fun c => Word.zero);
    debug_regs :=  (fun d => Word.zero);
    pc_reg := pc
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
    rtl_mach_state := init_full_machine;
    rtl_memory := empty_mem
  |}.
Defined.

(*

### General Purpose Registers

Rocksalt (see `register` type) and Stocke have all GRPs:

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
      pc_reg := pc
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

(* Existing Instance listSpaceSearch. *)
Existing Instance rosette.

Extraction Language Scheme.

Extract Constant Word.repr => "word-mkint".
Extract Constant Word.zero => "word-zero".
Extract Constant Word.one => "word-one".
Extract Constant Word.mone => "word-mone".
Extract Constant Word.eq => "word-eq".
Extract Constant Word.lt => "word-lt".
Extract Constant Word.ltu => "word-ltu".

Extract Constant cast_unsigned => "word-unsigned-cast".
Extract Constant cast_signed => "(lambdas (srcBits dstBits x) (error 'signed-cast))".
Extract Constant Word.unsigned => "(lambdas (_) (error 'unsigned))".
Extract Constant Word.signed => "(lambdas (_) (error 'signed))".

Extract Constant Word.add => "word-add".
Extract Constant Word.sub => "(lambdas (_) (error 'sub))".
Extract Constant Word.mul => "(lambdas (_) (error 'mul))".
Extract Constant Word.divs => "(lambdas (_) (error 'divs))".
Extract Constant Word.divu => "(lambdas (_) (error 'divu))".
Extract Constant Word.modu => "(lambdas (_) (error 'modu))".
Extract Constant Word.mods => "(lambdas (_) (error 'mods))".
Extract Constant Word.and => "word-and".
Extract Constant Word.or => "word-or".
Extract Constant Word.xor => "word-xor".
Extract Constant Word.shl => "word-shl".
Extract Constant Word.shr => "word-shr".
Extract Constant Word.shru => "word-shru".
Extract Constant Word.ror => "(lambdas (_) (error 'ror))".
Extract Constant Word.rol => "(lambdas (_) (error 'rol))".

(* Define an instruction *)

(*
Finally, an instruction can have one instruction prefixes from each of the four groups: (1) lock and repeat prefixes, (2) segment override prefixes, (3) operand-size override prefix, and (4) address-size override prefix. In 64-bit mode, REX prefixes are used for specifying GPRs and SSE registers, 64-bit operand size, and extended control registers. Each instruction can have only one REX prefix at a time.

Imm_op = Immediate operand = constant

The boolean passed to instructions toggels betweeen 8bit (false) and 32bit (true)

http://penberg.blogspot.com/2010/04/short-introduction-to-x86-instruction.
*)
Definition no_prefix : prefix := mkPrefix None None false false.

Parameter runStoke : prefix -> instr -> SharedState -> SharedState.

Extract Constant runStoke => "run-stoke".

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

Definition runRocksalt (p:prefix) (i:instr) (s:SharedState) : option SharedState.
  refine (let r := RTL_step_list (instr_to_rtl p i) (shared_rtl_state s) in _).
  refine (match r with 
  | (Okay_ans tt, s') => Some (rtl_state_shared s')
  | _ => None
  end).
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
  refine (Word.eq (of s0) (of s1)).
Defined.

Definition instrEq (p:prefix) (i:instr) (s:SharedState) : option (SharedState * SharedState * option SharedState).
  refine (let rs := runRocksalt p i s in _).
  refine (let ss := runStoke p i s in _).
  refine (let error := Some (s, ss, rs) in _).
  refine (match rs with 
  | None =>  error
  | Some rs' => _ 
  end).
  refine (if shared_state_eq rs' ss 
          then None
          else error).
Defined.  

Definition instrEqSpace (p:prefix) (i:instr) : Space (SharedState * SharedState * option SharedState).
  refine (bind symbolicSharedState (fun s => _)).
  refine (match instrEq p i s with Some r => single r | None => empty end).
Defined.

Definition verifyInstrEq (p:prefix) (i:instr) : option (SharedState * SharedState * option SharedState).
  refine (search (instrEqSpace p i)).
Defined.

Definition andEaxEbx : instr := AND true (Reg_op EAX) (Reg_op EBX).

Definition notEax : instr := NOT true (Reg_op EAX).

Extraction "x86sem" instrEq instrEqSpace verifyInstrEq andEaxEbx notEax no_prefix.

