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

Print prefix.

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

Definition maxInt {bits} : int bits.
  refine (# (Word.max_unsigned bits)).
  apply maxIntIsInt.
Defined.

Compute (@maxInt 31).

(* initialize state, inspired by see simulator/test.ml *)

Parameter freeIntSpace : forall n, Space (int n).
Axiom freeIntSpaceOk : forall n (a : int n), contains a (freeIntSpace n). 
Extract Constant freeIntSpace => "word-free".

Instance freeInt n : @Free rosette (int n) := {| 
  free := freeIntSpace n; 
  freeOk := freeIntSpaceOk n 
|}.

Arguments free {_ _ _}.

Existing Instance freeProd.

Definition bii := id (A:=nat).

Definition empty_mem : AddrMap.t int8 := (@Word.zero (bii 7), PTree.empty _).
Definition empty_reg : fmap register int32 := (fun reg => @Word.zero (bii 31)).
Definition empty_seg : fmap segment_register int32 := (fun seg => @Word.zero (bii 31)).
Definition pc := @Word.zero (bii 31).

Definition symbolic_reg : Space (fmap register int32) :=
  bind free (fun x => single (fun _ => x)).

Definition empty_flags : fmap flag int1 := fun f => @Word.zero (bii 0).

Definition symbolic_flags : Space (fmap flag int1) :=
  bind free (fun x => single (fun _ => x)).

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
    seg_regs_limits := (fun seg_reg=>@maxInt (bii 31));
    flags_reg := empty_flags;
    control_regs := (fun c => @Word.zero (bii 31));
    debug_regs :=  (fun d => @Word.zero (bii 31));
    pc_reg := pc
  |}.
Defined.

Definition symbolic_machine : Space core_state. 
  refine (bind symbolic_reg (fun gprs => _)).
  refine (bind symbolic_flags (fun flags => _)).
  refine (single {|
    gp_regs := gprs;
    seg_regs_starts := empty_seg;
    seg_regs_limits := (fun seg_reg=>@maxInt (bii 31));
    flags_reg := flags;
    control_regs := (fun c => @Word.zero (bii 31));
    debug_regs :=  (fun d => @Word.zero (bii 31));
    pc_reg := pc
  |}).
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

Definition symbolic_full_machine : Space mach_state.
  refine (bind symbolic_machine (fun m => _)).
  refine (single {|
   core := m;
   fpu := empty_fpu_machine
  |}).
Defined.

Definition init_rtl_state : rtl_state.
  refine {|
    rtl_oracle := empty_oracle;
    rtl_mach_state := init_full_machine;
    rtl_memory := empty_mem
  |}.
Defined.

Definition symbolic_rtl_state : Space rtl_state.
  refine (bind symbolic_full_machine (fun m => _)).
  refine (single {|
    rtl_oracle := empty_oracle;
    rtl_mach_state := m;
    rtl_memory := empty_mem
  |}).
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

Record SharedState := { 
  rax : int64;
  rcx : int64; 
  rdx : int64; 
  rbx : int64; 
  rsp : int64;
  rbp : int64;
  rsi : int64;
  rdi : int64;

  cf : int1; 
  pf : int1; 
  af : int1;
  zf : int1;
  sf : int1;
  of : int1
}.

Definition symbolicSharedState : Space SharedState.
  refine (bind free (fun rax' => _)).
  refine (bind free (fun rcx' => _)).
  refine (bind free (fun rdx' => _)).
  refine (bind free (fun rbx' => _)).
  refine (bind free (fun rsp' => _)).
  refine (bind free (fun rbp' => _)).
  refine (bind free (fun rsi' => _)).
  refine (bind free (fun rdi' => _)).
  refine (bind free (fun cf' => _)).
  refine (bind free (fun pf' => _)).
  refine (bind free (fun af' => _)).
  refine (bind free (fun zf' => _)).
  refine (bind free (fun sf' => _)).
  refine (bind free (fun of' => _)). 
  refine (single {| 
    rax := rax';
    rcx := rcx'; 
    rdx := rdx'; 
    rbx := rbx'; 
    rsp := rsp';
    rbp := rbp';
    rsi := rsi';
    rdi := rdi';
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
    | EAX => cast_unsigned (rax s)
    | ECX => cast_unsigned (rcx s)
    | EDX => cast_unsigned (rdx s)
    | EBX => cast_unsigned (rbx s)
    | ESP => cast_unsigned (rsp s)
    | EBP => cast_unsigned (rbp s)
    | ESI => cast_unsigned (rsi s)
    | EDI => cast_unsigned (rdi s)
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
      seg_regs_limits := (fun seg_reg=>@maxInt (bii 31));
      flags_reg := shared_flags;
      control_regs := (fun c => @Word.zero (bii 31));
      debug_regs :=  (fun d => @Word.zero (bii 31));
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

Definition rtl_eax_cast8_add (n:int32) := [set_loc_rtl 
  (cast_u_rtl_exp 31
    (arith_rtl_exp add_op
      (cast_u_rtl_exp 7 (get_loc_rtl_exp (reg_loc EAX)))
      (cast_u_rtl_exp 7 (imm_rtl_exp n)))) 
  (reg_loc EAX)].

Definition cast8_add n m := rtl_eax_cast8_add n ++ rtl_eax_cast8_add m.

Definition run p := RTL_step_list p init_rtl_state.

Definition get_eax (i:list rtl_instr) :=
  let s := run i in
    (fst s, gp_regs (core (rtl_mach_state (snd s))) EAX).

Compute get_eax (cast8_add (repr 4) (repr 6)).

(* 510 % 256 = 254, 254 + 4 = 258, 258 % 256 = 2 *)
Compute get_eax (cast8_add (repr 510) (repr 4)).

(* Existing Instance listSpaceSearch. *)
Existing Instance rosette.

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

Open Scope positive.

Compute @positiveSpace' listSpaceSearch 0.
Compute @positiveSpace' listSpaceSearch 1.
Compute @positiveSpace' listSpaceSearch 2.
Compute @positiveSpace' listSpaceSearch 3.
Compute @positiveSpace' listSpaceSearch 4.

(* this is fast for reasonable p :) *)
Definition constructPositiveSpace (p:nat) : Space positive :=
  positiveSpace p.

(* this takes ages for reasonable p :( *)
Definition trivialPositiveVerification (p:nat) : option positive.
  refine (search _).
  refine (bind (positiveSpace p) (fun n => _)).
  refine (if eqb n n then empty else single n).
Defined.

Extraction Language Scheme.

Extract Constant mkint => "word-mkint".
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

Definition instr_add n m := 
  set_loc_rtl (imm_rtl_exp n) (reg_loc EAX) ::
  instr_to_rtl no_prefix (ADD true (Reg_op EAX) (Imm_op m)).

Definition instr_not_8bit n := 
  set_loc_rtl (imm_rtl_exp n) (reg_loc EAX) ::
  instr_to_rtl no_prefix (NOT false (Reg_op EAX)).

Definition instr_not n := 
  set_loc_rtl (imm_rtl_exp n) (reg_loc EAX) ::
  instr_to_rtl no_prefix (NOT true (Reg_op EAX)).

Definition instr_and n m := 
  set_loc_rtl (imm_rtl_exp n) (reg_loc EAX) ::
  instr_to_rtl no_prefix (AND true (Reg_op EAX) (Imm_op m)).

Goal unit.
  (* Print instr. *)
  refine ((fun n : int32 => _) zero).
  refine (let i := instr_to_rtl no_prefix (AND true (Reg_op EAX) (Imm_op n)) in _);
(*
  refine (let i := instr_to_rtl no_prefix (OR true (Reg_op EAX) (Imm_op n)) in _);
  refine (let i := instr_to_rtl no_prefix (ADD true (Reg_op EAX) (Imm_op n)) in _). 
  refine (let i := instr_to_rtl no_prefix (NOT true (Reg_op EAX)) in _). *)

  unfold instr_to_rtl in *; simpl in *; unfold runConv in *; 
  simpl in *.
Abort.

Compute (get_eax (instr_not_8bit (repr 126))).

(*
  Fixpoint interp_rtl_exp s (e:rtl_exp s) (rs:rtl_state) : int s :=
    match e with 
      | arith_rtl_exp _ b e1 e2 =>
        let v1 := interp_rtl_exp e1 rs in 
        let v2 := interp_rtl_exp e2 rs in interp_arith b v1 v2
      | test_rtl_exp _ t e1 e2 => 
        let v1 := interp_rtl_exp e1 rs in
        let v2 := interp_rtl_exp e2 rs in interp_test t v1 v2
      | if_rtl_exp _ cd e1 e2 =>
        let v := interp_rtl_exp cd rs in
        if (Word.eq v Word.one) then interp_rtl_exp e1 rs
        else interp_rtl_exp e2 rs
      | cast_s_rtl_exp _ _ e =>
        let v := interp_rtl_exp e rs in cast_signed v
      | cast_u_rtl_exp _ _ e => 
        let v := interp_rtl_exp e rs in cast_unsigned v
      | imm_rtl_exp _ v => v
      | get_loc_rtl_exp _ l => get_location l (rtl_mach_state rs)
      | get_array_rtl_exp _ _ a e => 
        let i := interp_rtl_exp e rs in array_sub a i (rtl_mach_state rs)
      | get_byte_rtl_exp addr => 
        let v := interp_rtl_exp addr rs in AddrMap.get v (rtl_memory rs)
      | farith_rtl_exp _ _ hyp fop rm e1 e2 =>
        let v1 := interp_rtl_exp e1 rs in let v2 := interp_rtl_exp e2 rs in
        let vrm := interp_rtl_exp rm rs in
        interp_farith hyp fop vrm v1 v2
      | fcast_rtl_exp _ _ _ _ hyp1 hyp2 rm e =>
        let v := interp_rtl_exp e rs in
        let vrm := interp_rtl_exp rm rs in
        interp_fcast hyp1 hyp2 vrm v
      | get_random_rtl_exp _ => 
        let oracle := rtl_oracle rs in
        oracle_bits oracle _ (oracle_offset oracle)
    end.

  Definition interp_arith s (b:bit_vector_op)(v1 v2:int s) : int s := 
    match b with 
      | add_op => Word.add v1 v2
      | sub_op => Word.sub v1 v2
      | mul_op => Word.mul v1 v2
      | divs_op => Word.divs v1 v2
      | divu_op => Word.divu v1 v2
      | modu_op => Word.modu v1 v2
      | mods_op => Word.mods v1 v2
      | and_op => Word.and v1 v2
      | or_op => Word.or v1 v2
      | xor_op => Word.xor v1 v2
      | shl_op => Word.shl v1 v2
      | shr_op => Word.shr v1 v2
      | shru_op => Word.shru v1 v2
      | ror_op => Word.ror v1 v2
      | rol_op => Word.rol v1 v2
    end.

  Definition interp_test s (t:test_op)(v1 v2:int s) : int size1 := 
    if (match t with 
      | eq_op => Word.eq v1 v2 
      | lt_op => Word.lt v1 v2
      | ltu_op => Word.ltu v1 v2
        end) then Word.one else Word.zero.

*)

Definition findWordProposition (bits:nat) (x:int bits) : option (int bits).
  refine (if Word.eq x maxInt then Some x else None).
Defined.

Definition verifyForall {A} {B} `{Free A} (p:A -> option B) : option B.
  refine (search _).
  refine (bind free (fun a : A => _)).
  refine (match p a with Some b => single b | None => empty end).
Defined.

Definition findWord (bits:nat) : option (int bits) :=
  verifyForall (findWordProposition bits).

Definition wordVerification (bits:nat) : option (int bits * int bits).
  refine (search _).
  refine (bind free (fun x : int bits => _)).
  refine (bind free (fun y : int bits => _)).
  refine (if Word.eq (Word.add x y) (Word.add y x) 
          then empty
          else single (x, y)).
Defined.

Definition initRTLState (_:unit) := init_rtl_state.

Definition cast8AddVerificationProposition (nm:int32 * int32) : option (int32 * int32 * int32 * int32).
  refine (let n := fst nm in _).
  refine (let m := snd nm in _).
  refine (let expected := Word.add n m in _).
  refine (match get_eax (cast8_add n m) with
  | (Okay_ans tt, result) => _
  | (_, result) => Some (nm,result,expected)
  end).
  refine (if Word.eq result expected then None else Some (nm,result,expected)).
Defined.

Definition cast8AddVerification (_:unit) := verifyForall cast8AddVerificationProposition.

Definition notVerificationProposition (n:int32) : option (int32 * int32 * int32).
  refine (let expected := Word.not n in _).
  refine (match get_eax (instr_not n) with
  | (Okay_ans tt, result) => _
  | (_, result) => Some (n,result,expected)
  end).
  refine (if Word.eq result expected then None else Some (n,result,expected)).
Defined.

Definition notVerification (_:unit) := verifyForall notVerificationProposition.

Definition andVerificationProposition (nm:int32 * int32) : option (int32 * int32 * int32).
  refine (let n := fst nm in _).
  refine (let m := snd nm in _).
  refine (let expected := Word.not (Word.or (Word.not n) (Word.not m)) in _).
  refine (match get_eax (instr_and n m) with
  | (Okay_ans tt, result) => _
  | (_, result) => Some (n,result,expected)
  end).
  refine (if Word.eq result expected then None else Some (n,result,expected)).
Defined.

Definition andSpace : Space (int32 * int32 * int32).
  refine (bind free (fun nm : int32 * int32 => _)).
  refine (match andVerificationProposition nm with Some r => single r | None => empty end).
Defined.

Definition andVerification (_:unit) := verifyForall andVerificationProposition.

Parameter runStoke : prefix -> instr -> SharedState -> SharedState.

Extract Constant runStoke => "run-stoke".

Definition rtl_state_shared (s:rtl_state) : SharedState.
  refine (let gpr := gp_regs (core (rtl_mach_state s)) in _).
  refine (let fgs := flags_reg (core (rtl_mach_state s)) in _).
  refine (
  {| 
    rax := cast_unsigned (gpr EAX);
    rcx := cast_unsigned (gpr ECX); 
    rdx := cast_unsigned (gpr EDX); 
    rbx := cast_unsigned (gpr EBX); 
    rsp := cast_unsigned (gpr ESP);
    rbp := cast_unsigned (gpr EBP);
    rsi := cast_unsigned (gpr ESI);
    rdi := cast_unsigned (gpr EDI);
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

Require Import Bool.

Definition shared_state_eq (s0 s1:SharedState) : bool.
  refine (Word.eq (rax s0) (rax s1) && _).
  refine (Word.eq (rcx s0) (rcx s1) && _).
  refine (Word.eq (rdx s0) (rdx s1) && _).
  refine (Word.eq (rbx s0) (rbx s1) && _).
  refine (Word.eq (rsp s0) (rsp s1) && _).
  refine (Word.eq (rbp s0) (rbp s1) && _).
  refine (Word.eq (rsi s0) (rsi s1) && _).
  refine (Word.eq (rdi s0) (rdi s1) && _).
  refine (Word.eq (cf s0) (cf s1) && _).
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

Extraction "x86sem" constructPositiveSpace wordVerification cast8AddVerification trivialPositiveVerification findWord findWordProposition cast8AddVerificationProposition initRTLState notVerificationProposition notVerification andVerificationProposition andVerification andSpace symbolicSharedState instrEq instrEqSpace verifyInstrEq andEaxEbx notEax no_prefix.

