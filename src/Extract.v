Require Import X86Semantics.
Import X86_RTL.
Import X86_Compile.

Check instr_to_rtl.

Check interp_rtl.

Print RTL.

Check step.  (* appears to be execution *)

Print  RTL.


Check steps.

Print rtl_state.

Check instr_to_rtl.

(* seee simulator/test.ml *)

Require Import Bits.

Check Word.zero.

Check Word.int.

Definition bii := id (A:=nat).

Require Import Maps.

Import PTree.

Definition empty_mem := (@Word.zero (bii 7), PTree.empty).
Definition empty_reg := (fun reg => @Word.zero (bii 31)).
Definition empty_seg := (fun seg => @Word.zero (bii 31)).
Definition empty_regpcseg = (empty_reg, Word.zero (bii 31), empty_seg);;

let empty_oracle =
  { oracle_bits = (fun a b -> zero_big_int); oracle_offset = zero_big_int }

let (loaded_mem, _) = load_memory empty_mem [] mem_file;;
let (loaded_reg, pc, loaded_seg) = load_regpc empty_regpcseg reg_file;;

let init_machine =     
  { gp_regs = loaded_reg;
    seg_regs_starts =  loaded_seg;
    seg_regs_limits = (fun seg_reg->(Word.repr (bii 31) (Word.max_unsigned
                                                           (bii 31))));
    flags_reg = (fun f -> Word.zero (bii 0));
    control_regs = (fun c -> Word.zero (bii 31));
    debug_regs =  (fun d -> Word.zero (bii 31));
    pc_reg = pc;
  };;


(*let init_fpu_machine = 
{
  This is not the syntax, just taken from x86semantics
  { fpu_data_regs : (int3, int80) fmap; fpu_status : 
                     int16; fpu_control : int16;
                     fpu_tags : (int3, int2) fmap; fpu_lastInstrPtr : 
                     int48; fpu_lastDataPtr : int48; fpu_lastOpcode : 
                     RTL.int }
};;
*)

let empty_fpu_machine =
{
  fpu_data_regs = (fun fpr -> (Word.repr(bii 2) (Word.zero(bii 79))));
  fpu_status = Word.zero(bii 15);
  fpu_control = Word.zero(bii 15);
  fpu_tags = (fun t -> (Word.repr(bii 2) (Word.zero(bii 1))));
  fpu_lastInstrPtr = Word.zero(bii 47);
  fpu_lastDataPtr = Word.zero(bii 47);
  fpu_lastOpcode = Word.zero(bii 2);
};;

let init_full_machine = 
{  core = init_machine;
   fpu = empty_fpu_machine;
}

let init_rtl_state =
  { rtl_oracle = empty_oracle;
    rtl_mach_state = init_full_machine; 
    rtl_memory = loaded_mem 
  };; 

