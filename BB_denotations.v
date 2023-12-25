Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. 
Import SetsNotation.
Require Import Coq.Logic.Classical_Prop.
Require Import compcert.lib.Integers.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope sets.
Require Import Main.grammer.
Require Import Main.cmd_denotations.
Require Import Main.BB_generation.
Require Import Coq.Lists.List.
Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.

Record BB_state: Type := {
  BB_num: nat;
  st: state
}.

Module BDenote.
Record BDenote: Type := {
  Bnrm: BB_state -> BB_state -> Prop;
  Berr: BB_state -> Prop;
  Binf: BB_state -> Prop
}.
End BDenote.

Import BDenote.

Definition empty_sem : BDenote := {|
  Bnrm := ∅;
  Berr := ∅;
  Binf := ∅
|}.

Definition get_state (bs: BB_state): state := bs.(st).


(* Handle Jmp Sem ====================================================================================================================== *)


Definition test_true_jmp (D: EDenote):
  state -> Prop :=
    (fun s => exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false_jmp (D: EDenote):
  state -> Prop :=
    (fun s => D.(nrm) s (Int64.repr 0)).

Definition ujmp_sem (BBnum : nat) (jum_dest: nat): BDenote :=
  {|
    Bnrm := fun (bs1: BB_state) (bs2 :BB_state) =>
      bs1.(st) = bs2.(st) /\ bs1.(BB_num) = BBnum 
      /\ bs2.(BB_num) = jum_dest /\ (bs1.(BB_num) <> bs2.(BB_num));
    Berr := ∅;
    Binf := ∅;
  |}.

Definition cjmp_sem (BBnum : nat) (jump_dest_1: nat) (jmp_dest2: nat) (D: EDenote) : BDenote :=
  {|
    Bnrm := fun bs1 bs2 => ((bs1.(st) = bs2.(st)) /\
            (bs1.(BB_num) = BBnum) /\ 
            ((bs2.(BB_num) = jump_dest_1) /\ (test_true_jmp D bs1.(st)) \/ ((bs2.(BB_num) = jmp_dest2) 
            /\ (test_false_jmp D bs1.(st))))) /\ (bs1.(BB_num) <> bs2.(BB_num));
    Berr := ∅; (* Ignore err cases now *)
    Binf := ∅;
  |}.


Definition BJump_sem (BBnum : nat) (jump_dest_1: nat) (jmp_dest2: option nat)(D: option EDenote) :BDenote :=
  match D with 
  | None => ujmp_sem BBnum jump_dest_1 (* No expr *)
  | Some D => match jmp_dest2 with
              | None => ujmp_sem BBnum jump_dest_1
              | Some jmp_dest2 => cjmp_sem BBnum jump_dest_1 jmp_dest2 D
              end
  end.


(* =================================================================================================================================================================================    *)



Definition BAsgn_sem (x: var_name) (e:EDenote) : BDenote := {|
  Bnrm := fun (bs1:BB_state) (bs2:BB_state) => 
     exists i,
     (e.(nrm) bs1.(st) i) /\  (bs2.(st) x = Vint i) /\ (forall y, x <> y -> bs1.(st) y = bs2.(st) y);
  Berr := fun(bs1:BB_state) => bs1.(st) ∈ e.(err);
  Binf := ∅;
|}.

(** Now we are certain that BB only contains BAsgn and BJump cmds *)
(* The sementics for a list of BAsgn *)
Print BB_cmd.


Definition BAsgn_denote (BAsgn_cmd: BB_cmd) : BDenote :=   
  let x := BAsgn_cmd.(X) in 
  let e := BAsgn_cmd.(E) in
 {|
  Bnrm :=  fun (bs1: BB_state) (bs2: BB_state) => (BAsgn_sem x (eval_expr e)).(Bnrm) bs1 bs2 /\ (bs1.(BB_num) = bs2.(BB_num)); 
  Berr := (BAsgn_sem x (eval_expr e)).(Berr);
  Binf := ∅;
|}.



Fixpoint BAsgn_list_sem (BAsgn_list: list BB_cmd) : BDenote := 
match BAsgn_list with 
 | BAsgn_cmd :: tl =>
   {|   
      Bnrm := (BAsgn_denote BAsgn_cmd).(Bnrm) ∘ (BAsgn_list_sem tl).(Bnrm);
      Berr := (BAsgn_denote BAsgn_cmd).(Berr) ∪ (BAsgn_denote BAsgn_cmd).(Bnrm) ∘ (BAsgn_list_sem tl).(Berr);
      Binf := ∅;
  |}
  | _ =>
  {|
      Bnrm := Rels.id;
      Berr := ∅;
      Binf := ∅;
  |}
end.

Definition eval_cond_expr (e: option expr): option EDenote :=
  match e with
  | Some (EBinop op e1 e2) =>
      Some (binop_sem op (element_sem (e1)) (element_sem (e2)))
  | Some (EUnop op e1) =>
      Some (unop_sem op (element_sem (e1)))
  | None => None
  end.


Definition BB_jmp_sem (BB: BasicBlock): BDenote := {| 
  Bnrm := 
    let jump_dest_1 := BB.(jump_info).(jump_dest_1) in
    let jmp_dest2 := BB.(jump_info).(jump_dest_2) in
    let jmp_cond := BB.(jump_info).(jump_condition) in
    (BJump_sem BB.(block_num) jump_dest_1 jmp_dest2 (eval_cond_expr jmp_cond)).(Bnrm); 
  Berr := ∅;
  Binf := ∅;
|}.

Definition BB_cmds_sem (BB: BasicBlock): BDenote := {| 
  Bnrm := 
    (BAsgn_list_sem BB.(cmd)).(Bnrm);
  Berr := ∅;
  Binf := ∅;
|}.

Definition BB_sem (BB: BasicBlock): BDenote := {|
  Bnrm := (BB_cmds_sem BB).(Bnrm) ∘ (BB_jmp_sem BB).(Bnrm) ;
  Berr :=  ∅;
  Binf :=  ∅;
|}.

Fixpoint BB_sem_union (BBs: list BasicBlock): BDenote :=  {|
  Bnrm := 
    match BBs with 
    | BB :: tl => (BB_sem BB).(Bnrm) ∪ (BB_sem_union tl).(Bnrm)
    | nil => ∅
    end;
  Berr := ∅;
  Binf := ∅;
|}.

Fixpoint Iter_nrm_BBs_n (BD: BDenote) (n: nat):  BB_state -> BB_state  -> Prop :=
  match n with
  | O => Rels.id
  | S n0 => (BD.(Bnrm) ∘ (Iter_nrm_BBs_n BD n0))
  end.


(*
S = ⋃ BBsems
BBlistsem = I ∪ S ∪ (S ∘ S) ∪ (S ∘ S ∘ S) U ... *)

(* Combine the single_step_stem to form the denotation for BB_list_sem.
   Not certain about its correctness  *)
Definition BB_list_sem (BBs: list BasicBlock): BDenote := {|
  Bnrm := ⋃ (Iter_nrm_BBs_n (BB_sem_union BBs)); 
  Berr := ∅;
  Binf := ∅;
|}.

(* End of Denotations *)

