Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. 
Import SetsNotation.
Require Import compcert.lib.Integers.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.
Require Import Main.grammer.
Require Import Main.cmd_denotations.
Require Import Main.BB_generation.

Import Denotation.
Import EDenote.
Import CDenote.

Record BB_state: Type := {
  BB_num: nat;
  st: state
}.


Module BDenote.
Record BDenote: Type := {
  nrm: BB_state -> BB_state -> Prop;
  err: BB_state -> Prop;
  inf: BB_state -> Prop
}.
End BDenote.

Import BDenote.

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  | BDenote => exact (BDenote.nrm x)
  end.
Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  | BDenote => exact (BDenote.err x)
  end.

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).
Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).



Definition ujmp_sem (jum_dist: nat): BDenote :=
  {|
    nrm := fun bs1 bs2 =>
      bs1.(st) = bs2.(st) /\ bs2.(BB_num) = jum_dist;
    err := ∅;
    inf := ∅;
  |}.


Definition test_true_jmp (D: EDenote):
  state -> Prop :=
    (fun s => exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false_jmp (D: EDenote):
  state -> Prop :=
    (fun s => D.(nrm) s (Int64.repr 0)).


Definition cjmp_sem (jmp_dist1: nat) (jmp_dist2: nat) (D: EDenote) : BDenote :=
  {|
    nrm := fun bs1 bs2 => ((bs1.(st) = bs2.(st)) /\ 
            ((bs2.(BB_num) = jmp_dist1) /\ (test_true_jmp D bs1.(st)) \/ ((bs2.(BB_num) = jmp_dist2) /\ (test_false_jmp D bs1.(st)))));
    err := ∅; (* Ignore err cases now *)
    inf := ∅;
  |}.


Definition empty_sem : BDenote := {|
  nrm := ∅;
  err := ∅;
  inf := ∅
|}.

Definition jmp_sem (jmp_dist1: nat) (jmp_dist2: option nat)(D: option EDenote) :BDenote :=
  match D with 
  | None => ujmp_sem jmp_dist1 (* No expr *)
  | Some D => match jmp_dist2 with
              | None => ujmp_sem jmp_dist1
              | Some jmp_dist2 => cjmp_sem jmp_dist1 jmp_dist2 D
              end
  end.


Definition BAsgn_sem (BB_asgn_sem: CDenote) : BDenote := {|
  nrm := fun bs1 bs2 => 
    BB_asgn_sem.(nrm) bs1.(st) bs2.(st);
  err := ∅;
  inf := ∅;
|}.


Definition BJump_sem (BB_end: BDenote) (jmp_dist1: nat) (jmp_dist2: option nat) (D: option EDenote) : BDenote := {|
  nrm := fun bs1 bs2 => 
    exists i,
      bs1.(st) = i.(st) /\ (jmp_sem jmp_dist1 jmp_dist2 D).(nrm) i bs2;
  err := ∅;
  inf := ∅;
|}.


(* Should move the Theorem elsewhere, but it just came to me that we need it *)
Fixpoint is_seq_cmds (cmds : list cmd) : bool :=
  match cmds with

  | CAsgn x e :: tl => is_seq_cmds tl

  | CIf e c1 c2 :: tl => false

  | CWhile pre e body :: tl => false

  | _ => true

  end.

(* TODO: the cmds in the BBs generated are all BAsgn. *)

(*  *)
(* Fixpoint BAsgn_list_sem (BAsgn_sem_list: list BB_state) : BB_state :=
  match BAsgn_sem_list with 
  | cmd :: tl => BAsgn_sem ∘ BAsgn_list_sem tl
  | _ => Rels.id × Rels.id
  end. *)


(* Combine list of BAsgn and the final BJump *)
(* 
Definition BB_sem (BB: BasicBlock) BDenote := {|
  
|} *)



(* Definition single_step_sem (cmds: CDenote) (jmp_dist1: nat) (jmp_dist2: option nat) (D: option EDenote): BDenote :=
  {|
    nrm := fun bs1 bs2 => exists bs3,  
        cmds.(nrm) bs1.(st) bs3.(st) /\ (jmp_sem jmp_dist1 jmp_dist2 D).(nrm) bs3 bs2; 
    err := ∅;
    inf := ∅;
  |}
. *)





