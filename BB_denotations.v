Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.
Require Import Main.grammer.
Require Import Main.cmd_denotations.

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
    err := ∅; (* 条件跳转出错还没考虑*)
    inf := ∅;
  |}.


Definition empty_sem : BDenote := {|
  nrm := ∅;
  err := ∅;
  inf := ∅
|}.

Definition jmp_sem (jmp_dist1: nat) (jmp_dist2: option nat)(D: option EDenote) :BDenote :=
  match D with 
  | None => ujmp_sem jmp_dist1 (*没有传入E*)
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

Compute jmp_sem 1 None None.


Definition BJump_sem (BB_end: BDenote) (jmp_dist1: nat) (jmp_dist2: option nat) (D: option EDenote) : BDenote := {|
  nrm := fun bs1 bs2 => 
    exists i,
      bs1.(st) = i.(st) /\ (jmp_sem jmp_dist1 jmp_dist2 D).(nrm) i bs2;
  err := ∅;
  inf := ∅;
|}.

Definition single_step_sem (cmds: CDenote) (jmp_dist1: nat) (jmp_dist2: option nat) (D: option EDenote): BDenote :=
  {|
    nrm := fun bs1 bs2 => exists bs3,  
        cmds.(nrm) bs1.(st) bs3.(st) /\ (jmp_sem jmp_dist1 jmp_dist2 D).(nrm) bs3 bs2; 
        (**对于从bs1到bs2的单步执行，语义为存在一个bs3，它先执行了bs1中的basicblock语句，然后跳转到了bs2*)
    err := ∅;
    inf := ∅;
  |}
.





