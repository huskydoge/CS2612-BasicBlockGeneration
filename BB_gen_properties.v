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
Require Import Main.BB_denotations.


Definition BB_num_set := nat -> Prop.

Definition add_one_num (oldset: BB_num_set)(new: nat): BB_num_set :=
  fun BBnum => oldset BBnum \/ BBnum = new.

(*BBnum \in (nat \cap [BBnum_start, BBnum_end]) *)
Definition BBnum_start_end_set (BBnum_start: nat) (BBnum_end: nat): BB_num_set :=
  fun BBnum => Nat.le BBnum_start BBnum /\ Nat.le BBnum BBnum_end.

Definition BBnum_set (BBs: list BasicBlock): BB_num_set :=
  (* 拿到一串BBs里，所有出现的BBnum，包括block num和jmp dest num*)
  fun BBnum => exists BB, (In BB BBs) /\ BB.(block_num) = BBnum.

Definition BBjmp_dest_set (BBs: list BasicBlock): BB_num_set :=
  fun BBnum => exists BB, (In BB BBs) /\ (BB.(jump_info).(jump_dest_1) = BBnum \/ BB.(jump_info).(jump_dest_2) = Some BBnum).

(*BBnumset BBs >= num*)
Definition BB_all_ge (BBs: list BasicBlock)(num: nat): Prop :=
    forall BB, In BB BBs -> Nat.le num BB.(block_num) \/ BBs = nil.
(*BBnumset BBs < num*)
Definition BB_all_lt (BBs: list BasicBlock)(num: nat): Prop :=
    forall BB, In BB BBs -> Nat.lt BB.(block_num) num \/ BBs = nil.

(*定义自然数区间*)
Definition section (startnum endnum: nat) : nat -> Prop :=
  fun BBnum => Nat.le startnum BBnum /\ Nat.le BBnum endnum.

Definition P_BBgen_range (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results)(cmds: list cmd): Prop :=
    forall startnum endnum BBs BBnow BBnow' BBdelta,
    let res := (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow startnum) in
    let basicblocks := to_result res in
    endnum = res.(next_block_num)
    -> 
      basicblocks = BBs ++ BBnow'::nil ++ BBdelta ->
      BBnow'.(block_num) <> BBnow'.(jump_info).(jump_dest_1) ->
      Some BBnow'.(block_num) <> BBnow'.(jump_info).(jump_dest_2) ->
    (
      BB_all_ge BBdelta startnum /\
      BB_all_lt BBdelta endnum /\ 
      BBjmp_dest_set (BBnow'::BBdelta) ⊆ add_one_num (section startnum endnum) BBnow.(jump_info).(jump_dest_1)
    ).

Definition Q_BBgen_range (c: cmd): Prop :=
    forall startnum endnum BBs BBnow BBnow' BBdelta,
    let res := (cmd_BB_gen c BBs BBnow startnum) in
    let basicblocks := to_result res in
    endnum = res.(next_block_num)
    -> basicblocks = BBs ++ BBnow'::nil ++ BBdelta ->
    (
      BB_all_ge BBdelta startnum /\
      BB_all_lt BBdelta endnum /\
      BBjmp_dest_set (BBnow'::BBdelta) ⊆ add_one_num (section startnum endnum) BBnow.(jump_info).(jump_dest_1)
    ).


Lemma Q_if_BBgen_range:
forall (e: expr) (c1 c2: list cmd),
    P_BBgen_range cmd_BB_gen c1  ->
    P_BBgen_range cmd_BB_gen c2  ->

    Q_BBgen_range (CIf e c1 c2).
Proof.
 intros.
  Admitted.

Lemma Q_while_BBgen_range:
forall (e: expr) (c1 c2: list cmd),

    P_BBgen_range cmd_BB_gen c1 ->
    P_BBgen_range cmd_BB_gen c2 ->

    Q_BBgen_range (CWhile c1 e c2).
Proof.
  Admitted.

Lemma length_eq : forall (A : Type) (xs ys : list A),
  xs = ys -> length xs = length ys.
Proof.
  intros A xs ys H.
  rewrite H.
  reflexivity.
Qed.

(*这个肯定成立，没有新的block*)
Lemma Q_asgn_BBgen_range:
forall  (x: var_name) (e: expr),
    Q_BBgen_range (CAsgn x e).
Proof.
  intros. unfold Q_BBgen_range. intros. simpl in H0. unfold to_result in H0. simpl in H0.
  pose proof app_inv_head BBs  ({|
     block_num := BBnow.(block_num);
     commands := BBnow.(cmd) ++ {| X := x; E := e |} :: nil;
     jump_info := BBnow.(jump_info) |} :: nil) (BBnow' :: BBdelta) H0.
  clear H0. assert(BBdelta=nil).
{
  destruct BBdelta. tauto. pose proof length_eq BasicBlock ( {|
     block_num := BBnow.(block_num);
     commands := BBnow.(cmd) ++ {| X := x; E := e |} :: nil;
     jump_info := BBnow.(jump_info) |} :: nil) (BBnow' :: b :: BBdelta) H1. unfold length in H0. discriminate.
}
  rewrite H0. split.
  - unfold BB_all_ge. intros. tauto.
  - unfold BB_all_lt. intros. admit.
Admitted.

Lemma P_BBgen_nil: forall (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results),
    P_BBgen_range cmd_BB_gen nil.
Proof.
  intros. unfold P_BBgen_range. intros. simpl in H0. unfold to_result in H0. simpl in H0. 
  pose proof app_inv_head BBs (BBnow :: nil) (BBnow' :: BBdelta) H0.
  assert(BBdelta = nil).

(* {
  destruct BBdelta. tauto. pose proof length_eq BasicBlock (BBnow :: nil) (BBnow' :: b :: BBdelta) H1. discriminate.
} 
  rewrite H2. split.
  - unfold BB_all_ge. intros. tauto.
  - unfold BB_all_lt. intros. split. 
    + intros. tauto.
    + simpl. *)
Admitted.

Lemma P_BBgen_con:
    forall (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results) (c: cmd) (cmds: list cmd),
    Q_BBgen_range c ->
    P_BBgen_range cmd_BB_gen cmds ->
    P_BBgen_range cmd_BB_gen (c::cmds).
Proof.
Admitted.


Section BB_gen_range_sound.

Variable cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results.
Variable BB_gen_range_soundness: forall (c: cmd), Q_BBgen_range c.

Fixpoint BBgen_list_range_soundness (cmds: list cmd): P_BBgen_range cmd_BB_gen cmds :=
  match cmds with
  | nil => P_BBgen_nil cmd_BB_gen
  | c :: cmds0 => P_BBgen_con cmd_BB_gen c cmds0 (BB_gen_range_soundness c) (BBgen_list_range_soundness cmds0)
  end.

End BB_gen_range_sound.

Fixpoint BB_gen_range_soundness (c: cmd): Q_BBgen_range c :=
  match c with
  | CAsgn x e => Q_asgn_BBgen_range x e
  | CIf e cmds1 cmds2 =>
      Q_if_BBgen_range e cmds1 cmds2
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds1)
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds2)
  | CWhile cmds1 e cmds2 =>
      Q_while_BBgen_range e cmds1 cmds2
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds1)
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds2)
  end.


Lemma BBgen_range_single_soundness_correct:
    forall (c: cmd),
    Q_BBgen_range c.
Proof.
    apply BB_gen_range_soundness.
Qed.

Lemma BBgen_range_list_soundness_correct:
    forall (cmds: list cmd),
    P_BBgen_range cmd_BB_gen cmds.
Proof.
    apply BBgen_list_range_soundness.
    pose proof BBgen_range_single_soundness_correct.
    apply H.
Qed.






