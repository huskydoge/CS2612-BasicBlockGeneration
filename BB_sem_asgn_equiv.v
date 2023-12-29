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
Require Import Main.BB_aux_proof.

Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.
Import BDenote.


Lemma Q_asgn:
  forall (x: var_name) (e: expr),
  Qb (CAsgn x e).
Proof.
  intros. unfold Qb. left. rename H into jmp_prop.
  exists {|
    block_num := BBnow.(block_num);
    commands := BBnow.(cmd) ++ {| X:= x; E:= e|} :: nil;
    jump_info := BBnow.(jump_info);
  |}.
  exists {| X := x; E := e|}.
  split.
  + reflexivity.
  + split. tauto. split.
    - unfold BAsgn_list_sem. simpl.
      sets_unfold. intros.
      split; intros.
      * destruct H as [? [? [? [? [? [? ?]]]]]].
        destruct H as [? ?].
        destruct H as [? ?].
        destruct H as [[? ?] ?].
        exists x3.
        rewrite H0 in H.
        rewrite <- H4 in H1.
        rewrite H1 in H.
        split. apply H. split. apply H.
        destruct H as [? [? ?]].
        intros.
        specialize (H7 Y). apply H7 in H8.
        rewrite H8. 
        tauto.
      * destruct H as [? [? [? ?]]].
        exists {| st := a; BB_num := BBnow.(block_num) |}.
        exists {| st := a0; BB_num := BBnow.(block_num) |}.
        split.
        ++ simpl.
           exists {| st := a0; BB_num := BBnow.(block_num) |}.
           split. split.
           exists x0. simpl.
           split. apply H. 
           split. apply H0.
           intros. specialize (H1 y). apply H1 in H2. rewrite H2. tauto.
           simpl. tauto.
           simpl. tauto.
        ++ simpl. tauto.
    - admit.
    - admit. 
Admitted.