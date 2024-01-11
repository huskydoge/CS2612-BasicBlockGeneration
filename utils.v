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

(*如果l = l1 + l2，l1不为空，那么l不为空*)
Lemma not_nil_l:
  forall (A: Type) (l1 l2: list A),
  l1 <> nil -> l1 ++ l2 <> nil.
Proof.
  intros. unfold not. intros. destruct l1.
  - apply H. reflexivity.
  - inversion H0.
Qed.

(*如果l = l1 + l2，l2不为空，那么l不为空*)
Lemma not_nil_r:
  forall (A: Type) (l1 l2: list A),
  l2 <> nil -> l1 ++ l2 <> nil.
Proof.
  intros. unfold not. intros. destruct l1.
  - inversion H0. simpl in H0. tauto.
  - inversion H0.
Qed.


Lemma In_l1_or_l2:
  forall (A: Type) (l1 l2: list A) (a: A),
  In a (l1 ++ l2) -> In a l1 \/ In a l2.
Proof.
  intros. induction l1.
  - simpl in H. right. apply H.
  - simpl in H. destruct H.
    + left. left. apply H.
    + apply IHl1 in H. destruct H.
      * left. right. apply H.
      * right. apply H.
Qed.



Lemma cut_nil_r:
  forall (A: Type) (x y:  A),
  x::nil = y::nil <-> x = y.
Proof.
  intros. split; intros.
  - inversion H. reflexivity.
  - rewrite H. reflexivity.
Qed.

Lemma cut_eq_part_l:
  forall (A: Type) (a b: A) (l1 l2: list A),
  l1 ++ a :: l2 = l1 ++ b :: l2 -> a = b.
Proof.
  intros.
  induction l1.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. inversion H. apply IHl1. apply H1.
Qed.

Lemma cut_eq_part_r:
  forall (A: Type) (a b: A) (l1 l2: list A),
  l1 ++ a :: l2 = l1 ++ b :: l2 -> a = b.
Proof.
  intros.
  induction l1.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. inversion H. apply IHl1. apply H1.
Qed.

Lemma cut_eq_part_list_l:
  forall (A: Type) (l1 l2 l3: list A),
  l1 ++ l2 = l1 ++ l3 -> l2 = l3.
Proof.
  intros.
  induction l1.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. inversion H. apply IHl1. apply H1.
Qed.


(*a obvious transform*)
Lemma tran_ele:
  forall (A: Type)(l1 l2: list A)(a: A),
  l1 ++ a::l2 = l1 ++ a::nil ++ l2.
Proof.
  intros. 
  simpl.
  reflexivity.
Qed.

Lemma append_nil_r : forall A (l : list A),
  l ++ nil = l.
Proof.
  intros A l.
  induction l as [| x xs IH].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = x :: xs *)
    simpl. rewrite IH. reflexivity.
Qed.

Lemma append_nil_l : forall A (l : list A),
  nil ++ l = l.
Proof.
  intros A l.
  induction l as [| x xs IH].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = x :: xs *)
    simpl. rewrite <- IH. reflexivity.
Qed.

Lemma eli_nil:
  forall(A: Type) (l1 l2: list A)(a: A),
  l1 ++ a::nil = l2 ++ a::nil -> l1 = l2.
Proof.
  intros.
Admitted. 


Lemma cut_eq_part_list_r:
  forall (A: Type) (l1 l2 l3: list A),
  l2 ++ l1 = l3 ++ l1 -> l2 = l3.
Proof.
  intros. revert l2 l3 H.
  induction l1.
  - intros. rewrite app_nil_r in H. rewrite app_nil_r in H. apply H.
  - intros. inversion H.
    pose proof tran_ele A l2 l1 a. 
    pose proof tran_ele A l3 l1 a. 
    rewrite H0 in H. rewrite H2 in H.
    pose proof IHl1 (l2 ++ a :: nil) (l3 ++ a :: nil).
    assert ( (l2 ++ a :: nil) ++ l1 = (l3 ++ a :: nil) ++ l1).
    {
      rewrite app_assoc_reverse.
      rewrite <- app_assoc.
      simpl.
      simpl in H. tauto.
    }
    pose proof H3 H4.
    pose proof IHl1 l2 l3.
    pose proof eli_nil A l2 l3 a H5. tauto.
Qed.

Lemma cut_eq_part_list_r':
  forall (A: Type) (l1 l2 l3: list A),
  l2 = l3 -> l2 ++ l1 = l3 ++ l1.
Proof.
  intros. revert l2 l3 H.
  induction l1.
  - simpl. intros. rewrite app_nil_r. rewrite app_nil_r. apply H.
  - intros. simpl. 
    pose proof tran_ele A l2 l1 a. rewrite H0.
    pose proof tran_ele A l3 l1 a. rewrite H1.
    assert (l2 ++ a :: nil = l3 ++ a :: nil).
    {
      rewrite H. reflexivity.
    }
    specialize (IHl1 (l2 ++ a :: nil) (l3 ++ a :: nil) H2).
    rewrite <- app_assoc in IHl1. simpl in IHl1. 
    rewrite <- app_assoc in IHl1. simpl in IHl1. tauto.
Qed.


(*如果在BBs里，那么一定在BBs ++ tl里*)
Lemma In_tail_inclusive:
  forall (BBs : list BasicBlock) (BB tl : BasicBlock),
    In BB BBs -> In BB (BBs ++ tl::nil).
Proof.
  intros. induction BBs.
  - unfold In in H. tauto.
  - unfold In. simpl.
    unfold In in H. destruct H as [? | ?].
    + left. apply H.
    + right. pose proof IHBBs H. apply H0.
Qed. 

