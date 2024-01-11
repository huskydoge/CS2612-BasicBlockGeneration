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