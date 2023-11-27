Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Init.Specif.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.


Require Import Main.grammer.
Require Import Main.BB_generation.

Local Open Scope bool.
Local Open Scope list.
Local Open Scope nat.

(* 判断 cmds 是不是一串 CAsgn*)
Fixpoint is_seq_cmds (cmds : list cmd) : bool :=
  match cmds with
  | [] => true
  
  | CAsgn x e :: tl => is_seq_cmds tl

  | CIf e c1 c2 :: tl => false

  | CWhile pre e body :: tl => false

  end.

(* 判断 一个 cmd 是不是 CAsgn*)
Definition is_CAsgn (cmd: cmd) : bool :=
  match cmd with
  | CAsgn _ _ => true
  | _ => false
  end.


Definition empty_block := {|
  block_num := 0;
  commands := [];
  jump_info := {|
      jump_kind := UJump;
      jump_dist_1 := 0;
      jump_dist_2 := None;
      jump_condition := None
    |}
|}.


(* Not Empty BB *)
Definition not_empty_BBs (BBs: list BasicBlock) :bool := 
  match BBs with
  | [] => false
  | _  => true
  end.
   

(* If all cmds are CAsgn, then the length of the generated BB is 1 *)

(* Get the head element of the BB_block *)
Definition BB_head (cmds: list cmd) : list cmd :=
  match (list_cmd_BB_gen cmd_BB_gen cmds [empty_block]).(BasicBlocks) with
  | [] => []
  | h :: _ => h.(cmd)
  end.
  
(*证明两个BB list相加后求长度和分别求长度再相加效果一致*)
Lemma distributive_length_add: forall (BBs1: list BasicBlock) (BBs2: list BasicBlock),
  length (BBs1) + length (BBs2) = length (BBs1 ++ BBs2).
Proof.
  intros BBs1.
  induction BBs1; simpl.
  - reflexivity.
  - intros BBs2. rewrite <- IHBBs1. reflexivity.
Qed.

(* 定义一个函数，删除列表中的最后一个元素 *)
Fixpoint remove_last {X : Type} (l : list X) : list X :=
  match l with
  | [] => [] (* 空列表返回空 *)
  | [x] => [] (* 单元素列表返回空 *)
  | x :: xs => x :: remove_last xs (* 递归地删除最后一个元素 *)
  end.

Lemma length_cons : forall (X : Type) (x : X) (l : list X),
  length (x :: l) = S (length l).
Proof.
  intros X x l. simpl. reflexivity.
Qed.

Lemma length_move_front_to_back : forall (X : Type) (a : X) (xl : list X),
  length (a :: xl) = length (xl ++ [a]).
Proof.
  intros X a xl.
  simpl.
  rewrite app_length.
  simpl.
  rewrite Nat.add_1_r.
  reflexivity.
Qed.

(* 一个列表，删除最后一个元素会让它的长度减少 1 *)
Lemma remove_last_decreases_length : forall (X : Type) (l : list X) (e: X),
  length (remove_last (l ++ [e])) = length l.
Proof.
  intros X l H.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - simpl.
    assert (xs ++ [H] <> []). {
      induction xs.
        + discriminate.
        + discriminate.
    }
    destruct (xs ++ [H]).
    + contradiction H0;reflexivity.
    + rewrite length_cons.
      rewrite IH.
      reflexivity.
Qed.

(* 一个BasicBlocks列表，删除最后一个元素会让它的长度减少 1 *)
Lemma BB_delete_last_length: forall (BBs: list BasicBlock) (BB: BasicBlock),
length (remove_last (BBs ++ [BB])) = length BBs.
Proof.
  intros BBs BB.
  apply remove_last_decreases_length.
Qed.

  
(* BasicBlocks的两种连接方式等价 *)
Lemma BB_add_equal: forall (BBs: list BasicBlock) (BB: BasicBlock),
  [BB] ++ BBs = BB :: BBs.
Proof.
  reflexivity.
Qed.

(* 一个BasicBlocks列表，删除最后一个元素再加上一个元素的长度不变 *)
Lemma delete_one_add_one_length: forall (BB_pre: list BasicBlock) (BB_tail: BasicBlock) (BB_new: BasicBlock),
  length (remove_last (BB_pre ++ [BB_tail]) ++ [BB_new]) = length (BB_pre ++ [BB_tail]).
Proof.
  intros.
  rewrite <- distributive_length_add.
  rewrite BB_delete_last_length.
  rewrite <- distributive_length_add.
  simpl.
  reflexivity.
Qed.

(* Prove that the adding an CAsgn cmd will have the exact same length, probably useful *)
Lemma seq_cmd_retains_BB:
    forall (asgn: cmd) (cmds: list cmd) (BB_pre: list BasicBlock) (BB_tail: BasicBlock),
        is_seq_cmds [asgn] = true -> 
        length (list_cmd_BB_gen cmd_BB_gen ([asgn] ++ cmds) (BB_pre ++ [BB_tail])).(BasicBlocks) = length (list_cmd_BB_gen cmd_BB_gen cmds (BB_pre ++ [BB_tail])).(BasicBlocks).
Proof.
  intros.
  induction cmds.
  * induction asgn; unfold is_seq_cmds in H; simpl.
    - 



    - discriminate.
  * induction asgn; unfold is_seq_cmds in H.
    - simpl.
      admit.
      

    - discriminate.
    - discriminate.
Admitted.
    

Lemma cmd_list_len_nonneg:
    forall (cmds: list cmd),
        cmd_list_len cmd_len cmds >= 0.
Proof.
  intros.
  induction cmds.
  - simpl. lia.
  - simpl. destruct a.
    + simpl. lia.
    + simpl. lia.
    + simpl. lia.
Qed.

Lemma seq_cmd_aux1:
  forall (cmds: list cmd) (c1: cmd),
    is_seq_cmds [c1] = true ->
    is_seq_cmds (c1 :: cmds) = true ->
    is_seq_cmds cmds = true.
Proof.
  intros.
  unfold is_seq_cmds in H.
  assert((is_CAsgn c1) = true). {
    unfold is_CAsgn. 
    apply H.
  }
  unfold is_seq_cmds in H0. 
  destruct c1.
  + unfold is_seq_cmds.
    apply H0.
  + discriminate.
  + discriminate.
Qed.
  


Theorem seq_cmds_single_BB:
    forall (cmds : list cmd),        
        is_seq_cmds cmds = true ->
        length (list_cmd_BB_gen cmd_BB_gen cmds [empty_block]).(BasicBlocks) = 1.
Proof.
  intros.
  induction cmds.
  - simpl. lia.
  - intros.
    destruct a.
    + pose proof seq_cmd_retains_BB.
      pose proof seq_cmd_aux1 cmds (CAsgn x e).
      assert ((is_seq_cmds [CAsgn x e]) = true). {
        unfold is_seq_cmds. tauto.
      }
      (* apply H1 in H2.
      apply IHcmds in H. *)
      pose proof seq_cmd_retains_BB (CAsgn x e) cmds [empty_block].
      pose proof H2.
      apply H1 in H2.
      apply H3 in H4.
      apply IHcmds in H2.
      simpl in H4. simpl.
      rewrite H4.
      apply H2.
      apply H.
    + simpl in H. inversion H.
    + simpl in H. inversion H. 
Qed.

(* Prove that the generated cmds and the original cmds are exactly the same *)
Theorem seq_cmds_sound: 
    forall (cmds : list cmd),        
        is_seq_cmds (cmds) = true ->
        BB_head (cmds) = cmds.
Proof. 
  intros.
  induction cmds.
  - simpl. reflexivity.
  - simpl.
    destruct a.
    + apply IHcmds in H.
      unfold BB_head.
      unfold BB_head in H.
      simpl.
      admit.
    + simpl in H. inversion H.
    + simpl in H. inversion H.
Admitted.