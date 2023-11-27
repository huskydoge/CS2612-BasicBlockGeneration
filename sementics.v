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

Fixpoint is_seq_cmds (cmds : list cmd) : bool :=
  match cmds with
  | [] => true
  
  | CAsgn x e :: tl => is_seq_cmds tl

  | CIf e c1 c2 :: tl => false

  | CWhile pre e body :: tl => false

  end.


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




Lemma delete_one_add_one_length: forall (BBs: list BasicBlock) (BB: BasicBlock),
  not_empty_BBs BBs = true->
  length (delete_last BBs ++ [BB]) = length BBs.
Proof.
  intros.
  destruct BBs.
  + discriminate.
  + simpl.
    pose proof distributive_length_add (match BBs with
    | [] => []
    | _ :: _ => b :: delete_last BBs
    end) ([BB]).
    rewrite <- H0.
    simpl.




(* Prove that the adding an CAsgn cmd will have the exact same length, probably useful *)
Lemma seq_cmd_retains_BB:
    forall (asgn: cmd) (cmds: list cmd) (BBs: list BasicBlock),
        is_seq_cmds [asgn] = true -> 
        not_empty_BBs BBs = true ->
        length (list_cmd_BB_gen cmd_BB_gen ([asgn] ++ cmds) BBs).(BasicBlocks) = length (list_cmd_BB_gen cmd_BB_gen cmds BBs).(BasicBlocks).
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