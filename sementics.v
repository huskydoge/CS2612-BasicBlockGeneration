Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Init.Specif.
Require Import Coq.Lists.List.

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


(* If all cmds are CAsgn, then the length of the generated BB is 1 *)

(* Get the head element of the BB_block *)
Definition BB_head (cmds: list cmd) : list cmd :=
  match basic_block_gen cmds empty_block with
  | [] => []
  | h :: _ => h.(cmd)
  end.



(* Prove that the adding an CAsgn cmd will have the exact same length, probably useful *)
Lemma seq_cmd_retains_BB:
    forall (asgn: cmd) (cmds: list cmd) (BB_now: BasicBlock),
        is_seq_cmds (BB_head cmds) = true ->
        is_seq_cmds [asgn] = true ->
        cmd_list_len cmd_len (BB_head cmds) > 1 -> 
        length (basic_block_gen (asgn :: cmds) BB_now) = length (basic_block_gen cmds BB_now).
Proof.
  intros.
  induction cmds.
  - simpl. 
    unfold basic_block_gen. 
    unfold is_seq_cmds in H0.
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


Theorem seq_cmds_single_BB:
    forall (cmds : list cmd),        
        is_seq_cmds cmds = true ->
        cmd_list_len cmd_len cmds > 0 -> 
        length (basic_block_gen cmds empty_block) = 1.
Proof.
  intros.
  unfold basic_block_gen.
  induction cmds.
  - simpl. reflexivity.
  - intros. simpl.
    destruct a.
    + simpl. 
      apply IHcmds in H.
      * admit.
      * pose proof cmd_list_len_nonneg cmds. admit.  
    + simpl in H. inversion H.
    + simpl in H. inversion H. 
Admitted.


(* Prove that the generated cmds and the original cmds are exactly the same *)
Theorem seq_cmds_sound: 
    forall (cmds : list cmd),        
        is_seq_cmds (cmds) = true ->
        BB_head(cmds) = cmds.
Proof. 
  intros.
  unfold BB_head.
  unfold basic_block_gen.
  induction cmds.
  - simpl. reflexivity.
  - simpl.
      destruct a.
      + simpl. 
        apply IHcmds in H.
        
        admit.
      + simpl in H. inversion H.
      + simpl in H. inversion H.
Admitted.