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


Fixpoint basic_block_gen (cmds: list cmd) (BB_now: BasicBlock): list BasicBlock :=
match cmds with
| [] =>
    (* No more commands, return the current basic block *)
    [BB_now]

    (* 这里是表示取列表的头元素为CAsgn的情况，:: tl表示的是[列表剩下的所有元素] *)
| CAsgn x e :: tl =>
    (* Add the assignment command to the current basic block *)
    let BB_next := {|
    block_num := BB_now.(block_num); (* 这里block_num是不改的 *)
    commands := BB_now.(commands) ++ [CAsgn x e]; (* 这里是把CAsgn x e加到commands的末尾 *)
    jump_info := BB_now.(jump_info) (* 这里其实还是空 *)
    |} in
    basic_block_gen tl BB_next (* 用剩下的cmd和更新后的BB来进一步递归 *)

| CIf e c1 c2 :: tl => []

| CWhile pre e body :: tl => []

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
Definition BB_head (cmds : list cmd) : list cmd :=
  match basic_block_gen cmds empty_block with
  | [] => []
  | h :: _ => h.(cmd)
  end.

Definition remove_head (cmds : list cmd) : list cmd :=
tl cmds.

(* Prove that the removing the cmd will have the exact same length, probably useful *)
Lemma seq_cmd_retains_BB:
    forall (cmds: list cmd) (BB_now: BasicBlock),
        is_seq_cmds (BB_head cmds) = true ->
        cmd_list_len cmd_len (BB_head cmds) > 0 -> 
        length (basic_block_gen (remove_head cmds) BB_now) = length (basic_block_gen cmds BB_now).
Proof.
    Admitted.

        
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
    - intros. admit.
Admitted.


(* Prove that the generated cmds and the original cmds are exactly the same *)
Theorem seq_cmds_sound: 
    forall (cmds : list cmd),        
        is_seq_cmds (cmds) = true ->
        BB_head(cmds) = cmds.
Proof.
Admitted.
