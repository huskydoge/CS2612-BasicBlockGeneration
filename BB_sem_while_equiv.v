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



Lemma Q_while:
  forall (pre: list cmd) (e: expr) (body: list cmd),
  P pre (cmd_BB_gen) -> P body (cmd_BB_gen) -> Qb (CWhile pre e body).
Proof.
  intros. unfold Qb. intros. 
  (* get lemmas and select the right target *)
  rename H1 into jmp_prop. rename H2 into BBnow_num_prop. rename H3 into BBnow_not_jmp_toself.  right.
  (* get correct numbers *)
  set(BB_pre_num := BBnum). set(BB_body_num := S(BB_pre_num)). set(BB_next_num := S(BB_body_num)). set(BB_num2 := S(BB_next_num)).
  (* set basic basicblocks *)
  set(BB_pre := {|block_num := BB_pre_num;
                   commands := nil;
                   jump_info := {|
                      jump_kind := CJump;
                      jump_dest_1 := BB_body_num; 
                      jump_dest_2 := Some BB_next_num; 
                      jump_condition := Some e
                      |};
                   |}).
  set(BB_body := {|block_num := BB_body_num;
                 commands := nil;
                 jump_info := {|
                    jump_kind := UJump;
                    jump_dest_1 := BB_pre_num; 
                    jump_dest_2 := None; 
                    jump_condition := None
                    |};
                 |}).
  set(BB_next := {|block_num := BB_next_num;
                 commands := nil;
                 jump_info := BBnow.(jump_info)
                 |}).
  set(BBnow' := {|block_num := BBnow.(block_num);
                   commands := BBnow.(commands);
                   jump_info := {|
                      jump_kind := UJump;
                      jump_dest_1 := BB_pre_num; 
                      jump_dest_2 := None; 
                      jump_condition := None
                      |};
                   |}).
(* set and fill correct parameters *)
  set(BBs_wo_last := to_result(list_cmd_BB_gen cmd_BB_gen body nil BB_body BB_num2)). 
  set(BBs' := BBs_wo_last ++ BB_next :: nil).
  exists BBnow'. exists BBs'. exists BB_next_num. exists BBs_wo_last.
Admitted.