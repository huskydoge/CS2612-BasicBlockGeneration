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
  set(BB_pre_num := BBnum). set(BB_body_num := S(BB_pre_num)). set(BB_next_num := S(BB_body_num)). set(BB_num1 := S(BB_next_num)).
(* set basic basicblocks *)
  remember( {|block_num := BB_pre_num;
                   commands := nil;
                   jump_info := {|
                      jump_kind := CJump;
                      jump_dest_1 := BB_body_num; 
                      jump_dest_2 := Some BB_next_num; 
                      jump_condition := Some e
                      |};
                   |}) as BB_pre.
  remember ( {|block_num := BB_body_num;
                 commands := nil;
                 jump_info := {|
                    jump_kind := UJump;
                    jump_dest_1 := BB_pre_num; 
                    jump_dest_2 := None; 
                    jump_condition := None
                    |};
                 |}) as BB_body. 
  remember({|block_num := BB_next_num;
                 commands := nil;
                 jump_info := BBnow.(jump_info)
                 |}) as BB_next.
  remember({|block_num := BBnow.(block_num);
                   commands := BBnow.(commands);
                   jump_info := {|
                      jump_kind := UJump;
                      jump_dest_1 := BB_pre_num; 
                      jump_dest_2 := None; 
                      jump_condition := None
                      |};
                   |}) as BBnow'. 
(* set and fill correct parameters *)
  remember(list_cmd_BB_gen cmd_BB_gen pre nil BB_pre BB_num1) as BB_pre_generated_results.
  set(BB_num2 := BB_pre_generated_results.(next_block_num)).
  remember(list_cmd_BB_gen cmd_BB_gen body nil BB_body BB_num2) as BB_body_generated_results.
  remember(to_result(BB_pre_generated_results)++to_result(BB_body_generated_results)) as BBs_wo_last. 
  remember(BBs_wo_last ++ BB_next :: nil) as BBs'.
  exists BBnow'. exists BBs'. exists BB_next_num. exists BBs_wo_last.

(*assert 1*)
  assert ((cmd_BB_gen (CWhile pre e body) BBs BBnow BB_pre_num).(BasicBlocks) ++
  (cmd_BB_gen (CWhile pre e body) BBs BBnow BB_pre_num).(BBn) :: nil =
  BBs ++ (BBnow' :: nil) ++ BBs').
  {
  cbn[cmd_BB_gen]. simpl. 
  subst BB_pre_num. subst BB_body_num. subst BB_next_num. subst BB_num1.
  rewrite <- HeqBBnow'.  rewrite <- HeqBB_pre. 
  rewrite <- HeqBB_pre_generated_results. subst BB_num2. rewrite <- HeqBB_body.
  rewrite <- HeqBB_body_generated_results. rewrite <- HeqBBs_wo_last. rewrite <- HeqBB_next. 
  rewrite HeqBBs'. 
  rewrite <- app_assoc. reflexivity.
  }

(*assert 2*)
assert ((cmd_BB_gen (CWhile pre e body) BBs BBnow BB_pre_num).(BasicBlocks) = BBs ++ (BBnow' :: nil) ++ BBs_wo_last).
  {
  cbn[cmd_BB_gen]. simpl.
   subst BB_pre_num. subst BB_body_num. subst BB_next_num. subst BB_num1.
  rewrite <- HeqBBnow'.  rewrite <- HeqBB_pre. 
  rewrite <- HeqBB_pre_generated_results. subst BB_num2. rewrite <- HeqBB_body.
  rewrite <- HeqBB_body_generated_results. rewrite HeqBBs_wo_last. reflexivity.
  }

(*assert 3*)
assert(((cmd_BB_gen (CWhile pre e body) BBs BBnow BB_pre_num).(BBn)).(block_num) = BB_next_num).
  {
  cbn[cmd_BB_gen]. simpl. subst BB_pre_num. subst BB_next_num. reflexivity.
  }
 
  
Admitted.