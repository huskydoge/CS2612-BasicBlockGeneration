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
Require Import Main.BB_sem_asgn_equiv.
Require Import Main.BB_sem_while_equiv.
Require Import Main.BB_sem_if_equiv.


Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.
Import BDenote.


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


(* #TODO: fix p_nil*)
Lemma P_nil: forall cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results,
  P nil (cmd_BB_gen).
Proof.
  unfold P. intros.
  exists nil. exists BBnow. exists nil. exists BBnum. exists BBnow.(block_num).
  repeat split; try tauto.
  - rewrite append_nil_r. tauto.
  - intros. simpl. my_destruct H. cbn [Bnrm] in H.
    pose proof unfold_once ({|
        block_num := BBnow.(block_num);
        commands := nil;
        jump_info := BBnow.(jump_info)
      |} :: nil ++ nil) as key.
    sets_unfold in key. specialize (key x x0). apply key in H.
    clear key.
    destruct H as [case1 | case2].
    + rewrite case1 in H0. sets_unfold. rewrite H0 in H1. tauto.
    + sets_unfold. destruct case2 as [middle [cond1 cond2]].
      pose proof simplify_listsem_with_mismatch_num middle x0 {|
      block_num := BBnow.(block_num);
      commands := nil;
      jump_info := BBnow.(jump_info)
    |} nil as steps.
    assert(pre1: {|
    block_num := BBnow.(block_num);
    commands := nil;
    jump_info := BBnow.(jump_info)
  |}.(block_num) <> BB_num middle). admit.

    assert(pre2:
  BB_gen_properties.BBnum_set
    ({|
       block_num := BBnow.(block_num);
       commands := nil;
       jump_info := BBnow.(jump_info)
     |} :: nil)
  ∩ BB_gen_properties.BBjmp_dest_set
      ({|
         block_num := BBnow.(block_num);
         commands := nil;
         jump_info := BBnow.(jump_info)
       |} :: nil) == ∅). admit.
    pose proof (steps pre1 pre2 cond2) as p.
    pose proof nil_sem middle x0 p. tauto.
  - intros. exists {| st := a ; BB_num := BBnow.(block_num) |}.
    exists {| st := a0 ; BB_num := BBnow.(block_num) |}.
    repeat split; simpl; try tauto.
    simpl in H. sets_unfold in H. rewrite <- H. admit. admit.
  - admit. (* err case *)
  - admit.  (* err case *)
  - admit. (* inf case *)
  - admit. (* inf case *) 
Admitted.



Lemma P_cons:
  forall (c: cmd) (cmds: list cmd) (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results),
  Qb c -> P cmds cmd_BB_gen -> P (c :: cmds) (cmd_BB_gen).
Proof.
  intros.
  destruct c.
  - admit.
  - admit.
  - admit.
Admitted. 


Section BB_sound.

Variable cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results.
Variable cmd_BB_gen_sound: forall (c: cmd), Qb c.

Fixpoint cmd_list_BB_gen_sound (cmds: list cmd): P cmds cmd_BB_gen :=
  match cmds with
  | nil => P_nil cmd_BB_gen
  | c :: cmds0 => P_cons c cmds0 cmd_BB_gen (cmd_BB_gen_sound c) (cmd_list_BB_gen_sound cmds0)
  end.

End BB_sound.

Fixpoint cmd_BB_gen_sound (c: cmd): Qb c :=
  match c with
  | CAsgn x e => Q_asgn x e
  | CIf e cmds1 cmds2 =>
      Q_if e cmds1 cmds2
        (cmd_list_BB_gen_sound cmd_BB_gen cmd_BB_gen_sound cmds1)
        (cmd_list_BB_gen_sound cmd_BB_gen cmd_BB_gen_sound cmds2)
  | CWhile cmds1 e cmds2 =>
      Q_while cmds1 e cmds2
        (cmd_list_BB_gen_sound cmd_BB_gen cmd_BB_gen_sound cmds1)
        (cmd_list_BB_gen_sound cmd_BB_gen cmd_BB_gen_sound cmds2)
  end.


Lemma cmd_BB_gen_sound_correct:
  forall (c: cmd),
  Qb c.
Proof.
  apply cmd_BB_gen_sound.
Qed.

Lemma cmd_list_BB_gen_sound_correct:
  forall (cmds: list cmd),
  P cmds cmd_BB_gen.
Proof.
  apply cmd_list_BB_gen_sound.
  apply cmd_BB_gen_sound_correct.
Qed.