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


(*BBnumset BBs >= num*)
Definition BB_all_ge (BBs: list BasicBlock)(num: nat): Prop :=
    forall BB, In BB BBs -> Nat.le num BB.(block_num).
(*BBnumset BBs < num*)
Definition BB_all_lt (BBs: list BasicBlock)(num: nat): Prop :=
    forall BB, In BB BBs -> Nat.lt BB.(block_num) num.



Definition P_BBgen_range (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results)(cmds: list cmd): Prop :=
    forall startnum endnum BBs BBnow,
    let res := (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow startnum) in
    let basicblocks := to_result res in
    endnum = res.(next_block_num)
    -> 
    (
      exists BBnow' BBdelta,
      basicblocks = BBs ++ BBnow'::nil ++ BBdelta /\
      BB_all_ge BBdelta startnum /\
      BB_all_lt BBdelta endnum
    ).

Definition Q_BBgen_range (c: cmd): Prop :=
    forall startnum endnum BBs BBnow,
    let res := (cmd_BB_gen c BBs BBnow startnum) in
    let basicblocks := to_result res in
    endnum = res.(next_block_num)
    ->
    (
      exists BBnow' BBdelta,
      basicblocks = BBs ++ BBnow'::nil ++ BBdelta /\
      BB_all_ge BBdelta startnum /\
      BB_all_lt BBdelta endnum
    ).


Lemma Q_if_BBgen_range:
forall (e: expr) (c1 c2: list cmd),
    P_BBgen_range cmd_BB_gen c1  ->
    P_BBgen_range cmd_BB_gen c2  ->

    Q_BBgen_range (CIf e c1 c2).
Proof.
Admitted.

Lemma Q_while_BBgen_range:
forall (e: expr) (c1 c2: list cmd),

    P_BBgen_range cmd_BB_gen c1 ->
    P_BBgen_range cmd_BB_gen c2 ->

    Q_BBgen_range (CWhile c1 e c2).
Proof.
  Admitted.

(*这个肯定成立，没有新的block*)
Lemma Q_asgn_BBgen_range:
forall  (x: var_name) (e: expr),
    Q_BBgen_range (CAsgn x e).
Proof.
  intros. unfold Q_BBgen_range. intros. split.
  - unfold cmd_BB_gen. simpl. admit.
  - exists {| block_num := BBnow.(block_num);
              commands := BBnow.(commands) ++ {| X := x; E := e |} :: nil;
              jump_info := BBnow.(jump_info) |}. 
    admit.
Admitted.

Lemma P_BBgen_nil: forall (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results),
    P_BBgen_range cmd_BB_gen nil.
Proof.
Admitted.

Lemma P_BBgen_con:
    forall (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results) (c: cmd) (cmds: list cmd),
    Q_BBgen_range c ->
    P_BBgen_range cmd_BB_gen cmds ->
    P_BBgen_range cmd_BB_gen (c::cmds).
Proof.
Admitted.


Section BB_gen_range_sound.

Variable cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results.
Variable BB_gen_range_soundness: forall (c: cmd), Q_BBgen_range c.

Fixpoint BBgen_list_range_soundness (cmds: list cmd): P_BBgen_range cmd_BB_gen cmds :=
  match cmds with
  | nil => P_BBgen_nil cmd_BB_gen
  | c :: cmds0 => P_BBgen_con cmd_BB_gen c cmds0 (BB_gen_range_soundness c) (BBgen_list_range_soundness cmds0)
  end.

End BB_gen_range_sound.

Fixpoint BB_gen_range_soundness (c: cmd): Q_BBgen_range c :=
  match c with
  | CAsgn x e => Q_asgn_BBgen_range x e
  | CIf e cmds1 cmds2 =>
      Q_if_BBgen_range e cmds1 cmds2
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds1)
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds2)
  | CWhile cmds1 e cmds2 =>
      Q_while_BBgen_range e cmds1 cmds2
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds1)
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds2)
  end.

Lemma BBgen_range_soundness_correct:
    forall (c: cmd),
     c.
Proof.
Admitted.








