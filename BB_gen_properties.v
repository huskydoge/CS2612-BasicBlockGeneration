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

(* Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.
Import BDenote. *)

(*
Then
    BB_num2 =
    (list_cmd_BB_gen cmd_BB_gen c1 (BBs ++ BBnow' :: nil) BB_then BB_num1).(next_block_num) /\
    BB_now_then.(cmd) = BB_then.(cmd) ++ BB_cmds_then /\
    BB_now_then.(block_num) = BB_then.(block_num) /\
    (list_cmd_BB_gen cmd_BB_gen c1 (BBs ++ BBnow' :: nil) BB_then BB_num1).(BasicBlocks) ++
    (list_cmd_BB_gen cmd_BB_gen c1 (BBs ++ BBnow' :: nil) BB_then BB_num1).(BBn) :: nil = 
    (BBs ++ BBnow' :: nil) ++ (BB_now_then :: nil) ++ BBs_then 

*)

(*
Else
     BB_num3 =
     (list_cmd_BB_gen cmd_BB_gen c2
        (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) BB_else
        BB_num2).(next_block_num) /\
     BB_now_else.(cmd) = BB_else.(cmd) ++ BB_cmds_else /\
     BB_now_else.(block_num) = BB_else.(block_num) /\
     (list_cmd_BB_gen cmd_BB_gen c2
        (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) BB_else
        BB_num2).(BasicBlocks) ++
     (list_cmd_BB_gen cmd_BB_gen c2
        (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) BB_else
        BB_num2).(BBn) :: nil =
     (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) ++
     (BB_now_else :: nil) ++ BBs_else
*)

(*
BBnow:
BB_next_num_to_asgn: BBthen的num
S BB_next_num_to_asgn: BBelse的num
SS BB_next_num_to_asgn: BBnext的num
SSS BB_next_num_to_asgn: 以BBthen为起点，下一个分配的num
*)

(* 
    - delta1 ∩ delta2 = ∅ ，一条大引理
    考虑BB1和BB2：
    - BBnum < BB_next_num_to_asgn -> BBnum < BBnum_set delta ，一条引理
    - Bnum_set delta ≥ BB_next_num_to_asgn 一条引理，下一个分配的num，一定小于等于新生成的BBs里所有的num
    - delta.(next_block_num) ⪧ BBnum_set delta 一条引理，而生成完毕后，现在分配到的那个num，一定大于刚刚生成的BBs里所有的num
    - BBnum < BBnum_set delta -> BBnum ∉ BBnum_set delta 一条引理
        于是有 BB1num < BBnum_set delta1 < delta1.(next_block_num) = BB_next_num_to_asgn2 ≤ BBnum_set delta2
        ->
        BB1num  ∉ BBnum_set delta2
    - 类似地证明， BB2num  ∉ BBnum_set delta1，但是方向是反一下
    - 再加上BB1num ≠ BB2 num ，到时候用的时候，这是已经有的条件，不需要引理
    那么 BBnum_set (BB1::delta1) ∩ BBnumset (BB2::delta2) = ∅
*)


(*BBnumset BBs >= num*)
Definition BB_all_ge (BBs: list BasicBlock)(num: nat): Prop :=
    forall BB, In BB BBs -> Nat.le num BB.(block_num).
(*BBnumset BBs < num*)
Definition BB_all_lt (BBs: list BasicBlock)(num: nat): Prop :=
    forall BB, In BB BBs -> Nat.lt BB.(block_num) num.



Definition P_BBgen_range (startnum endnum: nat)(cmds: list cmd)(BBnow: BasicBlock): Prop :=
    forall BBs,
    let res := (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow startnum) in
    let basicblocks := to_result res in
    endnum = res.(next_block_num)
    /\ 
    (
      exists BBnow' BBdelta,
      basicblocks = BBs ++ BBnow'::nil ++ BBdelta /\
      BB_all_ge BBdelta startnum /\
      BB_all_lt BBdelta endnum
    ).

Definition Q_BBgen_range (startnum endnum: nat)(c: cmd)(BBnow: BasicBlock): Prop :=
    forall BBs,
    let res := (cmd_BB_gen c BBs BBnow startnum) in
    let basicblocks := to_result res in
    endnum = res.(next_block_num)
    /\ 
    (
      exists BBnow' BBdelta,
      basicblocks = BBs ++ BBnow'::nil ++ BBdelta /\
      BB_all_ge BBdelta startnum /\
      BB_all_lt BBdelta endnum
    ).


Lemma P_BBgen_range_sound:
  forall  (cmds: list cmd) (BBnow: BasicBlock)(BBs: list BasicBlock)(startnum: nat),
    let res := (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow startnum) in
    let endnum := res.(next_block_num) in
    P_BBgen_range startnum endnum cmds BBnow.
Proof.
  Admitted.
  

Lemma Q_if_BBgen_range (BB_now BB_then BB_else: BasicBlock):
forall (e: expr) (c1 c2: list cmd) (BBnum: nat) (startnum midnum endnum: nat) (BBs: list BasicBlock),
    P_BBgen_range startnum midnum c1 BB_then ->
    P_BBgen_range midnum endnum c2 BB_else ->

    exists BB_delta,
    let basicblocks := to_result (cmd_BB_gen (CIf e c1 c2) BBs BB_now BBnum) in  (*BBn是BBnext*)
    basicblocks = BBs++ BB_now::nil ++ BB_delta /\
    BB_all_ge BB_delta BBnum /\ BB_all_lt BB_delta endnum.
Proof.
    Admitted.


  
Lemma Q_if_BBgen_disjoint (BB_then BB_else: BasicBlock):
forall (e: expr) (c1 c2: list cmd) (BBnum: nat) (startnum midnum endnum: nat) (BBs: list BasicBlock),
    P_BBgen_range startnum midnum c1 BB_then ->
    P_BBgen_range midnum endnum c2 BB_else ->

    exists BB_then' BB_then_delta BB_else' BB_else_delta,
    let then_basicblocks := to_result (list_cmd_BB_gen cmd_BB_gen c1 BBs BB_then startnum) in
    let else_basicblocks := to_result (list_cmd_BB_gen cmd_BB_gen c2 (BBs ++ BB_then'::nil ++ BB_then_delta) BB_else midnum) in
    then_basicblocks = BBs ++ BB_then'::nil ++ BB_then_delta /\
    else_basicblocks = (BBs ++ BB_then'::nil ++ BB_then_delta) ++ BB_else'::nil ++ BB_else_delta /\
    (*不交*)
    BBnum_set BB_then_delta ∩ BBnum_set BB_else_delta = ∅.
Proof.
    intros.
    unfold P_BBgen_range in *.
    specialize (H BBs).
    destruct H as [mid_prop H2].
    destruct H2 as [BB_then' [BB_then_delta [?]]].
    specialize (H0 (BBs ++ BB_then'::nil ++ BB_then_delta)).
    destruct H0 as [end_prop H4].
    destruct H4 as [BB_else' [BB_else_delta [?]]].
    rename H1 into then_delta_range.
    rename H2 into else_delta_range.
    exists BB_then', BB_then_delta, BB_else', BB_else_delta.
    repeat split.
    - apply H.
    - apply H0.
    - (* #TODO *)



