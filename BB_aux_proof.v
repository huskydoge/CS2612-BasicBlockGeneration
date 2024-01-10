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
Require Import Main.BB_gen_properties.
Require Import Nat.


Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.
Import BDenote.

Lemma never_go_wrong: 
   forall (e: EDenote) (s: state),
  (exists (i : int64), (e).(nrm) s i).
Proof.
Admitted.

Lemma true_or_false:
  forall (e: EDenote) (s: state),
  (test_true_jmp (e)) s \/ (test_false_jmp (e)) s.
Proof.
  intros. assert((exists (i : int64), (e).(nrm) s i)). pose proof never_go_wrong e s. tauto.
  destruct H.
  pose proof classic (Int64.signed x = 0).
  unfold test_true_jmp. unfold test_false_jmp.
  destruct H0.
  - right. rewrite <- H0. rewrite Int64.repr_signed. apply H.
  - left. exists x. split. apply H. apply H0.
Qed.

Lemma as_a_part_then_in:
  forall (A: Type) (a: A) (l1 l2: list A),
  l1 ++ a::nil = l2 -> In a l2.
Proof.
  intros A a l1 l2 H.
  rewrite <- H.
  apply in_app_iff.
  right. simpl. left. tauto.
Qed.
  

Ltac my_destruct H :=
  match type of H with 
  | exists _, _ => destruct H as [? H]; my_destruct H 
  | _ /\ _ => let H1:= fresh "H" in 
              destruct H as [H H1];my_destruct H; my_destruct H1
  | _ => idtac 
  end.

(*比较两个BBstate相等*)
Lemma compare_two_BB_state:
  forall (bs1 bs2: BB_state),
  bs1 = bs2 <-> 
  bs1.(BB_num) = bs2.(BB_num) /\ bs1.(st) = bs2.(st) .
Proof.
  intros.
  split.
  - intros. rewrite H. split; reflexivity.
  - intros. destruct H. destruct bs1, bs2. simpl in *.
    subst. reflexivity.
Qed.

(* used in Qd_if_sound *)
Lemma list_assoc : forall (A : Type) (xs ys zs : list A),
  (xs ++ ys) ++ zs = xs ++ ys ++ zs.
Proof.
  intros A xs ys zs.
  induction xs as [| x xs' IHxs'].
  - (* Base case: xs is empty *)
    simpl. reflexivity.
  - (* Inductive case: xs = x :: xs' *)
    simpl. rewrite IHxs'. reflexivity.
Qed.

Lemma compare_two_BasicBlock:
  forall (BB1 BB2: BasicBlock),
  BB1 = BB2 <-> 
  BB1.(block_num) = BB2.(block_num) /\ BB1.(commands) = BB2.(commands) /\ BB1.(jump_info) = BB2.(jump_info).
Proof.
  intros.
  split.
  - intros. 
    destruct BB1. destruct BB2.
    simpl. injection H. intros. repeat split. apply H2. apply H1. apply H0.
  - intros. destruct BB1. destruct BB2. simpl in H. destruct H as [? [? ?]]. rewrite H. rewrite H0. rewrite H1. tauto.
Qed.

Lemma compare_two_BBstate:
  forall (bs1 bs2: BB_state),
  bs1 = bs2 <->
  bs1.(BB_num) = bs2.(BB_num) /\ bs1.(st) = bs2.(st).
Proof.
  intros.
  split.
  - intros. rewrite H. split; reflexivity.
  - intros. destruct H. destruct bs1, bs2. simpl in *.
    subst. reflexivity.
Qed.

Lemma unfold_once:
  forall (BBs: list BasicBlock),
(BB_list_sem BBs).(Bnrm) == Rels.id ∪ (BB_sem_union BBs).(Bnrm) ∘ (BB_list_sem BBs).(Bnrm).
Proof.
  intros. apply Sets_equiv_Sets_included.
  split.
  + intros.
    unfold BB_list_sem. simpl.
    apply Sets_indexed_union_included.
    destruct n. 
    - left. tauto.
    - sets_unfold. intros. right.
      unfold Iter_nrm_BBs_n in H. destruct H as [? ?]. sets_unfold in H.
      destruct H as [? ?].
      exists x. split; try tauto.
      exists n. unfold Iter_nrm_BBs_n. apply H0.

  + apply Sets_union_included.
    - unfold BB_list_sem. simpl.
      assert(Rels.id = Iter_nrm_BBs_n (BB_sem_union BBs) 0).
      -- tauto.
      -- rewrite H. simpl. sets_unfold. intros. exists O. rewrite H0. rewrite <- H. sets_unfold. tauto.
    - unfold BB_list_sem. simpl.
      sets_unfold. intros.
      destruct H as [? [? [? ?]]].
      exists (S x0). unfold Iter_nrm_BBs_n. sets_unfold.
      exists x.
      split. apply H.
      unfold Iter_nrm_BBs_n in H0. apply H0.
Qed.

Definition BDenote_concate (BD1: BDenote) (BD2: BDenote): BDenote := {|
  Bnrm := BD1.(Bnrm) ∘ BD2.(Bnrm);
  Berr := BD1.(Berr) ∪ BD1.(Bnrm) ∘ BD2.(Berr);
  Binf := ∅;
|}.



(* Some Important Property for S ========================================================================================================
  假如(S1 U ... U Sn)* (BBnum_start, s1) (BBnum_end, s2)

  缺少还有一个分离的性质

  但是所有S的分项当中只有S1能够从 BBnum_start出发, 也就是说，对于i >= 2都有， (S2 U ... U Sn)  (BBnum_start, s) (_, s') -> False

  那么(S1 U ... U Sn)* (BBnum_start, s1) (BBnum_end, s2) -> exists BBnum s1', S1 (BBnum_start, s1) (BBnum s1') /\ (S2 U ... U Sn) (BBnum s1') (BBnum_end, s2)
  
  S1 (BBnum_start, s1) (BBnum s1') 这个就是有cjump的那一步啊
*)

Definition separate_property (BB1: BasicBlock) (BBs: list BasicBlock) : Prop := 
  BBnum_set (BB1 :: nil) ∩ BBjmp_dest_set (BB1 :: BBs) == ∅.

Definition BB_restrict (BB1: BasicBlock)(BBs: list BasicBlock)(start_BB: nat)(end_BB: nat): Prop :=
  start_BB = BB1.(block_num) /\ BBjmp_dest_set BBs end_BB /\ ((BBnum_set (BB1::nil) ∩ BBnum_set (BBs)) == ∅).
(* ==================================================================================================================================== *)

(* Some Important Property for S ========================================================================================================
  假如(S1 U ... U Sn)* (BBnum_start, s1) (BBnum_end, s2)

  缺少还有一个分离的性质

  但是所有S的分项当中只有S1能够从 BBnum_start出发, 也就是说，对于i >= 2都有， (S2 U ... U Sn)  (BBnum_start, s) (_, s') -> False

  那么(S1 U ... U Sn)* (BBnum_start, s1) (BBnum_end, s2) -> exists BBnum s1', S1 (BBnum_start, s1) (BBnum s1') /\ (S2 U ... U Sn) (BBnum s1') (BBnum_end, s2)
  
  S1 (BBnum_start, s1) (BBnum s1') 这个就是有cjump的那一步啊

*)

(*对于空的BBslist，若(bs1, bs2)在其中，则bs1 = bs2*)
Lemma nil_sem:
  forall (bs1 bs2: BB_state),
  Bnrm (BB_list_sem nil) bs1 bs2 -> bs1 = bs2.
Proof.
  intros. unfold BB_list_sem in H. unfold BB_sem_union in H. 
  assert(forall (n: nat), n<>O ->Iter_nrm_BBs_n({| Bnrm := ∅; Berr := ∅; Binf := ∅ |})(n) == ∅).
{
  induction n.
  - simpl. tauto.
  - intros. cbn[Iter_nrm_BBs_n]. simpl. sets_unfold. intros. split. intros. my_destruct H1. tauto. tauto. 
}
  assert(⋃ (Iter_nrm_BBs_n {| Bnrm := ∅; Berr := ∅; Binf := ∅ |}) == Rels.id).
{
   sets_unfold. intros. split.
  - intros. destruct H1. induction x.  simpl in H1. tauto. assert((S x)<>O). lia. pose proof H0 (S x) H2. sets_unfold in H3. 
    assert(forall a a0 : BB_state,
     Iter_nrm_BBs_n
       {|
       Bnrm := fun _ _ : BB_state => False;
       Berr := fun _ : BB_state => False;
       Binf := fun _ : BB_state => False |} (S x) a a0 -> False).  apply H3.  pose proof H4 a a0 H1. tauto.
  - intros. exists O. simpl. tauto.
} 
  sets_unfold in H1. simpl in H. apply H1 in H. tauto.
Qed.



(*如果:
1. (bs1, bs2)属于BBnow的跳转语义
2. BBnow是无条件跳转，没有jumpdest2
那么bs2的num不等于BBnow, 且BBnow不会跳转到自身*)
Lemma Jump_restrict:
  forall (BBnow: BasicBlock)(bs1 bs2: BB_state),
  Bnrm (BJump_sem BBnow.(block_num) (jump_dest_1 BBnow.(jump_info))
     (jump_dest_2 BBnow.(jump_info))
     (eval_cond_expr (jump_condition BBnow.(jump_info)))) bs1 bs2 ->
  jump_dest_2 BBnow.(jump_info) = None ->
  BBnow.(block_num) <> bs2.(BB_num) /\
  BBnum_set
  ({|
     block_num := BBnow.(block_num);
     commands := nil;
     jump_info := BBnow.(jump_info)
   |} :: nil)
  ∩ 
  BBjmp_dest_set
    ({|
       block_num := BBnow.(block_num);
       commands := nil;
       jump_info := BBnow.(jump_info)
     |} :: nil) == ∅.
Proof.
  intros. 
  unfold BJump_sem in H.
  rename H0 into none_jmp_dest2. 
  destruct (eval_cond_expr (jump_condition BBnow.(jump_info))) eqn:?.
  - destruct (jump_dest_2 BBnow.(jump_info)) eqn:? in H. 
    + rewrite none_jmp_dest2 in Heqo0. discriminate Heqo0.
    + unfold ujmp_sem in H. cbn[Bnrm] in H. my_destruct H.
      split.
      * rewrite H0 in H2. tauto.
      * sets_unfold. intros. split.
        ** intros. destruct H3 as [cond1 cond2].
          unfold BBnum_set in cond1. simpl in cond1. destruct cond1 as [BB1 [cond11 cond12]].
          unfold BBjmp_dest_set in cond2. simpl in cond2. destruct cond2 as [BB2 [cond21 cond22]].
          destruct cond11. 
          -- destruct cond21.
            --- rewrite <- H3 in cond12. simpl in cond12. 
                rewrite <- H4 in cond22. simpl in cond22.
                destruct cond22 as [case1 | case2].
                *** rewrite case1 in H1. rewrite H1 in H2. rewrite cond12 in H0. rewrite H0 in H2. tauto.
                *** rewrite case2 in Heqo0. discriminate Heqo0.
            ---tauto.
          -- destruct cond21. tauto. tauto.
        ** intros. tauto.
  - unfold ujmp_sem in H. cbn [Bnrm] in H. my_destruct H. split.
    + rewrite H0 in H2. tauto.
    + 
      sets_unfold. intros. split.
      ** intros. destruct H3 as [cond1 cond2].
        unfold BBnum_set in cond1. simpl in cond1. destruct cond1 as [BB1 [cond11 cond12]].
        unfold BBjmp_dest_set in cond2. simpl in cond2. destruct cond2 as [BB2 [cond21 cond22]].
        destruct cond11. 
        -- destruct cond21.
          --- rewrite <- H3 in cond12. simpl in cond12. 
              rewrite <- H4 in cond22. simpl in cond22.
              destruct cond22 as [case1 | case2].
              *** rewrite case1 in H1. rewrite H1 in H2. rewrite cond12 in H0. rewrite H0 in H2. tauto.
              *** rewrite case2 in none_jmp_dest2. discriminate none_jmp_dest2.
          ---tauto.
        -- destruct cond21. tauto. tauto.
      ** intros. tauto.
Qed.


Lemma BBs_sem_union_exists_BB_bs1_bs2:
  forall (BBs: list BasicBlock) (bs1 bs2: BB_state),
    Bnrm (BB_sem_union BBs) bs1 bs2 -> (exists (BB: BasicBlock), In BB BBs /\ Bnrm (BB_sem BB) bs1 bs2).
Proof.
  intros. induction BBs.
  - unfold BB_sem_union in H. simpl in H. tauto.
  - unfold BB_sem_union in H. cbn[Bnrm] in H. sets_unfold in H.
    destruct H as [? | ?].
    + exists a. intros. split. unfold In. left. tauto. apply H.
    + pose proof IHBBs H. destruct H0 as [? [? ?]]. exists x.
      split. unfold In. right. apply H0. apply H1.
Qed. 

Lemma BBs_sem_union_exists_BB_bs1_bs2_inv:
  forall (BBs: list BasicBlock) (bs1 bs2: BB_state),
    (exists (BB: BasicBlock), In BB BBs /\ Bnrm (BB_sem BB) bs1 bs2) -> Bnrm (BB_sem_union BBs) bs1 bs2.
Proof.
  intros. destruct H as [? [? ?]].
  unfold BB_sem_union. induction BBs.
  - unfold In in H. tauto.
  - cbn[Bnrm]. sets_unfold. unfold In in H. destruct H as [? | ?].
    + left. rewrite <- H in H0. apply H0.
    + right. apply IHBBs. apply H.
Qed. 


Lemma BBs_list_sem_exists_BB_bs1_x:
  forall (BBs: list BasicBlock) (bs1 bs2: BB_state),
    Bnrm (BB_list_sem BBs) bs1 bs2 -> (exists (BB: BasicBlock) (x: BB_state), In BB BBs /\ Bnrm (BB_sem BB) bs1 x /\ Bnrm (BB_list_sem BBs) x bs2) \/ bs1 = bs2.
Proof.
  intros. unfold BB_list_sem in H. cbn[Bnrm] in H. 
  unfold Iter_nrm_BBs_n in H. sets_unfold in H. 
  destruct H as [? ?]. revert bs1 H. induction x; intros.
  - right. tauto. 
  - destruct H as [? [? ?]].
    pose proof BBs_sem_union_exists_BB_bs1_bs2 BBs bs1 x0 H.
    destruct H1 as [? [? ?]]. left.
    exists x1. exists x0. repeat split.
    apply H1. apply H2. unfold BB_list_sem. cbn[Bnrm].
    sets_unfold. exists x. apply H0.
Qed.


Lemma Iter_nrm_BBs_n_inv_expansion:
  forall (BBs: list BasicBlock) (bs1 bs2: BB_state) (a: nat),
    Iter_nrm_BBs_n (BB_sem_union BBs) (S a) bs1 bs2 ->
    exists i, Iter_nrm_BBs_n (BB_sem_union BBs) a bs1 i /\ Bnrm (BB_sem_union BBs) i bs2.
Proof.
  intros. simpl in H. sets_unfold in H.
  (*TODO*)
Admitted.


Lemma BBs_list_sem_exists_BB_bs1_x_tl:
  forall (BBs: list BasicBlock) (bs1 bs2: BB_state),
    Bnrm (BB_list_sem BBs) bs1 bs2 -> (exists (BB: BasicBlock) (x: BB_state), In BB BBs /\ Bnrm (BB_list_sem BBs) bs1 x /\ Bnrm (BB_sem BB) x bs2) \/ bs1 = bs2.
Proof.
  intros. unfold BB_list_sem in H. cbn[Bnrm] in H. 
  unfold Iter_nrm_BBs_n in H. sets_unfold in H. 
  destruct H as [? ?]. revert bs1 H. induction x; intros.
  - right. tauto. 
  - pose proof Iter_nrm_BBs_n_inv_expansion BBs bs1 bs2 x H.
    destruct H0 as [? [? ?]]. 
    pose proof BBs_sem_union_exists_BB_bs1_bs2 BBs x0 bs2 H1. left. 
    destruct H2 as [? [? ?]]. exists x1. exists x0. repeat split.
    apply H2. unfold BB_list_sem. cbn[Bnrm]. sets_unfold. exists x. apply H0.
    apply H3.
Qed.

     

(*如果BBs1是BBs2的子集，那么语义上也是*)
Lemma BB_sem_child_prop:
  forall (BBs1 BBs2 : list BasicBlock) (bs1 bs2 : BB_state),
    (forall (bb : BasicBlock), In bb BBs1 -> In bb BBs2) ->
    Bnrm (BB_sem_union BBs1) bs1 bs2 -> Bnrm (BB_sem_union BBs2) bs1 bs2.
Proof.
  intros. 
  pose proof BBs_sem_union_exists_BB_bs1_bs2 BBs1 bs1 bs2 H0.
  destruct H1 as [? [? ?]].
  pose proof BBs_sem_union_exists_BB_bs1_bs2_inv BBs2 bs1 bs2. apply H3.
  exists x. split.
  - specialize (H x). apply H. apply H1.
  - apply H2. 
Qed.


(*如果BBs1是BBs2的子集，那么任意多步的语义上也是*)
Lemma BB_list_sem_child_prop:
  forall (BBs1 BBs2 : list BasicBlock) (bs1 bs2 : BB_state),
      (forall (bb : BasicBlock), In bb BBs1 -> In bb BBs2) ->
      Bnrm (BB_list_sem BBs1) bs1 bs2 -> Bnrm (BB_list_sem BBs2) bs1 bs2.
Proof.
  intros. revert H0. unfold BB_list_sem. simpl. sets_unfold.
  intros. destruct H0. exists x. 
  assert(forall (n: nat), Iter_nrm_BBs_n (BB_sem_union BBs1) n ⊆ Iter_nrm_BBs_n (BB_sem_union BBs2) n).
  {
    intros. induction n. simpl. sets_unfold. tauto.
    cbn[Iter_nrm_BBs_n] . sets_unfold. intros. my_destruct H1.
    exists x0. split. pose proof BB_sem_child_prop BBs1 BBs2 a x0. tauto. sets_unfold in IHn.
    pose proof IHn x0 a0 H2. tauto.
  }
  pose proof H1 x.
  sets_unfold in H2.
  pose proof H2 bs1 bs2 H0. tauto.
Qed.



(* Important !*)

(* 针对state的start和end的性质 *)
Lemma sem_start_end_with_st:
  forall (sem1 sem2: state -> state -> Prop)(bs1 bs2: state),
  ((sem1 ∘ sem2) bs1 bs2 :Prop) -> (exists bs', (sem1 bs1 bs') /\ (sem2 bs' bs2)).
Proof.
  intros.
  sets_unfold in H.
  destruct H as [? [? ?]]. 
  exists x.
  split. apply H. apply H0.
  Qed.

(* 针对BBstate的start和end的性质 *)
Lemma sem_start_end_with:
  forall (sem1 sem2: BB_state -> BB_state -> Prop)(bs1 bs2: BB_state),
  ((sem1 ∘ sem2) bs1 bs2 :Prop) -> (exists bs', (sem1 bs1 bs') /\ (sem2 bs' bs2)).
Proof.
  intros.
  sets_unfold in H.
  destruct H as [? [? ?]]. 
  exists x.
  split. apply H. apply H0.
  Qed.

Lemma sem_start_end_with_2:
  forall (sem1 sem2: BB_state -> BB_state -> Prop)(bs1 bs2: BB_state),
  (exists bs', (sem1 bs1 bs') /\ (sem2 bs' bs2)) -> ((sem1 ∘ sem2) bs1 bs2 :Prop).
Proof.
  intros.
  sets_unfold.
  destruct H.
  exists x.
  apply H.
Qed.

(*处理完BB中的cmds之后，不会改变BBnum*)
(* ! bs2 bs1的顺序是反的 *)
Lemma BB_cmds_sem_no_change_num:
  forall (BB: BasicBlock) (bs2 bs1: BB_state),
  (BB_cmds_sem BB).(Bnrm) bs1 bs2 -> bs1.(BB_num) = bs2.(BB_num).
Proof.
  intros BB bs2.
  unfold BB_cmds_sem. simpl.
  induction BB.(cmd); intros.
  - simpl in H. sets_unfold in H. destruct bs1, bs2.
    simpl. injection H. intros. apply H1.
  - unfold BAsgn_list_sem in H. cbn[Bnrm] in H.
    sets_unfold in H. destruct H as [? [? ?]].
    pose proof IHl x. unfold BAsgn_list_sem in H1. apply H1 in H0.
    unfold BAsgn_denote in H. simpl in H.
    destruct H as [[? [? [? ?]]] ?].
    rewrite H4. apply H0.
Qed.
    (* sets_unfold in IHl.  *)

(* 处理完BBnow的jmp后，跳转到的BB的num在jmpdest BBnow 中 *)
Lemma BB_jmp_sem_num_in_BBjmp_dest_set:
  forall (BB: BasicBlock) (bs1 bs2: BB_state),
  (BB_jmp_sem BB).(Bnrm) bs1 bs2 -> bs2.(BB_num) ∈ BBjmp_dest_set (BB :: nil).
Proof.
  intros.
  unfold BBjmp_dest_set. unfold In. simpl. exists BB. split.
  + left. tauto.
  + unfold BB_jmp_sem in H. simpl in H. destruct eval_cond_expr.
    unfold BJump_sem in H. destruct jump_dest_2.
    - unfold cjmp_sem in H. simpl in H. my_destruct H. 
      destruct H2.
      ++ left. destruct H2. rewrite H2. reflexivity.
      ++ right. destruct H2. rewrite H2. reflexivity.
    - unfold ujmp_sem in H. simpl in H. my_destruct H.
      left. rewrite H1. reflexivity.
    - unfold BJump_sem in H. unfold ujmp_sem in H. simpl in H. my_destruct H.
      left. rewrite H1. reflexivity.
Qed.



Lemma iter_concate:
  forall (sem1 sem2: BB_state -> BB_state -> Prop) (bs1 bs2 bs3 :BB_state),
  ((sem1) bs1 bs2 :Prop) -> ((sem2) bs2 bs3 :Prop) -> ((sem1 ∘ sem2) bs1 bs3 :Prop).
Proof.
  intros.
  sets_unfold. exists bs2. split. apply H. apply H0.
Qed.


(* 前提中只用BB_restrict的前半部分 *)
Lemma BB_sem_num_change:
  forall (bs1 bs2: BB_state) (BBnow: BasicBlock) (BBs: list BasicBlock),
  separate_property BBnow BBs -> BB_num bs1 = BBnow.(block_num) -> Bnrm (BB_sem BBnow) bs1 bs2 -> bs1.(BB_num) <> bs2.(BB_num).
Proof.
  intros ? ? ? ? H H0 H1.
  unfold BB_sem in H1. simpl in H1.
  sets_unfold in H1.
  destruct H1 as [? [H1 H3]].
  (* ! x bs1 表示 bs1 -> x *)
  pose proof BB_cmds_sem_no_change_num BBnow x bs1 as H4.
  unfold BB_cmds_sem in H4. simpl in H4. apply H4 in H1.
  unfold separate_property in H.
  unfold BBnum_set in H. sets_unfold in H.
  specialize (H x.(BB_num)). destruct H as [? ?]. clear H2.
  unfold BJump_sem in H3. 
  destruct eval_cond_expr in H3. destruct jump_dest_2 in H3.
  - unfold cjmp_sem in H3. simpl in H3. destruct H3 as [[? [? ?]] ?].
    destruct H5 as [[? ?] | [? ?]]. 
    + rewrite H1. apply H6.
    + rewrite <- H0 in H3. rewrite H3 in H6. apply H6.
  - unfold ujmp_sem in H3. simpl in H3. destruct H3 as [? [? [? ?]]].
    rewrite <- H0 in H3. rewrite H3 in H6. apply H6.
  - unfold ujmp_sem in H3. simpl in H3. destruct H3 as [? [? [? ?]]]. rewrite <- H0 in H3. rewrite H3 in H6. apply H6. 
Qed.


Lemma BB_sem_start_BB_num:
  forall (bs1 bs2 : BB_state) (BBnow : BasicBlock),
  Bnrm (BB_sem BBnow) bs1 bs2 -> bs1.(BB_num) = BBnow.(block_num).
Proof.
  intros.
  unfold BB_sem in H. simpl in H.
  sets_unfold in H.
  destruct H as [? [? ?]].
  pose proof BB_cmds_sem_no_change_num BBnow x bs1.
  apply H1 in H. rewrite H.
  unfold BJump_sem in H0. destruct eval_cond_expr. destruct jump_dest_2.
  + unfold cjmp_sem in H0. simpl in H0. destruct H0 as [[? [? ?]] ?]. apply H2.
  + unfold ujmp_sem in H0. simpl in H0. destruct H0 as [? [? ?]]. apply H2.
  + unfold ujmp_sem in H0. simpl in H0. destruct H0 as [? [? ?]]. apply H2.
Qed.

(*
证明一个 (P -> Q) -> (~Q -> ~P)的引理
*)
Lemma sets_reverse:
  forall (P Q: Prop),
  (P -> Q) -> (~Q -> ~P) .
Proof.
  intros.
  unfold not. intros.
  apply H0. apply H. apply H1.
Qed.

(*证明，如果能正确执行跳转语义，那么bs1的num一定要是BBnow的blocknum*)
Lemma BB_jmp_sem_property_for_bs1:
  forall (BBnow: BasicBlock) (bs1 bs2: BB_state),
  Bnrm (BB_jmp_sem BBnow) bs1 bs2 -> BBnow.(block_num) = BB_num bs1.
Proof.
  intros.
  unfold BB_jmp_sem in H. cbn [Bnrm] in H.
  unfold BJump_sem in H. destruct eval_cond_expr.
  + destruct jump_dest_2.
    - unfold cjmp_sem in H. cbn [Bnrm] in H. destruct H as [[? [? ?]] ?].
      rewrite H0. reflexivity.
    - unfold ujmp_sem in H. cbn [Bnrm] in H. destruct H as [? [? [? ?]]].
      rewrite H0. reflexivity. 
  + unfold ujmp_sem in H. cbn [Bnrm] in H. destruct H as [? [? [? ?]]].
    rewrite H0. reflexivity.
Qed.

(*BBsem一步，bs1 bs2，bs1满足的性质*)
Lemma single_step_jmp_property_for_bs1:
  forall (BBnow: BasicBlock) (bs1 bs2: BB_state),
  Bnrm (BB_sem BBnow) bs1 bs2 -> BBnow.(block_num) = BB_num bs1.
Proof.
  intros.
  unfold BB_sem in H. cbn [Bnrm] in H.
  sets_unfold in H.
  destruct H as [? [? ?]].
  pose proof BB_cmds_sem_no_change_num BBnow x bs1.
  pose proof BB_jmp_sem_property_for_bs1 BBnow x bs2.
  pose proof (H2 H0).
  pose proof (H1 H).
  rewrite H3. rewrite H4. reflexivity.
Qed.

(*BBsem一步，bs1 bs2，bs2满足的性质*)
Lemma single_step_jmp_property_for_bs2:
  forall (BBnow: BasicBlock) (bs1 bs2: BB_state),
  Bnrm (BB_sem BBnow) bs1 bs2 -> (jump_dest_1 BBnow.(jump_info) = BB_num bs2 \/
  jump_dest_2 BBnow.(jump_info) = Some (BB_num bs2)).
Proof.
  intros.
  unfold BB_sem in H. cbn [Bnrm] in H.
  sets_unfold in H.
  destruct H as [? [? ?]]. clear H.
  unfold BB_jmp_sem in H0. cbn [Bnrm] in H0.
  unfold BJump_sem in H0. destruct (eval_cond_expr (jump_condition BBnow.(jump_info))).
  - destruct (jump_dest_2 BBnow.(jump_info)).
    + unfold cjmp_sem in H0. cbn [Bnrm] in H0. destruct H0 as [[? [? ?]] ?].
      destruct H1 as [[? ?] | [? ?]].
      ++ rewrite H1. left. tauto.
      ++ rewrite H1. right. tauto.
    + unfold ujmp_sem in H0. cbn [Bnrm] in H0. destruct H0 as [? [? [? ?]]].
      rewrite H1. left. tauto.
  - left. unfold ujmp_sem in H0. cbn [Bnrm] in H0. destruct H0 as [? [? [? ?]]]. rewrite H1. reflexivity.
Qed.



(*从一个bs出发，经过任意一个block的语义，得到的新的bs都不和原来的相等*)
Lemma different_bs_after_single_BBsem:
  forall (a: BasicBlock) (bs: BB_state), Bnrm (BB_sem a) bs bs -> False.
Proof.
  intros.
  unfold BB_sem in H. cbn [Bnrm] in H.
  sets_unfold in H.
  destruct H as [? [? ?]].
  pose proof (BB_cmds_sem_no_change_num a x bs H).
  unfold BB_jmp_sem in H0. cbn [Bnrm] in H0.
  unfold BJump_sem in H0. destruct (eval_cond_expr (jump_condition a.(jump_info))).
  + destruct (jump_dest_2 a.(jump_info)).
    - unfold cjmp_sem in H0. cbn [Bnrm] in H0. destruct H0 as [[? [? ?]] ?].
      unfold not in H4. rewrite H1 in H4. apply H4. reflexivity.
    - unfold ujmp_sem in H0. cbn [Bnrm] in H0. destruct H0 as [? [? [? ?]]]. 
      rewrite H1 in H4.
      unfold not in H4. apply H4. reflexivity.
  + unfold ujmp_sem in H0. cbn [Bnrm] in H0. destruct H0 as [? [? [? ?]]].
    rewrite H1 in H4. tauto.
Qed.

(*从一个bs出发，经过任意一一串block的并的语义，得到的新的bs都不和原来的相等*)
Lemma different_bs_after_BBsem_union:
  forall (a: BasicBlock) (tl: list BasicBlock) (bs: BB_state), Bnrm (BB_sem_union (a::tl)) bs bs -> False.
Proof.
  intros.
  unfold BB_sem_union in H. cbn [Bnrm] in H.
  sets_unfold in H.
  destruct H as [?|?].
  - apply different_bs_after_single_BBsem in H. tauto.
  - unfold BB_sem_union in H. cbn [Bnrm] in H.
    induction tl.
    ++ cbn [Bnrm] in H. tauto.
    ++ destruct H.
      * apply different_bs_after_single_BBsem in H. tauto.
      * apply IHtl in H. tauto.
Qed.


(* BUG Not Used*)
Lemma BBs_sem_num_not_BB_sem_num:
forall (bs1 bs2 bs3: BB_state) (BBnow: BasicBlock) (BBs: list BasicBlock),
  (BBs <> nil) -> separate_property BBnow BBs -> BB_num bs1 = BBnow.(block_num) -> Bnrm (BB_sem_union (nil ++ BBs)) bs2 bs3 -> (bs2 <> bs3) -> BB_num bs3 <> BB_num bs1.
Proof.
  intros.
  unfold separate_property in H. 

  assert ((BB_num bs1) ∈ BBnum_set (BBnow :: nil)). {
    unfold BBnum_set. sets_unfold.
    unfold BB_restrict in H0.
    exists BBnow.
    split.
    + unfold In. left. tauto. 
    + rewrite H1. tauto.
  }

  assert ((BB_num bs3) ∈ BBjmp_dest_set (BBnow :: BBs)). {
    sets_unfold. unfold BBjmp_dest_set.
    unfold BB_sem_union in H2.
    induction BBs.
    - tauto.
    - unfold separate_property in H0. 
    assert (BBnum_set (BBnow :: nil) ∩ BBjmp_dest_set (BBnow :: BBs) == ∅).
    { 
    pose proof Sets_complement_fact (BBnum_set (BBnow :: nil)) (BBjmp_dest_set (BBnow :: a :: BBs)).
    destruct H5. pose proof (H6 H0). clear H6.
    pose proof Sets_complement_fact (BBnum_set (BBnow :: nil)) (BBjmp_dest_set (BBnow :: BBs)).
    destruct H6. clear H8. 
    assert (Sets.complement (BBjmp_dest_set (BBnow :: a :: BBs)) ⊆ Sets.complement (BBjmp_dest_set (BBnow :: BBs))).
    {
      unfold BBjmp_dest_set. simpl. sets_unfold. intros. 
      assert (
      ((exists BB : BasicBlock,
      (BBnow = BB \/ In BB BBs) /\
      (jump_dest_1 BB.(jump_info) = a0 \/ jump_dest_2 BB.(jump_info) = Some a0)))
      ->
      (     
      (exists BB : BasicBlock,
      (BBnow = BB \/ a = BB \/ In BB BBs) /\
      (jump_dest_1 BB.(jump_info) = a0 \/ jump_dest_2 BB.(jump_info) = Some a0)))
      ).
      {
        intros. destruct H9 as [? [? ?]]. exists x. split.
        - destruct H9.
          + left. tauto.
          + right. right. tauto.
        - tauto.
      }
      pose proof (
      sets_reverse 
      ((exists BB : BasicBlock,
      (BBnow = BB \/ In BB BBs) /\
      (jump_dest_1 BB.(jump_info) = a0 \/ jump_dest_2 BB.(jump_info) = Some a0))) 
         
      (exists BB : BasicBlock,
      (BBnow = BB \/ a = BB \/ In BB BBs) /\
      (jump_dest_1 BB.(jump_info) = a0 \/ jump_dest_2 BB.(jump_info) = Some a0))
      
      ).
      pose proof (H10 H9). pose proof (H11 H8). apply H12.
    }
    assert (BBnum_set (BBnow :: nil) ⊆ Sets.complement (BBjmp_dest_set (BBnow :: BBs))). {
      transitivity (Sets.complement (BBjmp_dest_set (BBnow :: a :: BBs))). 
      - apply H7.
      - apply H8.
    }
    pose proof (H6 H9).
    apply H10.
    }
    destruct H2.
    -- exists a.
        split.
        ++ unfold In. right. tauto.
        ++ apply single_step_jmp_property_for_bs2 in H2. tauto.
    -- destruct BBs.
      + simpl in H2. sets_unfold in H2. tauto.
      + assert (b :: BBs <> nil). {
          unfold not. intros. discriminate.
        }
        unfold separate_property in IHBBs.
        pose proof (IHBBs H6 H5 H2). destruct H7. exists x. destruct H7. split.
        --- unfold In. unfold In in H7. destruct H7.  
          +++ left. tauto.
          +++ destruct H7.
            * right. right. left. tauto.
            * right. right. tauto.
        --- apply H8.
  }
  unfold separate_property in H0.
  intros contra.
  rewrite <- contra in H4.
  assert (BB_num bs3 ∈ BBnum_set (BBnow :: nil) ∩ BBjmp_dest_set (BBnow :: BBs)). {
    sets_unfold. split.
    sets_unfold in H3. sets_unfold in H4.
    - apply H4.
    - apply H5.
  }
  sets_unfold in H5. sets_unfold in H4. sets_unfold in H0.
  specialize (H0 (BB_num bs3)). 
  assert (BBnum_set (BBnow :: nil) (BB_num bs3) /\ BBjmp_dest_set (BBnow :: BBs) (BB_num bs3)). {
    split. apply H4. apply H5.
  }
  apply H0 in H6. tauto.
Qed.

(* 不考虑出错和inf的情况*)
Lemma No_err_and_inf_for_expr:
  forall (e: expr) (bs: BB_state),
  (exists i : int64, EDenote.nrm (eval_expr e) (st bs) i).
Admitted.

(*如果bs1的num不在BBs的num中，那bs1不能作为BBs单步语义的起点！*)
Lemma cannot_start_with:
  forall (bs1 bs2: BB_state)(BBs: list BasicBlock),
  ~ (BBnum_set BBs (BB_num bs1)) -> (BB_sem_union (BBs)).(Bnrm) bs1 bs2 -> False.
Proof.
  intros.
  unfold BBnum_set, not in H. apply H.
  unfold BB_sem_union in H0.
  destruct BBs.
  - simpl in H0. sets_unfold in H0. tauto.
  - clear H. simpl. cbn[Bnrm] in H0. destruct H0.
    pose proof BB_sem_start_BB_num bs1 bs2 b H. 
    + exists b. split. left. tauto. rewrite H0. tauto.
    + induction BBs.
      * simpl in H.  tauto.
      * destruct H.
        -- exists a. split.
          +++ right. unfold In. left. tauto.
          +++ pose proof single_step_jmp_property_for_bs1 a bs1 bs2 H. rewrite H0. tauto.
        -- pose proof (IHBBs H). destruct H0. exists x. destruct H0. split; destruct H0.
          +++ left. tauto.
          +++ right. unfold In. right. tauto.
          +++ rewrite H1. tauto.
          +++ rewrite H1. tauto.
Qed.

(* convert indexed union into one union *)
Lemma indexed_sem_exist_n:
  forall (BD: BDenote)(bs1 bs2 : BB_state),
  ⋃ (Iter_nrm_BBs_n  BD) bs1 bs2 <-> exists n : nat, Iter_nrm_BBs_n BD n bs1 bs2.
Proof.
  intros. split.
  - tauto.
  - tauto.
Qed.  


Lemma BBs_sem_union_jmp_dest:
  forall (bs1 bs2: BB_state) (BBs: list BasicBlock),
    Bnrm (BB_sem_union BBs) bs1 bs2 -> BBjmp_dest_set BBs bs2.(BB_num).
Proof.
  intros. 
  pose proof BBs_sem_union_exists_BB_bs1_bs2 BBs bs1 bs2 H.
  destruct H0 as [? [? ?]].
  unfold BB_sem in H1. cbn[Bnrm] in H1. sets_unfold in H1. destruct H1 as [? [? ?]].
  pose proof BB_jmp_sem_num_in_BBjmp_dest_set x x0 bs2 H2.
  sets_unfold in H3. unfold BBjmp_dest_set. exists x. repeat split.
  - apply H0.
  - unfold BBjmp_dest_set in H3. destruct H3 as [? [? ?]].
    assert (x1 = x). {
      unfold In in H3. destruct H3 as [? | ?].
      rewrite H3. tauto. tauto.
    }
    rewrite H5 in H4. apply H4.
Qed.


Lemma Iter_n_simplify:
  forall (n: nat) (BBnow: BasicBlock) (BBs: list BasicBlock)(bs2: BB_state), 
  BBnum_set (BBnow :: nil) ∩ BBjmp_dest_set (BBnow :: BBs) == ∅ ->
  forall (x: BB_state), ~BBnum_set (BBnow :: nil) (BB_num x) -> 
   Iter_nrm_BBs_n (BB_sem_union (BBnow :: nil ++ BBs)) n x bs2 -> Iter_nrm_BBs_n (BB_sem_union BBs) n x bs2.
Proof.
  intros n BBnow BBs bs2.
  induction n.
  - intros. simpl in H0. simpl. tauto.
  - intros. specialize (IHn H). cbn[Iter_nrm_BBs_n] in H1.
    pose proof sem_start_end_with (Bnrm (BB_sem_union (BBnow :: nil ++ BBs)))  (Iter_nrm_BBs_n (BB_sem_union (BBnow :: nil ++ BBs)) n) x bs2 H1.
    my_destruct H2. clear H1.
    assert(~ BBnum_set (BBnow :: nil) (BB_num x0)). (* use BBnum x0 in BBjmp_dest(BBnow :: BBs), and you can get it in H2 *)
    {
      pose proof BBs_sem_union_exists_BB_bs1_bs2 (BBnow::nil ++ BBs) x x0 H2.
      destruct H1 as [? [? ?]]. unfold not. intros.
      unfold In in H1. destruct H1 as [? | ?].
      + rewrite <- H1 in H4. pose proof BB_sem_start_BB_num x x0 BBnow H4.
        unfold not in H0. apply H0. unfold BBnum_set. exists BBnow. split. 
        unfold In. left. tauto. rewrite H6. tauto.
      + assert (BB_num x0 = BBnow.(block_num)).
        unfold BBnum_set in H5. my_destruct H5. unfold In in H5. destruct H5 as [? | ?].
        rewrite <- H5 in H6. rewrite H6. tauto. tauto.
        pose proof BBs_sem_union_jmp_dest x x0 (BBnow::BBs) H2.
        sets_unfold in H. specialize (H (BB_num x0)). destruct H as [? ?]. clear H8.
        apply H. split. apply H5. apply H7.
    }
    specialize (IHn x0 H1 H3).
    assert(Bnrm (BB_sem_union (BBs)) x x0).
  {
    cbn[BB_sem_union] in H2. cbn[Bnrm] in H2. destruct H2.
    + unfold BB_sem in H2. cbn[Bnrm] in H2. 
        pose proof sem_start_end_with (Bnrm (BB_cmds_sem BBnow)) (Bnrm (BB_jmp_sem BBnow)) x x0 H2.
        my_destruct H4.
        pose proof BB_cmds_sem_no_change_num BBnow x1 x H4.
        unfold BB_jmp_sem in H5. simpl in H5. 
        rewrite H6 in H0. unfold BJump_sem in H5. 
        assert (BBnum_set (BBnow :: nil) (BB_num x1)). unfold BBnum_set. exists BBnow. split. unfold In. tauto.
        destruct (eval_cond_expr (jump_condition BBnow.(jump_info))).
        destruct ( jump_dest_2 BBnow.(jump_info)).
        unfold cjmp_sem in H5. simpl in H5. my_destruct H5. rewrite H8. reflexivity.
        unfold ujmp_sem in H5. simpl in H5. my_destruct H5. rewrite H7. reflexivity.
        unfold ujmp_sem in H5. simpl in H5. my_destruct H5. rewrite H7. reflexivity.
        tauto.
    + tauto.
  }
    cbn[Iter_nrm_BBs_n]. 
    pose proof sem_start_end_with_2 (Bnrm (BB_sem_union (BBs)))  (Iter_nrm_BBs_n (BB_sem_union (BBs)) n) x bs2.
    apply H5. exists x0. split. tauto. tauto.
Qed.
    

(*如果:
1. bs1的num不在BBnow的num中
2. (bs1, bs2) 在 BBnow ++ BBs 的任意步语义中
3. BBs不可能跳回到BBnow
那么 (bs1, bs2) 在 BBs 的任意步语义中
*)
Lemma simplify_listsem_with_mismatch_num:
  forall (bs1 bs2: BB_state)(BBnow: BasicBlock)(BBs: list BasicBlock),
  BBnow.(block_num) <> BB_num bs1 ->
  BBnum_set (BBnow :: nil) ∩ BBjmp_dest_set (BBnow :: BBs) == ∅ ->
  Bnrm (BB_list_sem (BBnow :: nil ++ BBs)) bs1 bs2 ->
  Bnrm (BB_list_sem BBs) bs1 bs2.
Proof.
  intros. 
  pose proof BBs_list_sem_exists_BB_bs1_x (BBnow::nil ++ BBs) bs1 bs2 H1.
  destruct H2 as [? | ?].
  - destruct H2 as [? [? [? [? ?]]]].
    unfold In in H2. destruct H2 as [? | ?].
    + pose proof BB_sem_start_BB_num bs1 x0 x H3.
      rewrite <- H2 in H5. rewrite H5 in H. contradiction.
    + simpl in H2. assert(In x BBs). tauto. 
        assert(exists BB : BasicBlock, In BB BBs /\ Bnrm (BB_sem BB) bs1 x0). exists x. split. tauto. tauto.
        assert(Bnrm (BB_sem_union BBs) bs1 x0). pose proof BBs_sem_union_exists_BB_bs1_bs2_inv BBs bs1 x0 H6. tauto.
        assert(~ BBnum_set (BBnow :: nil) (BB_num x0)) as x0_num_prop.
      {
        pose proof BB_jmp_sem_num_in_BBjmp_dest_set x. unfold BB_sem in H3. cbn[Bnrm] in H3.
        pose proof sem_start_end_with (Bnrm (BB_cmds_sem x)) (Bnrm (BB_jmp_sem x)) bs1 x0 H3.
        my_destruct H9.
        assert(In x (BBnow::BBs)). unfold In. right. tauto.
        assert(BBjmp_dest_set (BBnow :: BBs) (BB_num x0)). unfold BBjmp_dest_set.
        exists x. split. tauto. unfold BB_jmp_sem in H10. simpl in H10. unfold BJump_sem in H10.
        destruct (eval_cond_expr (jump_condition x.(jump_info))). destruct (jump_dest_2 x.(jump_info)).
        unfold cjmp_sem in H10. simpl in H10. my_destruct H10. destruct H14. 
        destruct H14. rewrite H14. left. tauto.
        destruct H14. rewrite H14. right. tauto.
        unfold ujmp_sem in H10. simpl in H10. my_destruct H10. left. rewrite H13. tauto.
        unfold ujmp_sem in H10. simpl in H10. my_destruct H10. left. rewrite H13. tauto.
        sets_unfold in H0. specialize (H0 (BB_num x0)).
        destruct H0. clear H1 H2 H13 x H3 H4 H5 H6 H7 H8 H9 H10 H11.
        intro contra.
        apply H0.
        split. tauto. tauto.
      }
        assert(Bnrm (BB_list_sem BBs) x0 bs2).
      {
        unfold BB_list_sem in H4. pose proof indexed_sem_exist_n (BB_sem_union (BBnow :: nil ++ BBs)) x0 bs2. destruct H8.
        unfold Bnrm in H4. specialize (H8 H4). clear H9. unfold BB_list_sem. unfold Bnrm. 
        pose proof indexed_sem_exist_n (BB_sem_union BBs) x0 bs2. destruct H9. apply H10. clear H9 H10 H3 H4 H6 H7.
        destruct H8 as [n ?]. exists n. induction n. simpl in H3. simpl. tauto.
        pose proof Iter_n_simplify (S n) BBnow BBs bs2 H0 x0 x0_num_prop H3. tauto.
      }
      pose proof unfold_once BBs. sets_unfold in H9. pose proof H9 bs1 bs2. apply H9. right. exists x0. split. tauto. tauto.
  - pose proof unfold_once BBs. apply H3. sets_unfold. left. tauto.
Qed.


(*如果 (bs1 bs2) 在BBs的任意步语义中，那么
a. bs2在BBs的jmpdest中
\/
b. bs1和bs2相等*)
Lemma BBs_bs2_in_BB_jmp_set:
  forall (BBs : list BasicBlock) (bs1 bs2: BB_state),
    Bnrm (BB_list_sem BBs) bs1 bs2 -> BBjmp_dest_set BBs (BB_num bs2) \/ bs1 = bs2.
Proof.
  intros. unfold BBjmp_dest_set.
  unfold BB_list_sem in H. cbn[Bnrm] in H. unfold Iter_nrm_BBs_n in H.
  sets_unfold in H. destruct H as [? ?].
  pose proof BBs_list_sem_exists_BB_bs1_x_tl BBs bs1 bs2. 
  unfold BB_list_sem in H0. cbn[Bnrm] in H0. sets_unfold in H0.
  assert (exists i : nat, Iter_nrm_BBs_n (BB_sem_union BBs) i bs1 bs2). {
    exists x. apply H.
  }
  pose proof H0 H1. destruct H2 as [? | ?].
  - my_destruct H2. left. exists x0. 
    pose proof single_step_jmp_property_for_bs2 x0 x1 bs2 H4.
    split. apply H2. apply H5.
  - right. tauto.  
Qed.


(*如果 (bs1 bs2) 在BBs的任意步语义中，那么
a. bs1在BBs的numset中
\/
b. bs1和bs2相等*)
Lemma BBs_bs1_in_BB_num_set:
  forall (BBs : list BasicBlock) (bs1 bs2: BB_state),
    Bnrm (BB_list_sem BBs) bs1 bs2 -> BBnum_set BBs (BB_num bs1) \/ bs1 = bs2.
Proof.
  intros. unfold BBnum_set.
  pose proof BBs_list_sem_exists_BB_bs1_x BBs bs1 bs2 H.
  destruct H0 as [? | ?].
  - my_destruct H0. left. exists x. split. apply H0.
    pose proof BB_sem_start_BB_num bs1 x0 x H1. rewrite H3. tauto.
  - right. apply H0.
Qed.

(*
对于所有的BBnow，BBs，和两个BB_state, 如果：
x1和x2在(BDenote_concate (BB_jmp_sem BBnow) (BB_list_sem BBs))这个语义里，即BBnow的jmp语义和BBs的语义的连接
=> 那么BBnow BBs x1.(BB_num) x2.(BB_num) 
*)
Lemma BB_restrict_sound:
    forall (BBnow BBnow': BasicBlock)(BBnum: nat)(BB_wo_last_: list BasicBlock) (x1 x2: BB_state)(c: cmd),
    (cmd_BB_gen c nil BBnow BBnum).(BasicBlocks) = (BBnow' :: nil) ++ BB_wo_last_ ->
    Bnrm (BDenote_concate (BB_jmp_sem BBnow') (BB_list_sem BB_wo_last_)) x1 x2 ->
    BB_wo_last_ <> nil -> 
    lt BBnow'.(block_num) BBnum -> (*BBnow的blocknum小于BBnum*)
    BBnow'.(block_num) = BBnow.(block_num) -> (*BBnow'的blocknum和BBnow的blocknum相同*)
    jump_kind BBnow.(jump_info) = UJump /\ jump_dest_2 BBnow.(jump_info) = None /\ jump_condition BBnow.(jump_info) = None ->
    x1.(st) <> x2.(st) (*两个BB_state的state也不等（否则就等于没有传入cmd了）*) ->

    BB_restrict BBnow' BB_wo_last_ x1.(BB_num) x2.(BB_num).
Proof.
  intros. unfold BB_restrict. rename H into lst_prop. rename H0 into BDenote_concate_prop.
  rename H1 into not_empty. rename H2 into BBnow_num_lt_BBnum.
  rename H3 into eq_blocknum. rename H4 into jump_prop. rename H5 into neq_st.
  unfold BDenote_concate in BDenote_concate_prop. cbn[Bnrm] in BDenote_concate_prop. sets_unfold in BDenote_concate_prop.
  destruct BDenote_concate_prop as [bs [cond1 cond2]]. repeat split.
  - unfold BB_jmp_sem in cond1. cbn[Bnrm] in cond1. unfold BJump_sem in cond1.
    destruct eval_cond_expr. destruct jump_dest_2.
    + unfold cjmp_sem in cond1. cbn[Bnrm] in cond1. destruct cond1 as [[? [? ?]] ?].  tauto.
    + unfold ujmp_sem in cond1. cbn[Bnrm] in cond1. destruct cond1 as [? [? ?]]. tauto.
    + unfold ujmp_sem in cond1. cbn[Bnrm] in cond1. destruct cond1 as [? [? ?]]. tauto.
  - pose proof BBs_bs2_in_BB_jmp_set BB_wo_last_ bs x2. apply H in cond2.
    destruct cond2.
    + tauto.
    + unfold BB_jmp_sem in cond1. cbn[Bnrm] in cond1. unfold BJump_sem in cond1.
      destruct jump_prop as [jmp_prop1 [jmp_prop2 jmp_prop3]].
      destruct (eval_cond_expr (jump_condition BBnow'.(jump_info))). 
      destruct (jump_dest_2 BBnow'.(jump_info)).
      -- simpl in cond1. my_destruct cond1. rewrite H0 in cond1. tauto.
      -- simpl in cond1. my_destruct cond1. rewrite H0 in cond1. tauto.
      -- simpl in cond1. my_destruct cond1. rewrite H0 in cond1. tauto.
  - sets_unfold. intros. 
    pose proof BBgen_range_single_soundness_correct c as key. unfold Q_BBgen_range in key.
    remember((cmd_BB_gen c nil BBnow BBnum).(next_block_num)) as end_num.
    remember(BBnow'::nil ++ BB_wo_last_ ++ (cmd_BB_gen c nil BBnow BBnum).(BBn)::nil) as BBdelta.
    assert (tmp: jump_kind BBnow.(jump_info) = UJump /\
    jump_dest_2 BBnow.(jump_info) = None). tauto.
    specialize (key BBnum end_num nil BBnow BBdelta tmp Heqend_num).
    clear tmp.
    assert(temp: to_result (cmd_BB_gen c nil BBnow BBnum) = nil ++ BBdelta).
    { 
      rewrite HeqBBdelta. unfold to_result. rewrite lst_prop.
      rewrite app_assoc_reverse. reflexivity.
    }
    rewrite eq_blocknum in BBnow_num_lt_BBnum.
    specialize (key temp BBnow_num_lt_BBnum). destruct key as [prop1 [prop2 prop3]].
    assert (contra: BBnum_set (tl BBdelta) a). {
      unfold BBnum_set. rewrite HeqBBdelta. 
      destruct H as [_ in_wo_last].
      unfold BBnum_set in in_wo_last. 
      destruct in_wo_last as [BB_ [c1 c2]].
      exists BB_. split.
      - simpl. pose proof In_sublist_then_in_list_head BasicBlock BB_ BB_wo_last_ ((cmd_BB_gen c nil BBnow BBnum).(BBn) :: nil) c1.
        tauto.
      - tauto. 
    }
    unfold all_ge in prop1. specialize (prop1 a contra).
    destruct H as [in_bbnow _].
    unfold BBnum_set in in_bbnow. destruct in_bbnow as [BB_ [c1 c2]].
    simpl in c1. destruct c1.
    rewrite <- H in c2. rewrite eq_blocknum in c2. lia. tauto.
  - sets_unfold in H. tauto.
  - sets_unfold in H. tauto.
Qed.

(*针对传入的cmds对BBnow的jmpinfo进行赋值。如果第一个c是if或者while，马上结束递归；否则应该对剩下的tl继续匹配*)
Fixpoint JmpInfoMatching(cmds: list cmd)(BBnow' next_BB: BasicBlock)(BBnow_jmp_info: BlockInfo)(BBnum: nat) : Prop :=
  (match cmds with
  | nil =>  BBnow'.(jump_info) = BBnow_jmp_info
  | c :: tl =>
    (match c with
      | CAsgn x e => JmpInfoMatching tl BBnow' next_BB BBnow_jmp_info BBnum
      | CIf e c1 c2 => (let BB_then_num := BBnum in
             let BB_else_num := S(BB_then_num) in  (* 用哪个比较好？next_BB.(block_num)还是 BBnum？*)
             let BlockInfo' := {|
                                  jump_kind := CJump;
                                  jump_dest_1 := next_BB.(block_num);
                                  jump_dest_2 := Some (S(next_BB.(block_num)));
                                  jump_condition := Some e
                                |} in
                                BBnow'.(jump_info) = BlockInfo')
      | CWhile pre e body => (let BB_pre_num := BBnum in
             let BB_body_num := S(BB_pre_num) in  (* 用哪个比较好？next_BB.(block_num)还是 BBnum？*)
             let BlockInfo' := {|
                                  jump_kind := UJump;
                                  jump_dest_1 := next_BB.(block_num);
                                  jump_dest_2 := None;
                                  jump_condition := None
                                |} in
                                BBnow'.(jump_info) = BlockInfo') 
    end)
  end).

Definition P(cmds: list cmd)(cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results): Prop :=
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum :nat),  

    jump_kind BBnow.(jump_info) = UJump /\ jump_dest_2 BBnow.(jump_info) = None /\ jump_condition BBnow.(jump_info) = None ->
    lt BBnow.(block_num) BBnum -> 
    BBnow.(block_num) <> jump_dest_1 BBnow.(jump_info) -> (*不会跳转到自己*)

    (exists BBs' BBnow' (BBcmds: list BB_cmd) BBnum' BBendnum,
    let res := list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum in
    let BBres := res.(BasicBlocks) ++ (res.(BBn) :: nil) in (* 这里已经加入了生成完后，最后停留在的那个BB了，从而BBs'里有这个BB*)
      (*用BBnow_delta，一方面处理增加的BBcmds的语义，另一方面考虑了jumpinfo*)
      let BBnow_delta := {|
        block_num := BBnow'.(block_num);
        commands :=  BBcmds;
        jump_info := BBnow'.(jump_info);
      |}
      in 
    (* 连接当前基本块中因为Asgn添加的语义和新生成的基本块的语义*)
    let ConcateBDenote := 
    {| Bnrm := (BB_list_sem (BBnow_delta :: nil ++ BBs')).(Bnrm);
       Berr:= (BB_list_sem (BBnow_delta :: nil ++ BBs')).(Berr);
       Binf:= ∅;
      |}
    in

    (* 根据BBs' 的情况分配JumpInfo*)
    match BBs' with
    | nil => BBnow'.(jump_info) = BBnow.(jump_info) /\ BBendnum = BBnow.(block_num)
    | next_BB :: _  =>  JmpInfoMatching cmds BBnow' next_BB  BBnow.(jump_info) BBnum 
    end
    
    /\

    (*要拿到用于分配的下一个BBnum的信息*)

    BBnum' = res.(next_block_num) /\

    BBnow'.(commands) = BBnow.(commands) ++ BBcmds /\ BBnow'.(block_num) = BBnow.(block_num) /\

    BBres = BBs ++ (BBnow' :: nil) ++ BBs' /\ BCequiv (ConcateBDenote) (cmd_list_sem cmd_sem cmds) BBnow'.(block_num) BBnow.(jump_info).(jump_dest_1) (*也就是endinfo*)

    /\ res.(BBn).(jump_info) = BBnow.(jump_info)).



Definition Qd_if (e: expr) (c1 c2: list cmd): Prop :=
    forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum :nat), 
    let res := cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum in
    let BBres := res.(BasicBlocks) ++ (res.(BBn) :: nil) in 



    (*BBnow的jumpinfo是CJump*)
    (* BBnow为无条件跳转！*)
    (BBnow.(jump_info).(jump_kind) = UJump /\ BBnow.(jump_info).(jump_dest_2) = None) ->


    (*CIf*)
    forall BBnow' BBs' BBs_wo_last 
      BB_then_num BB_else_num BB_next_num
      BB_then BB_else BBs_then BBs_else 
      BB_now_then BB_now_else
      BB_num1 BB_num2
      , 

      res.(BasicBlocks) ++ (res.(BBn) :: nil) =  BBs ++ (BBnow' :: nil) ++ BBs' -> res.(BasicBlocks) =  BBs ++ (BBnow' :: nil) ++ BBs_wo_last ->
      BB_then_num = BBnum -> BB_else_num = S(BB_then_num) -> BB_next_num = S(BB_else_num) -> BB_num1 = S(BB_next_num)
      -> BB_then = {|block_num := BB_then_num;
        commands := nil;
        jump_info := {|
          jump_kind := UJump;
          jump_dest_1 := BB_next_num; 
          jump_dest_2 := None; 
          jump_condition := None
          |};
        |}
      -> BB_else = {|
        block_num := BB_else_num;
        commands := nil;
        jump_info := {|
            jump_kind := UJump;
            jump_dest_1 := BB_next_num; 
            jump_dest_2 := None; 
            jump_condition := None
          |}
        |}
      -> BBnow' = {|block_num := BBnow.(block_num);
      commands := BBnow.(commands);
      jump_info := {|
         jump_kind := CJump;
         jump_dest_1 := BB_then_num; 
         jump_dest_2 := Some BB_else_num; 
         jump_condition := Some e
         |};
      |}
      -> to_result (list_cmd_BB_gen cmd_BB_gen c1 (nil) BB_then BB_num1) =  BB_now_then::nil ++ BBs_then
      -> to_result (list_cmd_BB_gen cmd_BB_gen c2 (nil) BB_else BB_num2) = BB_now_else :: nil ++ BBs_else
      -> BB_num2 = (list_cmd_BB_gen cmd_BB_gen c1 (nil) BB_then BB_num1).(next_block_num)
      -> BB_now_then.(block_num) = BB_then_num
      -> BB_now_else.(block_num) = BB_else_num
      -> lt BBnow.(block_num) BBnum  (*BBnow的num小于下一个分配的num*)
      -> BBnow.(block_num) <> jump_dest_1 BBnow.(jump_info) (*BBnow不会无条件跳转到自身*)
      ->
      (separate_property BBnow' BBs_wo_last) (*分离性质1*)
      /\ (BBnum_set (BB_now_then :: nil ++ BBs_then) ∩ BBnum_set (BB_now_else :: nil ++ BBs_else) == ∅ ) (*分离性质3*)
      /\ (BBjmp_dest_set (BB_now_then :: nil ++ BBs_then) ∩ BBnum_set (BB_now_else :: nil ++ BBs_else) == ∅) (*分离性质5*)
      /\ (BBjmp_dest_set (BB_now_else :: nil ++ BBs_else) ∩ BBnum_set (BB_now_then :: nil ++ BBs_then) == ∅). (*分离性质6*)
 

(*如果在BBs里，那么一定在BBs ++ tl里*)
Lemma In_tail_inclusive:
  forall (BBs : list BasicBlock) (BB tl : BasicBlock),
    In BB BBs -> In BB (BBs ++ tl::nil).
Proof.
  intros. induction BBs.
  - unfold In in H. tauto.
  - unfold In. simpl.
    unfold In in H. destruct H as [? | ?].
    + left. apply H.
    + right. pose proof IHBBs H. apply H0.
Qed. 

Lemma Sx_not_equal_x:
  forall (a : nat),
    S a = a -> False.
Proof.
  intros. induction a.
  - inversion H.
  - apply IHa. inversion H. exact H.
Qed.

Lemma x_lt_Sx:
  forall (a : nat),
    lt a (S a).
Proof.
  intros. induction a.
  - apply Nat.lt_0_succ.
  - apply lt_n_S. apply IHa.
Qed.

Lemma x_lt_SSx:
  forall (a : nat),
    lt a (S (S a)).
Proof.
  intros. induction a.
  - apply Nat.lt_0_succ.
  - apply lt_n_S. apply IHa.
Qed.

Lemma x_lt_SSSx:
  forall (a : nat),
    lt a (S (S (S a))).
Proof.
  intros. induction a.
  - apply Nat.lt_0_succ.
  - apply lt_n_S. apply IHa.
Qed.

Lemma a_lt_b_le_c:
  forall (a b c : nat),
    lt a b -> le b c -> lt a c.
Proof.
  intros. induction H0.
  - apply H.
  - transitivity b.
    + apply H.
    + nia. 
Qed.

Lemma a_lt_b_a_neq_b : forall (a b : nat), lt a b -> a <> b.
Proof.
  intros a b H.
  unfold not.
  intros H0.
  rewrite H0 in H.
  apply (lt_irrefl b H).
Qed.

Lemma not_a_lt_a: forall (a : nat), ~ lt a a.
Proof.
  intros a H.
  apply (lt_irrefl a H).
Qed.

Lemma not_a_le_b_and_a_gt_b: forall (a b : nat), 
  le a b -> lt b a -> False.
Proof.
  intros. unfold not. intros.
  destruct H; nia.
Qed.






Lemma Qd_if_sound:
  forall (e: expr) (c1 c2: list cmd),
    Qd_if e c1 c2.
Proof.
  intros.
  unfold Qd_if. intros.
  rename H0 into BBlist_prop.
  rename H into jmp_prop.
  rename H1 into wo_last_prop. rename H2 into then_num_prop. rename H3 into else_num_prop. rename H4 into next_num_prop. rename H5 into BBnum1_prop. 
  rename H6 into BB_then_prop. rename H7 into BB_else_prop. rename H8 into BBnow'_prop.
  rename H9 into BBlist_then_prop. rename H10 into BBlist_else_prop.
  rename H11 into BBnum2_prop. rename H12 into BBnowthen_blocknum_prop.
  rename H13 into BBnowelse_blocknum_prop.
  rename H14 into bbnow_num_lt_BBnum.
  rename H15 into bbnow_num_neq_jmpdest1.
  repeat split.
  - pose proof BBgen_range_single_soundness_correct (CIf e c1 c2) as range_prop.
    unfold Q_BBgen_range in range_prop.
    remember ((cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num)) as endnum.
    specialize (range_prop BBnum endnum BBs BBnow (BBnow'::nil ++ BBs')). 
    unfold to_result in range_prop.
    pose proof range_prop jmp_prop Heqendnum BBlist_prop bbnow_num_lt_BBnum as range_prop. 
    sets_unfold. intros. rename H into key.
    destruct range_prop as [num_range_prop1 [num_range_prop2 jmp_range_prop]].
    assert (key_prop1: (BBs_wo_last ++ (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil) = BBs'). {
          (* 这个是列表的性质, 在H里两边消去即可 *)
          assert(BBs ++ (BBnow' :: nil) ++ (BBs_wo_last ++ (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil) =
          BBs ++ ((BBnow' :: nil) ++ BBs')). rewrite <- BBlist_prop. 
                pose proof list_assoc BasicBlock BBs  ((BBnow' :: nil) ++ BBs_wo_last)  ((cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil).
                rewrite wo_last_prop. 
                rewrite <-  app_assoc.
                rewrite app_assoc_reverse. reflexivity.
                pose proof app_inv_head ( BBs ++ (BBnow' :: nil)) (BBs_wo_last ++ (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil) (BBs').
                apply H0. rewrite <- app_assoc. rewrite app_assoc_reverse. apply H.
    }
    assert (key_prop2: a ∈ BBnum_set (BBnow' :: nil) ∩ BBjmp_dest_set (BBnow' :: BBs')). {
      sets_unfold. destruct key as [key1 key2]. split. 
      - apply key1.
      - unfold BBjmp_dest_set in key2. unfold BBjmp_dest_set. destruct key2 as [? [? ?]]. exists x. split.
        + rewrite <- key_prop1. simpl. destruct H. 
          left. tauto. 
          right. pose proof In_tail_inclusive BBs_wo_last x {|
              block_num := S (S BBnum);
              commands := nil;
              jump_info := BBnow.(jump_info)
            |}.
          apply H1. apply H.
        + apply H0. 
    }

    assert (empty_: BBnum_set (BBnow' :: nil) ∩ BBjmp_dest_set (BBnow' :: BBs') == ∅).
    { 
      (*num_range_prop1 | num_range_prop2 | jmp_range_prop*)
      sets_unfold in jmp_range_prop.
      intros contra.
      specialize (jmp_range_prop contra).
      split.
      - intros.
        destruct H as [cond1 cond2].
        pose proof jmp_range_prop cond2.
        destruct H as [case1 | case2].
        + unfold section in case1. destruct case1 as [? ?]. unfold BBnum_set in cond1.
          destruct cond1 as [BBnow'_ conds].
          destruct conds. simpl in H1. destruct H1. rewrite <- H1 in H2. rewrite BBnow'_prop in H2.
          cbn [block_num] in H2. rewrite H2 in bbnow_num_lt_BBnum. lia. tauto.
        + unfold unit_set in case2. unfold BBnum_set in cond1. destruct cond1. destruct H. simpl in H.
          destruct H. rewrite <- H in H0. rewrite BBnow'_prop in H0. cbn [block_num] in H0. lia. tauto.
      - intros. sets_unfold in H. tauto.
    }
    sets_unfold in empty_. specialize (empty_ a). tauto.
    
    (* rewrite H13 in H16. sets_unfold in H16. tauto. *)
  - sets_unfold in H. tauto.
  - sets_unfold in H. tauto.
  - pose proof BBgen_range_list_soundness_correct c1 as c1_range.
    pose proof BBgen_range_list_soundness_correct c2 as c2_range.
    unfold P_BBgen_range in c1_range, c2_range.

    (* Do if part first *)
    remember ((list_cmd_BB_gen cmd_BB_gen c1 nil BB_then BB_num1).(next_block_num)) as BB_then_end_num.
    specialize (c1_range BB_num1 BB_then_end_num nil BB_then (BB_now_then::nil ++ BBs_then)).
    assert (c1_jmp_prop: jump_kind BB_then.(jump_info) = UJump /\ jump_dest_2 BB_then.(jump_info) = None). {
      rewrite BB_then_prop. cbn [jump_info]. cbn [jump_kind]. cbn [jump_dest_2]. cbn [jump_condition]. tauto.
    }

    assert (c1_list_prop: to_result (list_cmd_BB_gen cmd_BB_gen c1 (nil) BB_then BB_num1) = BB_now_then :: nil ++ BBs_then). {
      rewrite BBlist_then_prop. simpl. reflexivity.
    }

    pose proof c1_range c1_jmp_prop HeqBB_then_end_num c1_list_prop as if_range.

    (* Then the second part *)
    remember ((list_cmd_BB_gen cmd_BB_gen c2 (nil) BB_else BB_then_end_num).(next_block_num)) as BB_else_end_num.

    specialize (c2_range BB_then_end_num BB_else_end_num (nil) BB_else (BB_now_else::nil ++ BBs_else)).
    
    assert (c2_jmp_prop: jump_kind BB_else.(jump_info) = UJump /\ jump_dest_2 BB_else.(jump_info) = None). {
      rewrite BB_else_prop. cbn [jump_info]. cbn [jump_kind]. cbn [jump_dest_2]. cbn [jump_condition]. tauto.
    }
    assert (c2_list_prop: to_result (list_cmd_BB_gen cmd_BB_gen c2 (nil) BB_else BB_then_end_num) =
    BB_now_else :: nil ++ BBs_else). {
      rewrite <- BBnum2_prop. 
      rewrite BBlist_else_prop. simpl. reflexivity.
    }


    pose proof c2_range c2_jmp_prop HeqBB_else_end_num c2_list_prop as else_range.
    clear c1_jmp_prop c2_jmp_prop.

    
    (* 之后只需要利用H12, H13, H16, H17来完成证明 *)
    assert (final: ~ exists x, x ∈ BBnum_set (BB_now_then :: nil ++ BBs_then) /\ x ∈ BBnum_set (BB_now_else :: nil ++ BBs_else)). {
      intros contra.
      destruct contra as [x [cond1 cond2]].
      destruct if_range as [if_range_p1 [if_range_p2 if_range_p3 ]].
      destruct else_range as [else_range_p1 [else_range_p2 else_range_p3 ]].
      sets_unfold in cond1. sets_unfold in cond2.
      unfold all_ge in if_range_p1. pose proof (if_range_p1 x) as if_range_p1.
      unfold all_ge in else_range_p1. pose proof (else_range_p1 x) as else_range_p1.
      unfold all_lt in if_range_p2. pose proof (if_range_p2 x) as if_range_p2.
      unfold all_lt in else_range_p2. pose proof (else_range_p2 x) as else_range_p2.
      cbn [tl] in *. simpl in *.

      unfold BBnum_set in cond1. unfold BBnum_set in cond2.
      sets_unfold in cond1. sets_unfold in cond2.
      destruct cond1 as [bb1 [pos1 restrict1]]. destruct cond2 as [bb2 [pos2 restrict2]].

      (* 矛盾点 *)
      assert (restrict: bb2.(block_num) = bb1.(block_num)). {
        rewrite <- restrict1 in restrict2. tauto.
      }
      
      (* 分成四种情况讨论 *)

      destruct pos1 as [is_then | is_in_BBs_then]; destruct pos2 as [is_else | is_in_BBs_else].

      - rewrite <- is_then in restrict. rewrite <- is_else in restrict.
        rewrite BBnowthen_blocknum_prop in restrict. rewrite BBnowelse_blocknum_prop in restrict. lia.
      - rewrite <- is_then in restrict. rewrite BBnowthen_blocknum_prop in restrict.
        assert (premise1: BBnum_set BBs_else x). {
          unfold BBnum_set. exists bb2. split.
          tauto. tauto.
        }

        pose proof else_range_p1 premise1 as else_range_p1.
        rewrite restrict in restrict2. rewrite <- restrict2 in else_range_p1.
          assert (lt BB_then_num BB_then_end_num). 
          {
            pose proof bbnow_num_lt_next_num nil BB_then BB_num1 c1 as lemma1.
            assert (temp: (BB_then.(block_num) < BB_num1)%nat).
            subst BB_then. simpl. lia.
            pose proof (lemma1 temp) as lemma1.
            rewrite <- HeqBB_then_end_num in lemma1.
            subst BB_then. simpl in lemma1. lia.
          }
          lia.
    
      - assert (premise1: BBnum_set BBs_then x). {
          unfold BBnum_set. exists bb1. split; tauto.
        }
        pose proof if_range_p1 premise1 as if_range_p1.
        + rewrite <- is_else in restrict2. rewrite BBnowelse_blocknum_prop in restrict2.
          rewrite <- restrict2 in if_range_p1. lia.

      - assert (premise1: BBnum_set BBs_then x).
        {
          unfold BBnum_set. exists bb1. split; tauto.
        }
        assert (premise2: BBnum_set BBs_else x).
        {
          unfold BBnum_set. exists bb2. split; tauto.
        }
        pose proof if_range_p1 premise1 as if_range_p1.
        pose proof else_range_p1 premise2 as else_range_p1.
        pose proof if_range_p2 premise1 as if_range_p2. lia.
    }
    unfold not in final.
    intros. rename H into premise.
    sets_unfold in premise.
    apply final.
    exists a. tauto.
  - sets_unfold in H. tauto.
  - sets_unfold in H. tauto.
  - intros. sets_unfold. 
    pose proof BBgen_range_list_soundness_correct c1 as c1_range.
    pose proof BBgen_range_list_soundness_correct c2 as c2_range.
    unfold P_BBgen_range in c1_range, c2_range.

    (* Do if part first *)
    remember ((list_cmd_BB_gen cmd_BB_gen c1 nil BB_then BB_num1).(next_block_num)) as BB_then_end_num.
    specialize (c1_range BB_num1 BB_then_end_num nil BB_then (BB_now_then::nil ++ BBs_then)).
    assert (c1_jmp_prop: jump_kind BB_then.(jump_info) = UJump /\ jump_dest_2 BB_then.(jump_info) = None). {
      rewrite BB_then_prop. cbn [jump_info]. cbn [jump_kind]. cbn [jump_dest_2]. cbn [jump_condition]. tauto.
    }

    assert (c1_list_prop: to_result (list_cmd_BB_gen cmd_BB_gen c1 (nil) BB_then BB_num1) = BB_now_then :: nil ++ BBs_then). {
      rewrite BBlist_then_prop. simpl. reflexivity.
    }

    pose proof c1_range c1_jmp_prop HeqBB_then_end_num c1_list_prop as if_range.

    (* Then the second part *)
    remember ((list_cmd_BB_gen cmd_BB_gen c2 (nil) BB_else BB_then_end_num).(next_block_num)) as BB_else_end_num.

    specialize (c2_range BB_then_end_num BB_else_end_num (nil) BB_else (BB_now_else::nil ++ BBs_else)).
    
    assert (c2_jmp_prop: jump_kind BB_else.(jump_info) = UJump /\ jump_dest_2 BB_else.(jump_info) = None). {
      rewrite BB_else_prop. cbn [jump_info]. cbn [jump_kind]. cbn [jump_dest_2]. tauto.
    }

    assert (c2_list_prop: to_result (list_cmd_BB_gen cmd_BB_gen c2 (nil) BB_else BB_then_end_num) =
    BB_now_else :: nil ++ BBs_else). {
      rewrite <- BBnum2_prop. 
      rewrite BBlist_else_prop. simpl. reflexivity.
    }


    pose proof c2_range c2_jmp_prop HeqBB_else_end_num c2_list_prop as else_range.
    clear c1_jmp_prop c2_jmp_prop.

    rename H into GOAL.
    destruct if_range as [if_range_p1 [if_range_p2 if_range_p3 ]].
    destruct else_range as [else_range_p1 [else_range_p2 else_range_p3 ]].
    clear if_range_p1 if_range_p2 c1_list_prop c2_list_prop c1_range c2_range.
    unfold section in if_range_p3. unfold section in else_range_p3.
    sets_unfold in if_range_p3. sets_unfold in else_range_p3.
    specialize (if_range_p3 a). specialize (else_range_p3 a).
    destruct GOAL as [in_then_set in_else_set].
    pose proof if_range_p3 in_then_set as key. clear if_range_p3. 
    destruct key as [case1 | case2].
    + unfold BBnum_set in in_else_set.
      destruct in_else_set as [bb_else [pos_else restrict_else]].
      destruct pos_else as [head | tail].
      * rewrite <- head in restrict_else. rewrite BBnowelse_blocknum_prop in restrict_else.
        rewrite <- restrict_else in case1. destruct case1 as [subcase1 subcase2].
        lia.
      * unfold all_ge in else_range_p1. specialize (else_range_p1 a). unfold BBnum_set in else_range_p1.
        assert (pre: (exists BB : BasicBlock,
        In BB (tl (BB_now_else :: nil ++ BBs_else)) /\ BB.(block_num) = a)).
        {
        exists bb_else.
        split.
        - tauto.
        - tauto.
        }
        specialize (else_range_p1 pre). lia.
    + unfold unit_set in case2. subst BB_then. cbn [jump_info] in case2. cbn[jump_dest_1] in case2.
      destruct in_else_set as [bb_else [pos_else restrict_else]].
      destruct pos_else as [head | tail].
      * rewrite <- head in restrict_else. rewrite case2 in restrict_else. rewrite BBnowelse_blocknum_prop in restrict_else.
        lia.
      * unfold all_ge in else_range_p1. specialize (else_range_p1 a). unfold BBnum_set in else_range_p1.
        assert (pre: (exists BB : BasicBlock,
        In BB (tl (BB_now_else :: nil ++ BBs_else)) /\ BB.(block_num) = a)).
        {
        exists bb_else.
        split.
        - tauto.
        - tauto.
        }
        specialize (else_range_p1 pre). 
        rewrite case2 in else_range_p1. 
        rewrite HeqBB_then_end_num in else_range_p1.
        rewrite BBnum1_prop in else_range_p1.
        set(temp_block := {|
        block_num := BB_then_num;
        commands := nil;
        jump_info :=
          {| jump_kind := UJump; jump_dest_1 := BB_next_num; jump_dest_2 := None; jump_condition := None |}
        |}).
        
        pose proof (bbnum_le_next_num nil temp_block (S BB_next_num) c1).
        assert (pre_: lt temp_block.(block_num) (S BB_next_num)). {
          subst temp_block. simpl. lia.
        }
        specialize (H pre_). subst temp_block. simpl in H. lia.
      
  - sets_unfold in H. tauto.
  - sets_unfold in H. tauto.
  - intros. sets_unfold. 
    pose proof BBgen_range_list_soundness_correct c1 as c1_range.
    pose proof BBgen_range_list_soundness_correct c2 as c2_range.
    unfold P_BBgen_range in c1_range, c2_range.

    (* Do if part first *)
    remember ((list_cmd_BB_gen cmd_BB_gen c1 nil BB_then BB_num1).(next_block_num)) as BB_then_end_num.
    specialize (c1_range BB_num1 BB_then_end_num nil BB_then (BB_now_then::nil ++ BBs_then)).
    assert (c1_jmp_prop: jump_kind BB_then.(jump_info) = UJump /\ jump_dest_2 BB_then.(jump_info) = None). {
      rewrite BB_then_prop. cbn [jump_info]. cbn [jump_kind]. cbn [jump_dest_2]. cbn [jump_condition]. tauto.
    }

    assert (c1_list_prop: to_result (list_cmd_BB_gen cmd_BB_gen c1 (nil) BB_then BB_num1) = BB_now_then :: nil ++ BBs_then). {
      rewrite BBlist_then_prop. simpl. reflexivity.
    }

    pose proof c1_range c1_jmp_prop HeqBB_then_end_num c1_list_prop as if_range.

    (* Then the second part *)
    remember ((list_cmd_BB_gen cmd_BB_gen c2 (nil) BB_else BB_then_end_num).(next_block_num)) as BB_else_end_num.

    specialize (c2_range BB_then_end_num BB_else_end_num (nil) BB_else (BB_now_else::nil ++ BBs_else)).
    
    assert (c2_jmp_prop: jump_kind BB_else.(jump_info) = UJump /\ jump_dest_2 BB_else.(jump_info) = None). {
      rewrite BB_else_prop. cbn [jump_info]. cbn [jump_kind]. cbn [jump_dest_2]. tauto.
    }

    assert (c2_list_prop: to_result (list_cmd_BB_gen cmd_BB_gen c2 (nil) BB_else BB_then_end_num) =
    BB_now_else :: nil ++ BBs_else). {
      rewrite <- BBnum2_prop. 
      rewrite BBlist_else_prop. simpl. reflexivity.
    }


    pose proof c2_range c2_jmp_prop HeqBB_else_end_num c2_list_prop as else_range.
    clear c1_jmp_prop c2_jmp_prop.

    rename H into GOAL.
    destruct if_range as [if_range_p1 [if_range_p2 if_range_p3 ]].
    destruct else_range as [else_range_p1 [else_range_p2 else_range_p3 ]].
    clear c1_list_prop c2_list_prop c1_range c2_range.
    unfold section in if_range_p3. unfold section in else_range_p3.
    sets_unfold in if_range_p3. sets_unfold in else_range_p3.
    specialize (if_range_p3 a). specialize (else_range_p3 a).
    destruct GOAL as [in_else_set in_then_set].
    pose proof else_range_p3 in_else_set as key. clear else_range_p3. 
    destruct key as [case1 | case2].
    + unfold BBnum_set in in_then_set.
      destruct in_then_set as [bb_then [pos_then restrict_then]].
      destruct pos_then as [head | tail].
      * rewrite <- head in restrict_then. rewrite BBnowthen_blocknum_prop in restrict_then.
        rewrite <- restrict_then in case1. destruct case1 as [subcase1 subcase2].
        pose proof bbnow_num_lt_next_num nil BB_then BB_num1 c1 as temp.
        assert ((BB_then.(block_num) < BB_num1)%nat). subst BB_num1. subst BB_then. simpl. lia.
        subst BB_then_num.
        pose proof bbnum_le_next_num nil BB_then BB_num1 c1 as temp1.
        assert (lt BB_then.(block_num) BB_num1). subst BB_then. simpl. lia.
        pose proof (temp1 H0) as key. subst BB_then_end_num. simpl in key. lia.
      * unfold all_ge in if_range_p1. specialize (if_range_p1 a). unfold BBnum_set in if_range_p1.
        assert (pre: (exists BB : BasicBlock,
        In BB (tl (BB_now_then :: nil ++ BBs_then)) /\ BB.(block_num) = a)).
        {
        exists bb_then.
        split.
        - tauto.
        - tauto.
        }
        unfold all_lt in if_range_p2. specialize (if_range_p2 a). unfold BBnum_set in if_range_p2.
        specialize (if_range_p2 pre). lia.
    + unfold unit_set in case2. subst BB_else. cbn [jump_info] in case2. cbn[jump_dest_1] in case2.
    destruct in_then_set as [bb_then [pos_then restrict_then]].
    destruct pos_then as [head | tail].
    * rewrite <- head in restrict_then. rewrite case2 in restrict_then. rewrite BBnowthen_blocknum_prop in restrict_then.
      lia.
    * unfold all_ge in if_range_p1. specialize (if_range_p1 a). unfold BBnum_set in if_range_p1.
      assert (pre: (exists BB : BasicBlock,
      In BB (tl (BB_now_then :: nil ++ BBs_then)) /\ BB.(block_num) = a)).
      {
      exists bb_then.
      split.
      - tauto.
      - tauto.
      }
      specialize (if_range_p1 pre). 
      rewrite case2 in if_range_p1. 
      rewrite HeqBB_then_end_num in else_range_p1.
      rewrite BBnum1_prop in else_range_p1.
      set(temp_block := {|
      block_num := BB_then_num;
      commands := nil;
      jump_info :=
        {| jump_kind := UJump; jump_dest_1 := BB_next_num; jump_dest_2 := None; jump_condition := None |}
      |}).
      
      pose proof (bbnum_le_next_num nil temp_block (S BB_next_num) c1).
      assert (pre_: lt temp_block.(block_num) (S BB_next_num)). {
        subst temp_block. simpl. lia.
      }
      specialize (H pre_). subst temp_block. simpl in H. lia.
    
  - sets_unfold in H. tauto.
  - sets_unfold in H. tauto.
Qed.


Definition is_asgn (c: cmd): Prop :=
  match c with
  | CAsgn _ _ => True
  | _ => False
  end.
 

Definition Qb(c: cmd): Prop :=
  (* Qb: Q basic, 不包含disjoint的性质。Qb(Asgn)里面不能出现cmds, 或者说Q(c)里面你就要讲BBs等等变化前后有什么区别, 别去搞cmds，你们搞得那个反而把问题搞复杂了
    嗯，当然你要证明的是语义的变化，所以你要说多出来的commands的语义，和那个c的语义一样 -- by cqx *)
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum :nat), 
    let res := cmd_BB_gen c BBs BBnow BBnum in
    jump_kind BBnow.(jump_info) = UJump /\ jump_dest_2 BBnow.(jump_info) = None -> 
    lt BBnow.(block_num) BBnum -> 
    BBnow.(block_num) <> jump_dest_1 BBnow.(jump_info) -> (*不会跳转到自己*)
    jump_condition BBnow.(jump_info) = None ->
    (*CAsgn*)
    (is_asgn(c) /\ (exists BBnow' BBcmd,
      res.(BBn) = BBnow' /\
      BBnow'.(commands) = BBnow.(commands) ++ (BBcmd :: nil) /\
      BCequiv (BAsgn_list_sem (BBcmd :: nil)) (cmd_sem c) BBnow'.(block_num) BBnow'.(block_num))) (*还在当下的BBnow里，BBnum则是下一个BB的编号，不能用*)
    \/
    (*CIf / CWhile*)
    ((~ is_asgn(c)) /\
    (exists BBnow' BBs' BBnum' BBs_wo_last, 
      res.(BasicBlocks) ++ (res.(BBn) :: nil) =  BBs ++ (BBnow' :: nil) ++ BBs' /\ res.(BasicBlocks) =  BBs ++ (BBnow' :: nil) ++ BBs_wo_last /\
      res.(next_block_num) = BBnum' /\
      BCequiv (BDenote_concate (BB_jmp_sem BBnow')(BB_list_sem BBs_wo_last)) (cmd_sem c) BBnow.(block_num) (S (S BBnum)))). (* 这里的BBnum'是生成的BBlist的最后一个BB的编号，对于If和while，语义上都应该停留在next里！要和cmd_BB_gen中的BBnum做区分！ *)
(* # BUG BCequiv里不应该有最后的BBnext！*)

(* c: the cmd we are currently facing
  BBs: list of Basic Blocks which have been already generated
  BBnow: the Basic Block we are currently at
  BB_num: we should start assigning new basic blocks with BB_num 
  
  Record basic_block_gen_results : Type := {
  BasicBlocks: list BasicBlock; (* already finished blocks*)
  BBn: BasicBlock; (* current_block_num should be the block num of BBnow, I think *)
  next_block_num: nat (* I think next block should start with the number*)
}.*)



(*对于cmdbbgen，cmd = CAsgn的一些性质*)
Lemma Asgn_prop:
  forall (BBnow: BasicBlock) (BBs: list BasicBlock) (BBnum: nat) (x: var_name) (e: expr),
  (cmd_BB_gen (CAsgn x e) BBs BBnow BBnum).(BasicBlocks) = BBs /\
  (cmd_BB_gen (CAsgn x e) BBs BBnow BBnum).(BBn) = {|
    block_num := BBnow.(block_num);
    commands := BBnow.(commands) ++ {| X := x; E := e |} :: nil;
    jump_info := BBnow.(jump_info)
  |} /\
  (cmd_BB_gen (CAsgn x e) BBs BBnow BBnum).(next_block_num) = BBnum.
Proof.
  intros. simpl. split.
  - reflexivity.
  - split.
    + reflexivity.
    + reflexivity.
Qed.


Lemma head_eq_prop:
  forall (A: Type) (l1 l2: list A) (a b: A),
  a::l1 = b::l2 -> a = b.
Proof.
  intros. inversion H. reflexivity.
Qed.

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

(*如果l1 ++ l2 = a :: l3，那么a肯定是l1的头*)
Lemma extract_head_from_list:
  forall (A: Type) (l1 l2 l3: list A) (a: A)(d: A),
  l1 ++ l2 = a :: l3 -> a = hd d l1.
Proof.
  intros. revert l1 l2 H.
  induction l3. 
  - intros. 
  (*TODO BUG*)
Admitted.

Lemma exact_tail_from_list:
  forall (A: Type) (l1 l2 l3: list A) (a b: A),
  l1 ++ a::nil = l2 ++ b::l3 -> l3 <> nil -> In a l3.
Proof.
  intros. revert l1 l2 H.
  (*TODO*)
Admitted.



(*如果num在BBnum_set(BBnow::BBs)中，那么为在BBnow的num，要么在BBs的num中*)
Lemma destruct_in_BBnum_set:
  forall (BBnow: BasicBlock) (BBs: list BasicBlock) (BBnum: nat),
  BBnum_set(BBnow::BBs) (BBnum) -> BBnum = BBnow.(block_num) \/ BBnum_set(BBs) (BBnum).
Proof.
  intros. unfold BBnum_set in H. my_destruct H.
  unfold In in H. destruct H as [? | ?].
  - left. rewrite <- H0. rewrite H. tauto.
  - right. rewrite <- H0. unfold BBnum_set. exists x. split. apply H. tauto.
Qed.


(*语义上的一些引理 ===================*)

(*对于任意步语义，在BBs的语义中总能推出在BBnow::BBs的语义中*)
Lemma Iter_shrink:
  forall (BBs: list BasicBlock)(BBnow'_: BasicBlock) (n: nat) (bs1 bs2: BB_state),
  Iter_nrm_BBs_n (BB_sem_union BBs) n bs1 bs2 ->
  (Iter_nrm_BBs_n
  {|
    Bnrm :=
      fun a1 a2 : BB_state =>
      (exists i : BB_state,
         Rels.id a1 i /\
         Bnrm
           (BJump_sem BBnow'_.(block_num) (jump_dest_1 BBnow'_.(jump_info))
              (jump_dest_2 BBnow'_.(jump_info))
              (eval_cond_expr (jump_condition BBnow'_.(jump_info)))) i a2) \/
      Bnrm (BB_sem_union BBs) a1 a2;
    Berr := fun _ : BB_state => False;
    Binf := fun _ : BB_state => False
  |} n bs1 bs2).
Proof.
  intros. revert bs1 bs2 H. 
  induction n. 
  - simpl. tauto.
  - intros.  simpl. destruct H as [? [? ?]]. sets_unfold. sets_unfold in H. sets_unfold in H0.
    exists x. split.
    + tauto.
    + specialize (IHn x bs2). specialize (IHn H0). tauto.
Qed.
  
(*===================*)

(*如果一个BB在一串列表里，但是它的num只和第一个head匹配，那它就是这个head*)
Lemma must_be_head_with_num_restriction:
forall (BBhead BBnow: BasicBlock) (BBs: list BasicBlock),
  In BBnow (BBhead :: nil ++ BBs) -> BBnow.(block_num) = BBhead.(block_num) -> ~ BBhead.(block_num) ∈ BBnum_set (BBs)
  -> BBnow = BBhead.
Proof.
  intros. unfold In in H. destruct H.
  - rewrite H. tauto.
  - unfold not in H1. sets_unfold in H1. assert (False). {
      apply H1. unfold BBnum_set. exists BBnow. split.
      apply H. apply H0.
    }
    tauto.
Qed. 


(*对于任意的两串BBs1和BBs2，以及任意的两个BBnow1 BBnow2 和 bs1 bs2， 如果: 
1. (bs1, bs2) 在 BB_list_sem (BBnow1 :: nil ++ BBs1 ++ BBnow2 :: nil ++ BBs2) 中
2. bs1 不等于 bs2
3. BBnow1 :: nil ++ BBs1 和 BBnow2 :: nil ++ BBs2 的BBnum_set不交
4. BBnow1 :: nil ++ BBs1 和 BBnow2 :: nil ++ BBs2 的BBjmp_dest_set不交
5. bs1的BBnum在 BBnow1 :: nil ++ BBs1 的numset中
6. bs2的BBnum在 BBnow2 :: nil ++ BBs2 的jmpset中
那么存在一个x，使得:
1. (bs1, x) 在 BB_list_sem (BBnow1 :: nil ++ BBs1) 中
2. (x, bs2) 在 BB_list_sem (BBnow2 :: BBs2) 中
*)
Lemma an_over_pass_bridge: 
  forall (BBs1 BBs2: list BasicBlock)(BBnow1 BBnow2: BasicBlock)(bs1 bs2: BB_state),
  Bnrm (BB_list_sem (BBnow1 :: nil ++ BBs1 ++ BBnow2 :: nil ++ BBs2 )) bs1 bs2 ->
  bs1 <> bs2 ->
  BBnum_set (BBnow1 :: nil ++ BBs1) ∩ BBnum_set (BBnow2 :: nil ++ BBs2) == ∅ ->
  BBjmp_dest_set (BBnow1 :: nil ++ BBs1) ∩ BBjmp_dest_set (BBnow2 :: nil ++ BBs2) == ∅ ->
  bs1.(BB_num) ∈  BBnum_set (BBnow1 :: nil ++ BBs1) ->
  bs2.(BB_num) ∈  BBjmp_dest_set (BBnow2 :: nil ++ BBs2) ->
  (exists x,
  Bnrm (BB_list_sem (BBnow1 :: nil ++ BBs1)) bs1 x /\
  Bnrm (BB_list_sem (BBnow2 :: BBs2)) x bs2).
Proof.
  intros. 
  remember (BBnow1 :: nil ++ BBs1 ++ BBnow2 :: nil ++ BBs2) as BBs.
  pose proof BBs_list_sem_exists_BB_bs1_x BBs bs1 bs2 H. destruct H5.
  - my_destruct H5. subst BBs.
    assert (In x (BBnow1 :: nil ++ BBs1) \/ In x (BBnow2 :: nil ++ BBs2)). admit.
    clear H5.
    destruct H8.
    + exists x0. split. 
      * unfold BB_list_sem. cbn[Bnrm]. sets_unfold. exists (S O).
        cbn[Iter_nrm_BBs_n]. sets_unfold. exists x0. split.
        pose proof BB_sem_child_prop (x::nil) (BBnow1::nil ++ BBs1) bs1 x0. apply H8.
        -- intros. unfold In in H9. unfold In.  destruct H9.
           rewrite <- H9. unfold In in H5. destruct H5 as [? | ?].
           rewrite H9. rewrite H5. left. apply H9.
           right. apply H5. tauto.
        -- unfold BB_sem_union. cbn[Bnrm]. sets_unfold. left. apply H6.
        -- tauto.
      * pose proof BB_jmp_sem_num_in_BBjmp_dest_set.
        admit.
    + pose proof BB_sem_start_BB_num bs1 x0 x H6.
      sets_unfold in H1. specialize (H1 x.(block_num)). destruct H1.
      clear H9.
      assert (False). {
        apply H1. split. sets_unfold in H3. rewrite <- H8. apply H3.
        unfold BBnum_set. exists x. split. apply H5. tauto.
      }
      tauto.
  - contradiction.
  (*TODO! IMPORTANT! lyz*)
Admitted.

Lemma an_over_pass_bridge_reverse:
  forall (BBs1 BBs2: list BasicBlock)(bs1 bs2: BB_state),
  (exists x, Bnrm (BB_list_sem (BBs1)) bs1 x /\ Bnrm (BB_list_sem (BBs2)) x bs2) ->
  Bnrm (BB_list_sem (BBs1 ++ BBs2)) bs1 bs2.
Proof.
  intros. my_destruct H.
  unfold BB_list_sem. cbn[Bnrm]. sets_unfold.
  unfold BB_list_sem in H. cbn[Bnrm] in H. sets_unfold in H.
  unfold BB_list_sem in H0. cbn[Bnrm] in H0. sets_unfold in H0.
  my_destruct H. my_destruct H0. 
  induction x1.
  + pose proof BB_list_sem_child_prop BBs1 (BBs1 ++ BBs2) bs1 x.
    simpl in H0. sets_unfold in H0. rewrite H0 in H1. apply H1.
    intros. apply In_sublist_then_in_list_head. apply H2.
    rewrite H0 in H. unfold BB_list_sem. cbn[Bnrm]. sets_unfold.
    exists x0. apply H.
  + cbn[Iter_nrm_BBs_n] in H0.  


  (*TODO! IMPORTANT!*)
Admitted.