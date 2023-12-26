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

Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.
Import BDenote.

Ltac my_destruct H :=
  match type of H with 
  | exists _, _ => destruct H as [? H]; my_destruct H 
  | _ /\ _ => let H1:= fresh "H" in 
              destruct H as [H H1];my_destruct H; my_destruct H1
  | _ => idtac 
  end.

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


Definition BB_num_set := nat -> Prop.

Definition add_one_num (oldset: BB_num_set)(new: nat): BB_num_set :=
  fun BBnum => oldset BBnum \/ BBnum = new.

(*BBnum \in (nat \cap [BBnum_start, BBnum_end]) *)
Definition BBnum_start_end_set (BBnum_start: nat) (BBnum_end: nat): BB_num_set :=
  fun BBnum => Nat.le BBnum_start BBnum /\ Nat.le BBnum BBnum_end.

Definition BBnum_set (BBs: list BasicBlock): BB_num_set :=
  (* 拿到一串BBs里，所有出现的BBnum，包括block num和jmp dest num*)
  fun BBnum => exists BB, (In BB BBs) /\ BB.(block_num) = BBnum.

Definition BBjmp_dest_set (BBs: list BasicBlock): BB_num_set :=
  fun BBnum => exists BB, (In BB BBs) /\ (BB.(jump_info).(jump_dest_1) = BBnum \/ BB.(jump_info).(jump_dest_2) = Some BBnum).

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



(* Important !*)
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
  unfold BB_jmp_sem in H. simpl in H.
  unfold BBjmp_dest_set. sets_unfold. unfold In.
  exists BB. unfold BJump_sem in H.
  destruct eval_cond_expr.
  + split. left. tauto. right. destruct jump_dest_2. 
    - unfold cjmp_sem in H. simpl in H.
      destruct H as [[? [? [?| ?]]] ].
      ++ admit. (* 这是说If语句走Then分支的情况，没有用到dest2，缺条件 *)
      ++ destruct H1 as [? ?]. rewrite H1. tauto.
    - admit. (* 这里是Condition有的，但是却选择了UJmp的情况，应该是None，但是缺条件 *) 
  + split. left. tauto. left. unfold ujmp_sem in H. simpl in H. destruct H as [? [? [? ?]]]. rewrite H1. tauto. 
Admitted.


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


(*应该证明这个*)
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


  (*如果bs1的num不在BBs的num中，那bs1不能作为BBs语义的起点！*)
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
        -- pose proof (IHBBs H). destruct H0. exists x. destruct H0. split ;destruct H0.
          +++ left. tauto.
          +++ right. unfold In. right. tauto.
          +++ rewrite H1. tauto.
          +++ rewrite H1. tauto.
Qed.


(* #TODO  Check Qd *)
Definition Qd(c: cmd): Prop :=
    (* Qd: Q disjoint, 描述的是disjoint的性质 *)
    forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum :nat),  exists BBs' BBnow' (BBcmds: list BB_cmd),
      let res := cmd_BB_gen c BBs BBnow BBnum in
      let BBres := res.(BasicBlocks) ++ (res.(BBn) :: nil) in 

          match c with
            | CAsgn x e => (let BlockInfo' := BBnow.(jump_info) in
                                            BBnow'.(jump_info) = BlockInfo')
            | CIf e c1 c2 => (let BB_then_num := BBnum in
                   let BB_else_num := S(BB_then_num) in  (* 用哪个比较好？next_BB.(block_num)还是 BBnum？*)
                   let BlockInfo' := {|
                                        jump_kind := CJump;
                                        jump_dest_1 := BB_then_num;
                                        jump_dest_2 := Some (S(BB_then_num));
                                        jump_condition := Some e
                                      |} in
                                      BBnow'.(jump_info) = BlockInfo')
            | CWhile pre e body => (let BB_pre_num := BBnum in
                   let BB_body_num := S(BB_pre_num) in  (* 用哪个比较好？next_BB.(block_num)还是 BBnum？*)
                   let BlockInfo' := {|
                                        jump_kind := UJump;
                                        jump_dest_1 := BB_pre_num;
                                        jump_dest_2 := None;
                                        jump_condition := None
                                      |} in
                                      BBnow'.(jump_info) = BlockInfo') 
        end
     /\

    (*要拿到用于分配的下一个BBnum的信息*)

    BBnow'.(commands) = BBnow.(commands) ++ BBcmds /\ BBnow'.(block_num) = BBnow.(block_num) /\

    BBres = BBs ++ (BBnow' :: nil) ++ BBs' 

    /\  BBnum_set BBs' ⊆ BBnum_start_end_set BBnum res.(BBn).(block_num)
    (*新的BBs'的jmpnum在 Z \cap ([BBnum, BBn.(block_num)] \cup endinfo) *)
    /\ (BBjmp_dest_set BBs) ⊆ add_one_num (BBnum_start_end_set BBnum res.(BBn).(block_num)) (BBnow.(jump_info).(jump_dest_1)) 
    /\ (BBnum_set BBs' ∩ BBnum_set (BBs ++ BBnow'::nil)) = ∅ . 

Lemma disjoint_c:
  forall (c: cmd),
  Qd c.
Proof.
Admitted.
 

Definition Qb(c: cmd): Prop :=
  (* Qb: Q basic, 不包含disjoint的性质。Qb(Asgn)里面不能出现cmds, 或者说Q(c)里面你就要讲BBs等等变化前后有什么区别, 别去搞cmds，你们搞得那个反而把问题搞复杂了
    嗯，当然你要证明的是语义的变化，所以你要说多出来的commands的语义，和那个c的语义一样 -- by cqx *)
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum :nat), 
    let res := cmd_BB_gen c BBs BBnow BBnum in
    (*CAsgn*)
    (exists BBnow' BBcmd,
      res.(BBn) = BBnow' /\
      BBnow'.(commands) = BBnow.(commands) ++ (BBcmd :: nil) /\
      BCequiv (BAsgn_list_sem (BBcmd :: nil)) (cmd_sem c) BBnow'.(block_num) BBnow'.(block_num)) (*还在当下的BBnow里，BBnum则是下一个BB的编号，不能用*)
    \/
    (*CIf / CWhile*)
    (exists BBnow' BBs' BBnum' BBs_wo_last, 
      res.(BasicBlocks) ++ (res.(BBn) :: nil) =  BBs ++ (BBnow' :: nil) ++ BBs' /\ res.(BasicBlocks) =  BBs ++ (BBnow' :: nil) ++ BBs_wo_last /\
      res.(BBn).(block_num) = BBnum' /\
      BCequiv (BDenote_concate (BB_jmp_sem BBnow')(BB_list_sem BBs_wo_last)) (cmd_sem c) BBnow.(block_num) (S (S BBnum))). (* 这里的BBnum'是生成的BBlist的最后一个BB的编号，对于If和while，语义上都应该停留在next里！要和cmd_BB_gen中的BBnum做区分！ *)
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

Definition P(cmds: list cmd)(cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results): Prop :=
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum :nat),  exists BBs' BBnow' (BBcmds: list BB_cmd) BBnum' BBendnum,
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
    | next_BB :: _  => 
        (match cmds with
        | nil =>  BBnow'.(jump_info) = BBnow.(jump_info)
        | c :: tl =>
          (match c with
            | CAsgn x e => (let BlockInfo' := {|
                                              jump_kind := UJump;
                                              jump_dest_1 := next_BB.(block_num);
                                              jump_dest_2 := None;
                                              jump_condition := None
                                            |} in
                                            BBnow'.(jump_info) = BlockInfo')
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
        end)
    end /\

    (*要拿到用于分配的下一个BBnum的信息*)

    BBnum' = res.(next_block_num) /\

    BBnow'.(commands) = BBnow.(commands) ++ BBcmds /\ BBnow'.(block_num) = BBnow.(block_num) /\

    BBres = BBs ++ (BBnow' :: nil) ++ BBs' /\ BCequiv (ConcateBDenote) (cmd_list_sem cmd_sem cmds) BBnow'.(block_num) BBnow.(jump_info).(jump_dest_1) (*也就是endinfo*)

    /\ res.(BBn).(jump_info) = BBnow.(jump_info).