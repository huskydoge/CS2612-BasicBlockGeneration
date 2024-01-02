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
Require Import Coq.Program.Equality.
Require Import Main.BB_gen_properties.
Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.
Import BDenote.



Lemma true_or_false:
  forall (e: expr) (s: state),
  (exists (i : int64), (eval_expr e).(nrm) s i) ->
  (test_true_jmp (eval_expr e)) s \/ (test_false_jmp (eval_expr e)) s.
Proof.
  intros.
  destruct H.
  pose proof classic (Int64.signed x = 0).
  unfold test_true_jmp. unfold test_false_jmp.
  destruct H0.
  - right. rewrite <- H0. rewrite Int64.repr_signed. apply H.
  - left. exists x. split. apply H. apply H0.
Qed.

Lemma true_or_false_classic1:
  forall (e: expr) (s: state),
  (test_true_jmp (eval_expr e)) s -> ~ (test_false_jmp (eval_expr e)) s.
Proof.
  intros.
  unfold not. intros.
  unfold test_true_jmp in H. unfold test_false_jmp in H0.
  destruct H as [? [? ?]]. 
Admitted. 


Lemma true_or_false_classic2:
  forall (e: expr) (s: state),
  (test_false_jmp (eval_expr e)) s -> ~ (test_true_jmp (eval_expr e)) s.
Proof.
Admitted.


Lemma separate_sem_union_aux1:
  forall (BB: BasicBlock) (BBs: list BasicBlock),
  Bnrm (BB_sem_union (BB::nil ++ BBs)) = Bnrm (BB_sem BB) ∪ Bnrm (BB_sem_union BBs).
Proof.
  intros.
  sets_unfold. tauto.
Qed.

Lemma separate_sem_union_aux2:
  forall (BB: BasicBlock) (BBs: list BasicBlock) (bs1 bs2: BB_state),
  Bnrm (BB_sem BB) bs1 bs2 -> Bnrm (BB_sem_union (BB:: BBs)) bs1 bs2.
Proof.
  intros.
  sets_unfold. left. apply H.
Qed.

Lemma separate_sem_union_aux3:
  forall (BB: BasicBlock) (BBs: list BasicBlock) (bs1 bs2: BB_state),
  Bnrm (BB_sem_union BBs) bs1 bs2 -> Bnrm (BB_sem_union (BB:: BBs)) bs1 bs2.
Proof.
  intros.
  sets_unfold. right. apply H.
Qed.


Lemma separate_sem_union:
  forall (BBs1 BBs2: list BasicBlock), 
  Bnrm (BB_sem_union (BBs1 ++ BBs2)) ==  (Bnrm (BB_sem_union BBs1)) ∪ Bnrm (BB_sem_union BBs2).
Proof.
  intros.
  sets_unfold. split; intros.
  - induction BBs1.
    + simpl in H. sets_unfold in H. tauto.
    + assert ( Bnrm (BB_sem_union ((a1 :: BBs1) ++ BBs2)) = Bnrm (BB_sem_union (a1 ::nil ++ BBs1 ++ BBs2))).
    {
      reflexivity.
    }
    rewrite H0 in H.
    pose proof (separate_sem_union_aux1 a1 (BBs1 ++ BBs2)).
    rewrite H1 in H. sets_unfold in H.
    destruct H.
    * left. pose proof separate_sem_union_aux2 a1 BBs1 a a0 H. tauto.
    * pose proof IHBBs1 H.
      destruct H2.
      ++ pose proof separate_sem_union_aux3 a1 BBs1 a a0 H2.
          left. tauto.
      ++ right. tauto.
  - induction BBs1.
    + simpl. sets_unfold. tauto.
    + assert ( Bnrm (BB_sem_union ((a1 :: BBs1) ++ BBs2)) = Bnrm (BB_sem_union (a1 ::nil ++ BBs1 ++ BBs2))).
    {
      reflexivity.
    }
    destruct H. 
    * destruct H.
      -- pose proof separate_sem_union_aux2 a1 (BBs1++BBs2) a a0 H.
          rewrite H0. tauto.
      -- assert (Bnrm (BB_sem_union BBs1) a a0 \/ Bnrm (BB_sem_union BBs2) a a0).
      {
      left. tauto.
      }
      pose proof IHBBs1 H1.
      rewrite H0. pose proof separate_sem_union_aux3 a1 (BBs1++BBs2) a a0 H2.
      tauto.
    * assert (Bnrm (BB_sem_union BBs1) a a0 \/ Bnrm (BB_sem_union BBs2) a a0).
    {
    right. tauto.
    }
    pose proof IHBBs1 H1.
    rewrite H0. pose proof separate_sem_union_aux3 a1 (BBs1++BBs2) a a0 H2.
    tauto.
Qed.

(*
如果满足几条分离性质，那么有
  (start, s1), (end, s2) \in (I U ((R1 U R234) o (R1 U R234))*  -> (start, s1), (end, s2) \in (R1 o (R234)*
**)
Lemma separate_step_aux1:
  forall (bs1 bs2: BB_state)(BBnow: BasicBlock)(BBs: list BasicBlock),

  separate_property BBnow BBs -> (* BBnow 不在 (BBnow :: BBs) 的跳转目标里 *)

  BB_restrict BBnow BBs bs1.(BB_num) bs2.(BB_num)-> (* BBnow的num是bs1.(BB_num), BBs的跳转目标中有bs2.(BBnum)*)

  (( Rels.id ∪ (BB_sem_union (BBnow::nil ++ BBs)).(Bnrm) ∘ (BB_list_sem (BBnow::nil ++ BBs)).(Bnrm)) bs1 bs2 :Prop)
  ->
    ((BB_sem BBnow).(Bnrm) ∘ (BB_list_sem (BBs)).(Bnrm)) bs1 bs2 : Prop.
Proof.
  intros.
  unfold BB_list_sem. cbn [Bnrm].
  unfold BB_list_sem in H1. cbn [Bnrm] in H1.
  cbn [BB_sem_union] in H1. cbn [Bnrm] in H1.
  unfold separate_property in H.
  destruct H1.
  - sets_unfold in H1. unfold BB_restrict in H0. destruct H0 as [? ?].
    sets_unfold in H. specialize (H bs1.(BB_num)). destruct H as [? ?].
    clear H3.
    assert (BBnum_set (BBnow :: nil) (BB_num bs1) /\ BBjmp_dest_set (BBnow :: BBs) (BB_num bs1)). {
      unfold BBnum_set. split. exists BBnow. split.
      unfold In. left. tauto. rewrite <- H0. tauto.
      rewrite H1. unfold BBjmp_dest_set. unfold BBjmp_dest_set in H2.
      destruct H2 as [[? [? [? | ?]]] ?].
      + exists x. split.
        * unfold In. right. tauto.
        * left. apply H3.
      + exists x. split.
        * unfold In. right. tauto.
        * right. apply H3.
    }
    apply H in H3. tauto.
  - apply sem_start_end_with in H1. destruct H1 as [bs' [? ?]].
    destruct H1.
    (*你先处理H1，然后由此可以得到x的性质，然后归纳证明，从x出发n步到达的不能是起始BBnum，这样就可以把BBnow给排除了*)
    + sets_unfold. exists bs'. split. apply H1.
      destruct H2 as [n H2]. exists n.
      assert (BB_num bs' <> BB_num bs1). {
        pose proof BB_sem_num_change bs1 bs' BBnow BBs.
        unfold not. intros.
        apply H3. unfold separate_property. apply H. 
        destruct H0 as [? ?].
        apply H0. apply H1. rewrite H4. tauto.
      }
      unfold BB_restrict in H0. destruct H0. clear H4 H1.
      revert bs' H2 H3. induction n; intros.
      * intros. simpl in H2. simpl. apply H2.
      * (*拆出H2，从bs'走一步到bs'',再从bs''到bs2*) 
        unfold Iter_nrm_BBs_n in H2. apply sem_start_end_with in H2.
        destruct H2 as [bs'' [? ?]]. destruct H1.
        --- pose proof BB_sem_start_BB_num bs' bs'' BBnow. 
            rewrite H0 in H3. apply H4 in H1. rewrite H1 in H3. unfold not in H3. assert (BBnow.(block_num) = BBnow.(block_num)). tauto. apply H3 in H5. tauto.
        --- assert (BB_num bs'' <> BB_num bs1). {
              induction BBs.
              - simpl in H1. sets_unfold in H1. tauto.
              - assert (a::BBs <> nil). {
                  unfold not. intros. discriminate.
                }
                assert (bs' <> bs''). {
                  unfold not. intros. rewrite H5 in H1. simpl in H1.
                  apply different_bs_after_BBsem_union in H1. tauto.
                  
                }
                pose proof BBs_sem_num_not_BB_sem_num bs1 bs' bs'' BBnow (a::BBs).
                unfold separate_property in H6.
                pose proof (H6 H4 H H0 H1 H5).
                apply H7.
            }
            pose proof IHn bs'' H2 H4.
            pose proof iter_concate.
            specialize (H6 (Bnrm (BB_sem_union (nil ++ BBs))) (Iter_nrm_BBs_n (BB_sem_union BBs) n) bs' bs'' bs2).
            pose proof (H6 H1 H5). simpl in H7. apply H7.
    + unfold BB_restrict in H0.
      pose proof cannot_start_with. specialize (H3 bs1 bs' (nil ++ BBs)).
      assert (~ BBnum_set (nil ++ BBs) (BB_num bs1)). {
        unfold not. intros. destruct H0 as [? [? ?]].
        assert (BB_num bs1 ∈ BBnum_set (nil ++ BBs)). {
          sets_unfold. apply H4.
        }

        assert (BB_num bs1 ∈ BBnum_set (BBnow :: nil)). {
          rewrite H0. unfold BBnum_set. sets_unfold.
          exists BBnow. unfold In. split. left. tauto. tauto.
        }
        
        assert (BB_num bs1 ∈ BBnum_set (BBnow :: nil) ∩ BBnum_set (BBs)). {
          split. sets_unfold in H8. apply H8. apply H4.
        }
        
        sets_unfold in H6. sets_unfold in H9.
        specialize (H6 bs1.(BB_num)). destruct H6 as [? ?]. clear H10.
        apply H6. apply H9. 
      }
      pose proof (H3 H4 H1). tauto. (*这里是说BBnow的jmpdest里有bs2，但是bs1和bs2不相等，所以不可能是BBnow的jmpdest*)
            
Qed.


Lemma BBs_sem_included: 
  forall (BBnow : BasicBlock) (BBs : list BasicBlock) (bs1 bs2: BB_state),
    (Bnrm (BB_list_sem (BBs))) bs1 bs2 -> (Bnrm (BB_list_sem (BBnow :: nil ++ BBs))) bs1 bs2.
Proof.
  intros.
  unfold BB_list_sem. cbn[Bnrm].
  unfold BB_list_sem in H. cbn[Bnrm] in H.
  unfold Iter_nrm_BBs_n. sets_unfold.
  unfold Iter_nrm_BBs_n in H. sets_unfold in H.
  destruct H as [? ?]. exists x.
  revert bs1 H.
  induction x; intros.
  - apply H.
  - destruct H as [? [? ?]]. exists x0.
    specialize (IHx x0).
    pose proof IHx H0. split.
    + unfold BB_sem_union. cbn[Bnrm].
      unfold BB_sem_union in H. cbn[Bnrm] in H.
      sets_unfold. right. apply H.
    + apply H1. 
Qed.


Lemma separate_step_aux2:
  forall (bs1 bs2: BB_state)(BBnow: BasicBlock)(BBs: list BasicBlock),
  (((BB_sem BBnow).(Bnrm) ∘ (BB_list_sem (BBs)).(Bnrm)) bs1 bs2 : Prop)
  ->
  (( Rels.id ∪ (BB_sem_union (BBnow :: nil ++ BBs)).(Bnrm) ∘ (BB_list_sem (BBnow :: nil ++ BBs)).(Bnrm)) bs1 bs2 : Prop).
Proof.
  intros.
  sets_unfold. sets_unfold in H. destruct H as [? [? ?]].
  right. unfold BB_sem_union. cbn[Bnrm]. exists x.
  sets_unfold. repeat split.
  - left. apply H.
  - pose proof BBs_sem_included BBnow BBs x bs2.
    pose proof H1 H0.
    apply H2.
Qed.

(* 如果一个nat在BBnum_set (BBs1 ++ BBs2)中，那么它一定在BBs1中或BBs2中 *)
Lemma in_add_means_in_cup:
  forall (BBs1 BBs2 : list BasicBlock) (n: nat),
  BBnum_set (BBs1 ++ BBs2) (n) -> BBnum_set (BBs2) (n) \/ BBnum_set (BBs1) n.
Proof.
  intros. unfold BBnum_set. unfold BBnum_set in H. destruct H as [? [? ?]].
  apply in_app_iff in H. destruct H.
  - right. exists x. tauto.
  - left. exists x. tauto.
Qed.


Lemma BB_start_in_BBs_if_Bnrm:
  forall (BBs : list BasicBlock) (bs1 bs2: BB_state),
    ((Bnrm (BB_sem_union BBs) bs1 bs2) : Prop) ->  BBnum_set BBs (BB_num bs1).
Proof.
  intros.
  induction BBs.
  - simpl in H. sets_unfold in H. tauto.
  - destruct H.
    + unfold BBnum_set. exists a. split. unfold In. left. tauto.
      pose proof BB_sem_start_BB_num bs1 bs2 a.
      pose proof H0 H. rewrite H1. tauto.
    + apply IHBBs in H. unfold BBnum_set. unfold BBnum_set in H.
      destruct H as [? [? ?]]. 
      exists x. split. unfold In. right. apply H. apply H0.
Qed.




Lemma BB_dest_in_BBs_jmp_dest_set:
  forall (BBs : list BasicBlock) (bs1 bs2 : BB_state),
     BBnum_set BBs (BB_num bs1) -> ((Bnrm (BB_sem_union BBs) bs1 bs2) : Prop) -> BBjmp_dest_set BBs (BB_num bs2).
Proof.
  intros. revert bs1 H H0.
  induction BBs; intros. 
  - simpl in H0. sets_unfold in H0. tauto.
  - assert ( bs2.(BB_num) ∈ BBjmp_dest_set (a :: nil) \/ bs2.(BB_num) ∈ BBjmp_dest_set BBs). {
      unfold BB_sem_union in H0. cbn[Bnrm] in H0.
      sets_unfold in H0. destruct H0 as [? | ?].
      - left. sets_unfold. unfold BBnum_set.
        unfold BB_sem in H0. cbn[Bnrm] in H0.
        sets_unfold in H0. destruct H0 as [? [? ?]]. unfold BBjmp_dest_set.
        exists a. split. unfold In. left. tauto.
        unfold BB_jmp_sem in H1. cbn[Bnrm] in H1.
        unfold BJump_sem in H1. destruct ( eval_cond_expr (jump_condition a.(jump_info))); destruct (jump_dest_2 a.(jump_info)).
        -- unfold cjmp_sem in H1. cbn [Bnrm] in H1. my_destruct H1. destruct H4. 
           ++ destruct H4. left. rewrite H4. reflexivity.
           ++ destruct H4. right. rewrite H4. reflexivity.
        -- unfold ujmp_sem in H1. cbn [Bnrm] in H1. my_destruct H1. left. rewrite H3. reflexivity.
        -- unfold ujmp_sem in H1. cbn [Bnrm] in H1. my_destruct H1. left. rewrite H3. reflexivity.
        -- unfold ujmp_sem in H1. cbn [Bnrm] in H1. my_destruct H1. left. rewrite H3. reflexivity.     
      - specialize (IHBBs bs1). 
        unfold BBnum_set in H. destruct H as [? [? ?]].
        unfold In in H. destruct H as [? | ?].
        + pose proof BB_start_in_BBs_if_Bnrm BBs bs1 bs2.
          pose proof H2 H0. pose proof IHBBs H3 H0. tauto.
        + right. sets_unfold. apply IHBBs. 
          unfold BBnum_set. exists x. split. apply H. apply H1. apply H0.
    }
    unfold BBnum_set.
    destruct H1.
    + sets_unfold in H1. unfold BBnum_set in H1.
      destruct H1 as [? [? ?]]. exists x. split.
      unfold In. left. unfold In in H1. destruct H1. apply H1. tauto. apply H2.
    + sets_unfold in H1. unfold BBnum_set in H1.
      destruct H1 as [? [? ?]]. exists x. split.
      unfold In. right. unfold In in H1. apply H1. apply H2.
Qed.


Lemma BB_dest_in_BBsA_if_BBsA_BBsB_independent: 
  forall (BBs1 BBs2: list BasicBlock) (bs1 bs2: BB_state),
  Bnrm (BB_sem_union (BBs1 ++ BBs2)) bs1 bs2 -> BBnum_set BBs1 (BB_num bs1) -> ~ BBnum_set BBs2 (BB_num bs1) -> BBjmp_dest_set BBs1 (BB_num bs2).
Proof.
  intros.
  pose proof BB_dest_in_BBs_jmp_dest_set (BBs1) bs1 bs2 H0.
  pose proof separate_sem_union BBs1 BBs2.
  apply H3 in H.
  sets_unfold in H.
  destruct H.
  - pose proof H2 H. tauto.
  - pose proof cannot_start_with bs1 bs2 BBs2 H1 H. tauto.
Qed.



(*
如果：
1. (bs1,bs2)在BBs1++BBs2的语义里
2. bs1不在BBs2中
=> 那么bs2在BBs1的jump目标中
*)
Lemma BB_num_change_from_BBsA_to_BBsB:
  forall (BBs1 BBs2 : list BasicBlock) (bs1 bs2: BB_state),
    ((Bnrm (BB_sem_union (BBs1 ++ BBs2)) bs1 bs2) : Prop) -> not (BBnum_set BBs2 (BB_num bs1)) -> BBjmp_dest_set BBs1 (BB_num bs2).
Proof.
  intros. unfold not in H0.
  pose proof cannot_start_with bs1 bs2 (BBs1 ++ BBs2).

  assert (BBnum_set BBs1 (BB_num bs1)). {
    pose proof classic (~ BBnum_set BBs1 (BB_num bs1)). destruct H2.
    - unfold not in H2. 
      assert (~ BBnum_set (BBs1 ++ BBs2) (BB_num bs1)). {
        unfold not. intros. apply in_add_means_in_cup in H3. 
        destruct H3. tauto. tauto.
      }
      pose proof H1 H3 H. tauto.
    - tauto. 
  }
  clear H1.
  pose proof BB_dest_in_BBsA_if_BBsA_BBsB_independent BBs1 BBs2 bs1 bs2.
  apply H1. apply H. apply H2. unfold not. apply H0.
Qed.


(*
对于两个BBlist，如果:
1. BBs1和BBs2不交
2. bs1不在BBs2中
3. BBs1中的block跳不到BBs2中
4. (bs1,bs2)在BBs1++BBs2的语义里
=> 那么bs2不在BBs2中
*)
Lemma BBs1_num_not_in_BBs2: 
  forall (BBs1 BBs2: list BasicBlock)(bs1 bs2: BB_state),
  (BBnum_set BBs1) ∩ (BBnum_set BBs2) == ∅ ->
  not (BBnum_set BBs2 (BB_num bs1))->
  (BBjmp_dest_set BBs1) ∩ (BBnum_set BBs2) == ∅ ->
  ((Bnrm (BB_sem_union (BBs1 ++ BBs2)) bs1 bs2) : Prop) 
  -> not (BBnum_set BBs2 (BB_num bs2)).
Proof.
  intros. sets_unfold.
  assert(BBjmp_dest_set BBs1 (BB_num bs2)).
  {
    unfold BB_sem_union in H2.
    pose proof BB_num_change_from_BBsA_to_BBsB BBs1 BBs2 bs1 bs2.
    pose proof H3 H2 H0. apply H4.
  }
  unfold not. intros.
  sets_unfold in H1. specialize (H1 (BB_num bs2)).
  destruct H1 as [? ?]. clear H5. apply H1.
  split. apply H3. apply H4.
Qed.


(*
对于一串BBs和两个BBstate, 如果：
1. bs1不在BBs中
2. (bs1,bs2)在BBs的语义里
=> 那么矛盾！！！
*)
Lemma BB_start_not_in_BBs_if_no_num_set: 
  forall (BBs : list BasicBlock) (bs1 bs2 : BB_state),
    ~ BBnum_set BBs (BB_num bs1) -> Bnrm (BB_sem_union BBs) bs1 bs2 -> False.
Proof.
  intros. unfold not in H. apply H.
  induction BBs.
  - simpl in H0. sets_unfold in H0. tauto.
  - unfold BBnum_set. unfold BB_sem_union in H0. sets_unfold in H0.
    cbn[Bnrm] in H0. destruct H0 as [? | ?].
    + exists a. split. unfold In. left. tauto.
      pose proof BB_sem_start_BB_num bs1 bs2 a. pose proof H1 H0. rewrite H2. tauto.
    + unfold BBnum_set in IHBBs.
      assert (BBnum_set BBs (BB_num bs1)). {
        apply IHBBs.
        - intros. destruct H1 as [? [? ?]]. apply H. unfold BBnum_set.
          exists x. unfold In. unfold In in H1. split. right. apply H1. apply H2.
        - apply H0.  
      }
      unfold BBnum_set in H1. destruct H1 as [? [? ?]].
      exists x. unfold In. unfold In in H1. split. right. apply H1. apply H2.
Qed.


(* 切第二刀，把then和else切开来*)
Lemma separate_step_aux3:
  forall (BBs1 BBs2: list BasicBlock)(bs1 bs2: BB_state),
  (BBnum_set BBs1) ∩ (BBnum_set BBs2) == ∅ ->
  not ((BB_num bs1) ∈ (BBnum_set BBs2))  ->
  (BBjmp_dest_set BBs1) ∩ (BBnum_set BBs2) == ∅ ->
  (BB_num bs2) ∈ (BBjmp_dest_set BBs1) ->
  Bnrm (BB_list_sem (BBs1 ++ BBs2)) bs1 bs2 ->
  Bnrm (BB_list_sem (BBs1)) bs1 bs2.
Proof.
  unfold BB_list_sem. simpl. intros.
  sets_unfold in H3.
  sets_unfold.
  destruct H3.
  exists x. revert bs1 H0 H3.
  induction x; intros.
  - tauto.
  - assert (forall (BBs: list BasicBlock), Iter_nrm_BBs_n (BB_sem_union (BBs)) (S x) =(Bnrm (BB_sem_union (BBs))   ∘ Iter_nrm_BBs_n (BB_sem_union (BBs)) (x))).
  {
    reflexivity.
  }
  rewrite H4 in H3.
  pose proof sem_start_end_with (Bnrm (BB_sem_union (BBs1 ++ BBs2))) (Iter_nrm_BBs_n (BB_sem_union (BBs1 ++ BBs2)) x) bs1 bs2 H3.
  rewrite H4.
  pose proof sem_start_end_with_2 (Bnrm (BB_sem_union BBs1)) (Iter_nrm_BBs_n (BB_sem_union BBs1) x) bs1 bs2.
  apply H6. (*?????*)
  clear H6 H3 H4.
  destruct H5. destruct H3 as [? ?].
  exists x0.
  split.
  ++ pose proof separate_sem_union BBs1 BBs2.
     specialize (H5 bs1 x0). destruct H5 as [? ?]. clear H6.
     pose proof H5 H3. sets_unfold in H6. destruct H6 as [? | ?]. apply H6.
     pose proof BB_start_not_in_BBs_if_no_num_set BBs2 bs1 x0.
     pose proof H7 H0 H6. tauto.
  ++ specialize (IHx x0). 
     apply IHx.
     -- pose proof BBs1_num_not_in_BBs2 BBs1 BBs2 bs1 x0.
        pose proof H5 H H0 H1 H3.
        apply H6.
     -- apply H4. 
Qed.



Lemma BB_true_jmp_iff_test_true_jmp:
  forall (e: expr) (a: state),
  (test_true_jmp (eval_expr e)) a <-> (test_true (eval_expr e)) a a.
Proof.
  intros.
  split.
  - unfold test_true_jmp. unfold test_true.
    intros. destruct H as [i [? ?]]. sets_unfold. split.
    + exists i. split.
      * apply H.
      * apply H0.
    + reflexivity.
  - unfold test_true_jmp. unfold test_true.
    intros. sets_unfold in H. my_destruct H. exists x. split.
      * apply H.
      * apply H1.
Qed.


Lemma BB_false_jmp_iff_test_false_jmp:
  forall (e: expr) (a: state),
  (test_false_jmp (eval_expr e)) a <-> (test_false (eval_expr e)) a a.
Proof.
  intros.
  split.
  - unfold test_false_jmp. unfold test_false.
    intros. sets_unfold. split; try tauto.
  - unfold test_false_jmp. unfold test_false.
    intros. sets_unfold in H. destruct H as [? ?]. apply H.
Qed.


Lemma Iter_sem_union_sem_included: 
  forall (BBnow: BasicBlock) (BBs: list BasicBlock) (bs1 bs2: BB_state) (x0: nat),
    Iter_nrm_BBs_n (BB_sem_union BBs) x0 bs1 bs2 -> Iter_nrm_BBs_n (BB_sem_union (BBnow :: BBs)) x0 bs1 bs2.
Proof.
  intros. revert bs1 H.
  induction x0; intros.
  - simpl in H. simpl. apply H.
  - unfold Iter_nrm_BBs_n in H. sets_unfold in H. destruct H as [? [? ?]]. 
    unfold Iter_nrm_BBs_n. sets_unfold. exists x. split.
    -- simpl. right. apply H.
    -- specialize (IHx0 x). apply IHx0. apply H0. 
Qed.



(*IMPORTANT*)
(* 对于所有的BBnow，BBs，和两个BBstate，如果：
1. BBnow和BBs满足分离性质 (separate_property)
2. BBnow BBs bs1.(BB_num) bs2.(BB_num) 满足限制条件 (BB_restrict)
3. 那么如果我创建一个新的BBnow'，将BBnow的jmp语义复制后，我可以做等价变换
((BDenote_concate (BB_jmp_sem BBnow) (BB_list_sem BBs)).(Bnrm) bs1 bs2) <-> (BB_list_sem (BBnow' :: nil ++ BBs)).(Bnrm) bs1 bs2.
*)
Lemma BDenote_concat_equiv_BB_list_sem:
  forall (BBnow : BasicBlock) (BBs : list BasicBlock)(bs1 bs2: BB_state),
    separate_property BBnow BBs -> 
    BB_restrict BBnow BBs bs1.(BB_num) bs2.(BB_num)-> (* BBnow的num是bs1.(BB_num), BBs的跳转目标中有bs2.(BBnum)*)
    let BBnow' := {|
      block_num := BBnow.(block_num);
      commands := nil;
      jump_info := BBnow.(jump_info);
    |} in
    ((BDenote_concate (BB_jmp_sem BBnow) (BB_list_sem BBs)).(Bnrm) bs1 bs2) <-> (BB_list_sem (BBnow' :: nil ++ BBs)).(Bnrm) bs1 bs2.
Proof.
  intros.
  assert (BBnum_set (BBnow' :: nil) == BBnum_set (BBnow :: nil)). {
  unfold BBnum_set. unfold BBnum_set. sets_unfold. split; intros.
  - exists BBnow. split. simpl. tauto. my_destruct H1. simpl in H1. destruct H1.
    + rewrite <- H1 in H2. unfold BBnow' in H2. simpl in H2. tauto.
    + tauto.
  - exists BBnow'. split. simpl. tauto. my_destruct H1. simpl in H1. destruct H1.
    + rewrite <- H1 in H2. unfold BBnow' in H2. simpl in H2. tauto.
    + tauto.
  }
  assert (BBjmp_dest_set (BBnow' :: BBs) == BBjmp_dest_set (BBnow :: BBs)). {
  unfold BBjmp_dest_set. unfold BBjmp_dest_set. sets_unfold. split; intros.
  - my_destruct H2. simpl in H2. destruct H2.
    + rewrite <- H2 in H3. unfold BBnow' in H3. simpl in H3. exists BBnow.
      split. simpl. tauto. apply H3.
    + exists x. split. simpl. tauto. apply H3.
  - my_destruct H2. simpl in H2. destruct H2.
    + rewrite <- H2 in H3. unfold BBnow' in H3. simpl in H3. exists BBnow'. split.
      simpl. tauto. apply H3.
    + exists x. split. simpl. tauto. apply H3.
  }
  assert (separate_property BBnow' BBs). {
    unfold separate_property. unfold separate_property in H.
    rewrite  H1. rewrite H2. apply H.
  }
  assert (BB_restrict BBnow' BBs (BB_num bs1) (BB_num bs2)
  ). {
    unfold BB_restrict. unfold BB_restrict in H0. destruct H0 as [? ?].
    split.
    - apply H0.
    - split. destruct H4 as [? ?]. apply H4. destruct H4. rewrite <- H1 in H5.
      apply H5.
  }
  pose proof separate_step_aux1 bs1 bs2 BBnow' BBs H3 H4.
  pose proof unfold_once (BBnow' :: nil ++ BBs).
  assert ((Bnrm (BB_list_sem (BBnow' :: nil ++ BBs)) bs1 bs2) <->
  (Rels.id ∪ Bnrm (BB_sem_union (BBnow' :: nil ++ BBs)) ∘ Bnrm (BB_list_sem (BBnow' :: nil ++ BBs)))
  bs1 bs2). {
    specialize (H6 bs1 bs2).
    sets_unfold in H6. 
    split.
    - destruct H6 as [? ?].
      clear H7. intros. pose proof H6 H7. destruct H8 as [? | ?].
      + sets_unfold. left. apply H8.
      + sets_unfold. right. apply H8.
    - intros. pose proof H5 H7. clear H5.
      unfold BB_list_sem. cbn[Bnrm].
      sets_unfold in H8. destruct H8 as [? [? ?]].
      unfold BB_restrict in H4. destruct H4 as [? [? ?]].
      unfold BB_list_sem in H8. destruct H8 as [? ?].
      (* ! 可以注意一下下边的操作，这里要看出来是S x0 *)
      sets_unfold. exists (S x0). simpl.
      sets_unfold. exists x. split. 
      + left. exists bs1. split. tauto. 
        unfold BB_sem in H5. cbn[Bnrm] in H5. unfold BB_cmds_sem in H5.
        simpl in H5. sets_unfold in H5. destruct H5 as [? [? ?]].
        rewrite <- H5 in H11. apply H11.
      + (* 这里必须clear H5 *)
        clear H5. revert x H8.
        induction x0; intros.
        simpl. simpl in H8. apply H8.
        unfold Iter_nrm_BBs_n in H8. sets_unfold in H8. destruct H8 as [? [? ?]]. 
        unfold Iter_nrm_BBs_n. sets_unfold. exists x1. split.
        -- simpl. right. apply H5.
        -- specialize (IHx0 x1). apply IHx0. apply H8.
  }
  
  rewrite H7. clear H5 H6 H7. split.
  - intros. sets_unfold.
    unfold BDenote_concate in H5. cbn[Bnrm] in H5.
    sets_unfold in H5. right. destruct H5 as [? [? ?]].
    exists x. split.
    + unfold BB_sem_union. cbn[Bnrm]. sets_unfold. left. unfold BB_sem.
      cbn[Bnrm]. sets_unfold. exists bs1. 
      subst BBnow'. simpl. split. sets_unfold. tauto.
      unfold BB_jmp_sem in H5. cbn[Bnrm] in H5. apply H5.
    + unfold BB_list_sem. cbn[Bnrm]. unfold BB_list_sem in H6. cbn[Bnrm] in H6.
      sets_unfold. sets_unfold in H6. destruct H6 as [? ?].
      exists x0. pose proof Iter_sem_union_sem_included BBnow' BBs x bs2 x0. simpl. apply H7. apply H6.
  - intros. sets_unfold in H5. destruct H5 as [? | ?].
    rename H5 into eq.
    + unfold BDenote_concate. cbn[Bnrm]. sets_unfold. exists bs1.
      rename H4 into contradict_point.
      rename H3 into contradict_point1. 
      unfold BB_restrict in contradict_point. destruct contradict_point as [p1 [p2 p3]].
      unfold separate_property in contradict_point1. sets_unfold in contradict_point1.
      specialize (contradict_point1 bs1.(BB_num)). 
      assert (contra_pre: BBnum_set (BBnow' :: nil) (BB_num bs1) /\ BBjmp_dest_set (BBnow' :: BBs) (BB_num bs1)).
      {
        split.
        + unfold BBnum_set. exists BBnow'. split. simpl. tauto. rewrite p1. tauto.
        + rewrite eq. unfold BBjmp_dest_set in p2. destruct p2 as [var [cond1 cond2]].
          unfold BBjmp_dest_set. exists var. split.
          *  simpl. tauto. 
          * tauto.
      }
      tauto.
    + unfold BDenote_concate. cbn[Bnrm]. sets_unfold. destruct H5 as [? [? ?]].
      exists x. 
      sets_unfold in H5. destruct H5 as [? | ?].
      -- split. unfold BB_sem in H5. cbn[Bnrm] in H5. sets_unfold in H5.
         destruct H5 as [? [? ?]].
         assert (x0 = bs1). {
           subst BBnow'. simpl in H5. sets_unfold in H5. rewrite H5. tauto.
         }
         rewrite H8 in H7. unfold BB_jmp_sem in H7. subst BBnow'. simpl in H7. unfold BB_jmp_sem. apply H7. 
         (* 这里x其实已经不在BBnow'中而在BBs中了，需要以此来缩小H6的范围 *)
         unfold separate_property in H3.
         admit.
      -- unfold BB_restrict in H4. destruct H4 as [key1 [key2 key3]].
         (* bs1的num等于BBnow'的num，但是BBnow'的num和BBs的num不相交，
            所以不可能有办法，让bs1从BBs的语义出发 *)
         pose proof cannot_start_with bs1 x (nil ++ BBs).
         assert (pre1: ~ BBnum_set (nil ++ BBs) (BB_num bs1)).
          {
            unfold not. intros. sets_unfold in key3. specialize (key3 (BB_num bs1)).
            assert (contra: BBnum_set (BBnow' :: nil) (BB_num bs1) /\ BBnum_set BBs (BB_num bs1)). {
              split.
              - unfold BBnum_set. exists BBnow'. split. simpl. tauto. rewrite key1. tauto.
              - tauto.
            }
            tauto.
          }
          tauto.
Admitted.


(*对于一个CJump的BB，它的jmp语义要么true jmp要么false jmp| 两个destination 择一*)
Lemma BB_jmp_sem_simplify:
  forall (BB: BasicBlock) (bs1 bs2: BB_state)(e: expr)(dest1 dest2: nat),
  BB.(jump_info) = 
  {|
  jump_kind := CJump;
  jump_dest_1 := dest1;
  jump_dest_2:= Some dest2;
  jump_condition:= Some e
  |} /\
  (BB_jmp_sem BB).(Bnrm) bs1 bs2  ->
  ((
  test_true_jmp (eval_expr e) bs1.(st) /\ bs2.(st) = bs1.(st) /\ bs2.(BB_num) = BB.(jump_info).(jump_dest_1) 
  \/ 
  test_false_jmp (eval_expr e) bs1.(st) /\  bs2.(st) = bs1.(st) /\ Some bs2.(BB_num) = BB.(jump_info).(jump_dest_2))).
Proof.
  intros.
  pose proof true_or_false.
  specialize (H0 e (bs1).(st)).
  assert ((exists i : int64, EDenote.nrm (eval_expr e) (st bs1) i)). {
  pose proof No_err_and_inf_for_expr e bs1. tauto.
  } 
  destruct H0.
  - apply H1.
  - left. split; destruct H.
    + apply H0.
    + split. unfold BB_jmp_sem in H2. cbn[Bnrm] in H2. unfold BJump_sem in H2.
      rewrite H in H2. simpl in H2. 
      assert ((match e with
      | EBinop op e1 e2 => Some (binop_sem op (element_sem e1) (element_sem e2))
      | EUnop op e1 => Some (unop_sem op (element_sem e1))
      end) <> None). {
        destruct e.
        - discriminate.
        - discriminate.
      }
      destruct (     
      match e with
      | EBinop op e1 e2 => Some (binop_sem op (element_sem e1) (element_sem e2))
      | EUnop op e1 => Some (unop_sem op (element_sem e1))
      end).
      * unfold cjmp_sem in H2. cbn [Bnrm] in H2. my_destruct H2.
        -- rewrite H2. reflexivity.
      * tauto.
      * unfold BB_jmp_sem in H2. cbn [Bnrm] in H2. rewrite H. cbn [jump_dest_1].
        unfold BJump_sem in H2. rewrite H in H2. simpl in H2. 
        assert ((match e with
        | EBinop op e1 e2 => Some (binop_sem op (element_sem e1) (element_sem e2))
        | EUnop op e1 => Some (unop_sem op (element_sem e1))
        end) <> None). {
          destruct e.
          - discriminate.
          - discriminate.
        }
        destruct e.
        -- unfold cjmp_sem in H2. cbn [Bnrm] in H2. my_destruct H2. destruct H6.
           ++ destruct H6. rewrite H6. reflexivity.
           ++ destruct H6.
              pose proof true_or_false_classic1 (EBinop op e1 e2) bs1.(st).
              pose proof H8 H0. contradiction.
        -- unfold cjmp_sem in H2. cbn [Bnrm] in H2. my_destruct H2. destruct H6.
           ++ destruct H6. rewrite H6. reflexivity.
           ++ destruct H6.
              pose proof true_or_false_classic1 (EUnop op e1) bs1.(st).
              pose proof H8 H0. contradiction.
  - right. split; destruct H.
    + apply H0.
    + split. unfold BB_jmp_sem in H2. cbn[Bnrm] in H2. unfold BJump_sem in H2.
      rewrite H in H2. simpl in H2. 
      assert ((match e with
      | EBinop op e1 e2 => Some (binop_sem op (element_sem e1) (element_sem e2))
      | EUnop op e1 => Some (unop_sem op (element_sem e1))
      end) <> None). {
        destruct e.
        - discriminate.
        - discriminate.
      }
      destruct (     
      match e with
      | EBinop op e1 e2 => Some (binop_sem op (element_sem e1) (element_sem e2))
      | EUnop op e1 => Some (unop_sem op (element_sem e1))
      end).
      * unfold cjmp_sem in H2. cbn [Bnrm] in H2. my_destruct H2.
        -- rewrite H2. reflexivity.
      * tauto.
      * unfold BB_jmp_sem in H2. cbn [Bnrm] in H2. rewrite H. cbn [jump_dest_1].
        unfold BJump_sem in H2. rewrite H in H2. simpl in H2. 
        assert ((match e with
        | EBinop op e1 e2 => Some (binop_sem op (element_sem e1) (element_sem e2))
        | EUnop op e1 => Some (unop_sem op (element_sem e1))
        end) <> None). {
          destruct e.
          - discriminate.
          - discriminate.
        }
        destruct e.
        -- unfold cjmp_sem in H2. cbn [Bnrm] in H2. my_destruct H2. destruct H6.
          ++ destruct H6. 
             pose proof true_or_false_classic1 (EBinop op e1 e2) bs1.(st).
             pose proof H8 H7. contradiction.
          ++ destruct H6. rewrite H6. simpl. tauto.
        -- unfold cjmp_sem in H2. cbn [Bnrm] in H2. my_destruct H2. destruct H6.
          ++ destruct H6. 
             pose proof true_or_false_classic1 (EUnop op e1) bs1.(st).
             pose proof H8 H7. contradiction.
          ++ destruct H6. rewrite H6. simpl. tauto.
Qed.


(*将BB::nil ++ BBs 的jmpdest分离开来，变成一个Block的jmp语义和一串BB的jmp语义*)
Lemma BBjmp_dest_set_separate:
  forall (BBnow: BasicBlock) (BBs: list BasicBlock),
  BBjmp_dest_set (BBnow :: BBs) == BBjmp_dest_set (BBnow :: nil) ∪ BBjmp_dest_set BBs.
Proof.
  intros. unfold BBjmp_dest_set. unfold BBjmp_dest_set. sets_unfold. split; intros.
  - my_destruct H. simpl in H. destruct H.
    + left. exists BBnow. split. simpl. tauto. rewrite <- H in H0. apply H0.
    + right. exists x. split. tauto. apply H0.
  - my_destruct H. simpl in H. destruct H. my_destruct H. destruct H.
    + exists BBnow. split. simpl. tauto. rewrite <- H in H0. apply H0.
    + tauto.
    + my_destruct H. exists x. split. simpl. tauto. apply H0.
Qed.
    
(*
对于所有的BBnow，BBs，和两个BB_state, 如果：
x1和x2在(BDenote_concate (BB_jmp_sem BBnow) (BB_list_sem BBs))这个语义里，即BBnow的jmp语义和BBs的语义的连接
=> 那么BBnow BBs x1.(BB_num) x2.(BB_num) 
*)
Lemma BB_restrict_sound:
    forall (BBnow: BasicBlock) (BBs: list BasicBlock) (x1 x2: BB_state),
    Bnrm (BDenote_concate (BB_jmp_sem BBnow) (BB_list_sem BBs)) x1 x2 
    -> BBs <> nil -> 
    BB_restrict BBnow BBs x1.(BB_num) x2.(BB_num).
Proof.
  intros. unfold BB_restrict.
  unfold BDenote_concate in H. cbn[Bnrm] in H. sets_unfold in H.
  destruct H as [? [? ?]]. repeat split.
  - unfold BB_jmp_sem in H. cbn[Bnrm] in H. unfold BJump_sem in H.
    destruct eval_cond_expr. destruct jump_dest_2.
    + unfold cjmp_sem in H. cbn[Bnrm] in H. destruct H as [[? [? ?]] ?]. tauto.
    + unfold ujmp_sem in H. cbn[Bnrm] in H. destruct H as [? [? ?]]. tauto.
    + unfold ujmp_sem in H. cbn[Bnrm] in H. destruct H as [? [? ?]]. tauto.
  - unfold BBjmp_dest_set. admit. 
  - admit. 
  (*TODO*)
Admitted.
     

(*如果BBs1是BBs2的子集，那么语义上也是*)
Lemma BB_sem_child_prop :
  forall (BBs1 BBs2 : list BasicBlock) (bs1 bs2 : BB_state),
    (forall (bb : BasicBlock), In bb BBs1 -> In bb BBs2) ->
    Bnrm (BB_sem_union BBs1) bs1 bs2 -> Bnrm (BB_sem_union BBs2) bs1 bs2.
Proof.
  intros. induction BBs1.
  - simpl in H0. tauto.
  - admit.
Admitted.


Lemma BB_list_sem_child_prop:
  forall (BBs1 BBs2 : list BasicBlock) (bs1 bs2 : BB_state),
      (forall (bb : BasicBlock), In bb BBs1 -> In bb BBs2) ->
      Bnrm (BB_list_sem BBs1) bs1 bs2 -> Bnrm (BB_list_sem BBs2) bs1 bs2.
Proof.
Admitted.

(*两个BB如果跳转信息和num相同，那么jmpsem相同*)
Lemma share_BBjmp_info_and_num_means_same:
  forall (BB1 BB2: BasicBlock) (x1 x2: BB_state),
  BB1.(jump_info) = BB2.(jump_info) -> BB1.(block_num) = BB2.(block_num) -> 
  BB2.(commands) = nil ->
  Bnrm (BB_jmp_sem BB1) x1 x2 -> Bnrm (BB_sem BB2) x1 x2.
Proof.
  intros. unfold BB_sem. simpl.
  rewrite H1. sets_unfold. exists x1. split. unfold BAsgn_list_sem. sets_unfold. simpl. tauto.
  rewrite <- H. rewrite <- H0. apply H2. 
Qed.


Lemma Q_if:
  forall (e: expr) (c1 c2: list cmd),
  P c1 (cmd_BB_gen) -> P c2 (cmd_BB_gen) -> Qb (CIf e c1 c2).
Proof.
  intros.
  unfold Qb. intros. rename H1 into jmp_prop. rename H2 into BBnow_num_prop. rename H3 into BBnow_not_jmp_toself. right. 
  (* 这里要和BBgeneration里的情况对齐
  P c1里的BBs，BBnow，BBnum和Q里的BBs，BBnow和BBnum并不相同！在BBgeneration中，我们是创建了一个BBthen来当作c1的BBnow！
  P c1用于分配的BBnum也是如此，如下：    
    let BB_then_num := BB_num in
    let BB_else_num := S(BB_then_num) in
    let BB_next_num := S(BB_else_num) in
    let BB_num1 := S(BB_next_num)
  # BBs并不是Q中的BBs ++ [BBnow]！BBnow要加上跳转信息！！！！ 
  #: Check!!!!!! *)
  (* Get correct num *)
  set(BB_then_num := BBnum). set(BB_else_num := S(BB_then_num)). set(BB_next_num := S(BB_else_num)). set(BB_num1 := S(BB_next_num)).
  (* Get correct BBnow for P c1 *)
  set(BB_then := {|block_num := BB_then_num;
                   commands := nil;
                   jump_info := {|
                      jump_kind := UJump;
                      jump_dest_1 := BB_next_num; 
                      jump_dest_2 := None; 
                      jump_condition := None
                      |};
                   |}).
  set(BBnow' := {|block_num := BBnow.(block_num);
                   commands := BBnow.(commands);
                   jump_info := {|
                      jump_kind := CJump;
                      jump_dest_1 := BB_then_num; 
                      jump_dest_2 := Some BB_else_num; 
                      jump_condition := Some e
                      |};
                   |}).
  pose proof Qd_if_sound e c1 c2. rename H1 into Qdif.
  unfold Qd_if in Qdif. 
  (* Get correct BBs for P c1 *)
  (*此时已经生成的 BBs_ := BBs ++ BBnow'::nil ++ BB_then::nil, 注意这里的BB_then和BBnow不同！它里面的commands可能由于CAsgn有填充*)
  (*此时的BBnow则应该用BB_then了*)
  (*接下来要拿c1到生成的基本块列表后，对else分支做同样的事情*)
  (* Get correct num。 我们首先要拿到c1 gen之后，下一个用于分配的BBnum(即BB_num2)，所以要先destruct H，即从P c1的命题中得到这个信息 *)
  (* Get correct BBs for P c1 *)
  (*此时已经生成的 BBs_ := BBs ++ BBnow'::nil ++ BB_then::nil, 注意这里的BB_then和BBnow不同！它里面的commands可能由于CAsgn有填充*)
  (*此时的BBnow则应该用BB_then了*)
  (*接下来要拿c1到生成的基本块列表后，对else分支做同样的事情*)
  (* Get correct num。 我们首先要拿到c1 gen之后，下一个用于分配的BBnum(即BB_num2)，所以要先destruct H，即从P c1的命题中得到这个信息 *)
  unfold P in H. specialize (H (nil) BB_then BB_num1). 
  
  (*接下来要拿c1到生成的基本块列表后，对else分支做同样的事情*)
  (* Get correct num。 我们首先要拿到c1 gen之后，下一个用于分配的BBnum(即BB_num2)，所以要先destruct H，即从P c1的命题中得到这个信息 *)
  destruct H as [BBs_then [BB_now_then [ BB_cmds_then [BB_num2 [?]]]]].
  (* Get correct BBnow for P c2 *)
  set (BB_else := {|
    block_num := BB_else_num;
    commands := nil;
    jump_info := {|
        jump_kind := UJump;
        jump_dest_1 := BB_next_num; 
        jump_dest_2 := None; 
        jump_condition := None
      |}
    |}).
  (*此时已经生成的 BBs_ := BBs ++ BBnow::nil ++ BB_now_then ++ BBs_then, 注意这里的BB_now_then和BB_then不同！它里面的commands可能由于CAsgn有填充*)
  (*此时的BBnow则应该用BB_else了*)

  unfold P in H0. 

  specialize (H0 (nil) BB_else BB_num2).

  (*现在要从else分支的结果中destruct得到新的东西, 和then的情况类似，但这里的BB_num3应该没用*)
  destruct H0 as [BBs_else [BB_now_else [ BB_cmds_else [BB_num3 [?]]]]].

  (*接下来要去构造结论中的BBs'和BBnum'
    BBnum'是最终停留在的BB的编号，应该是BBnext的编号
    BBs', 根据Q中的定义，是要剔除掉BBnow之后的Delta的部分，因为这是IF，所以BBnow中是不会增加新的cmd了
  *)
  set(BB_next := {|
  block_num := BB_next_num;
  commands := nil; (* 创建一个空的命令列表 *)
  jump_info := BBnow.(jump_info)
  |}).
  set(BBs'_ := BB_now_then::nil ++ BBs_then ++ BB_now_else::nil ++ BBs_else ++ BB_next::nil). (*这里BBs_else已经包括了else分支最后一个BB，然后就是无条件跳转到BBnext了，还要接上一个BBnext，*)
  set(BBs_wo_last_ := BB_now_then::nil ++ BBs_then ++ BB_now_else::nil ++ BBs_else). 
  (* Get correct BBs' for Q *)
  (* Get correct BBs' for Q *)
  exists BBnow'. exists BBs'_. exists BB_next_num. exists (BBs_wo_last_).
  (* MAIN ========================================== *)


  (*assert 1*)
  assert ((cmd_BB_gen (CIf e c1 c2) BBs BBnow BB_then_num).(BasicBlocks) ++
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BB_then_num).(BBn) :: nil =
  BBs ++ (BBnow' :: nil) ++ BBs'_). 
  {
  cbn [cmd_BB_gen]. simpl. 
  subst BB_then_num. subst BB_next_num. subst BB_else_num.
  my_destruct H. my_destruct H0.
  replace (S (S (S BBnum))) with (BB_num1).
  replace ({|
  block_num := BBnum;
  commands := nil;
  jump_info :=
    {|
      jump_kind := UJump;
      jump_dest_1 := S (S BBnum);
      jump_dest_2 := None;
      jump_condition := None
    |}
    |}) with (BB_then).
    replace {|
    block_num := S (S BBnum);
    commands := nil;
    jump_info := BBnow.(jump_info)
  |} with (BB_next).
  replace {|
            block_num := BBnow.(block_num);
            commands := BBnow.(cmd);
            jump_info :=
              {|
               jump_kind := CJump;
               jump_dest_1 := BBnum;
               jump_dest_2 := Some (S BBnum);
               jump_condition := Some e
              |}
            |} with BBnow'.
  replace {|
            block_num := S BBnum;
            commands := nil;
            jump_info :=
              {|
                jump_kind := UJump;
                jump_dest_1 := S (S BBnum);
                jump_dest_2 := None;
                jump_condition := None
              |}
          |} with BB_else.
    + subst BBs'_ . simpl. unfold to_result. simpl. rewrite <- H1. simpl in H10. 
      assert (BBs ++ BBnow' :: BB_now_then :: BBs_then = (BBs ++ BBnow' :: nil) ++ BB_now_then :: BBs_then).
      {
        rewrite <- app_assoc. simpl. reflexivity.
      }
      rewrite H4. rewrite H10. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. 
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  } 

  (*assert 2*)
  assert ((cmd_BB_gen (CIf e c1 c2) BBs BBnow BB_then_num).(BasicBlocks) =
  BBs ++ (BBnow' :: nil) ++ BBs_wo_last_).
  {  (*模仿上面的即可*)
  cbn [cmd_BB_gen]. simpl. 
  subst BB_then_num. subst BB_next_num. subst BB_else_num.
  my_destruct H. my_destruct H0.
  replace (S (S (S BBnum))) with (BB_num1).
  replace ({|
  block_num := BBnum;
  commands := nil;
  jump_info :=
    {|
      jump_kind := UJump;
      jump_dest_1 := S (S BBnum);
      jump_dest_2 := None;
      jump_condition := None
    |}
    |}) with (BB_then).
    replace {|
    block_num := S (S BBnum);
    commands := nil;
    jump_info := BBnow.(jump_info)
  |} with (BB_next).
  replace {|
            block_num := BBnow.(block_num);
            commands := BBnow.(cmd);
            jump_info :=
              {|
              jump_kind := CJump;
              jump_dest_1 := BBnum;
              jump_dest_2 := Some (S BBnum);
              jump_condition := Some e
              |}
            |} with BBnow'.
  replace {|
            block_num := S BBnum;
            commands := nil;
            jump_info :=
              {|
                jump_kind := UJump;
                jump_dest_1 := S (S BBnum);
                jump_dest_2 := None;
                jump_condition := None
              |}
          |} with BB_else.
  + remember (list_cmd_BB_gen cmd_BB_gen c1 (BBs ++ BBnow' :: nil) BB_then BB_num1).(next_block_num) as BB_then_end_num.
    (* clear Qdif. *)
    unfold to_result. rewrite H5. rewrite <- app_assoc. simpl.
    simpl in H11. rewrite H2 in H11. rewrite H11.
    simpl in BBs_wo_last_. subst BBs_wo_last_.
    tauto.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  } 
  rename H1 into add_prop1.
  rename H2 into add_prop2. 
  repeat split.
  - apply add_prop1. 
  - apply add_prop2.
  -
      my_destruct H0. my_destruct H.
      assert (BB_then_num = BBnum). {
        reflexivity.
      }
      rewrite H13 in *. 
      specialize (Qdif BBs BBnow BBnum jmp_prop BBnow' BBs'_ BBs_wo_last_ 
      BB_then_num BB_else_num BB_next_num BB_then BB_else BBs_then BBs_else BB_now_then BB_now_else
      (S BB_next_num) BB_num2 add_prop1 add_prop2 H13).
      assert (S BB_next_num = S BB_next_num). reflexivity.
      assert (BB_else_num = S BB_then_num). reflexivity. assert (BB_next_num = S BB_else_num). reflexivity.

      assert (BB_then =
      {|
        block_num := BB_then_num;
        commands := nil;
        jump_info :=
          {|
            jump_kind := UJump;
            jump_dest_1 := BB_next_num;
            jump_dest_2 := None;
            jump_condition := None
          |}
      |}). reflexivity.
      assert (BB_else =
      {|
        block_num := BB_else_num;
        commands := nil;
        jump_info :=
          {|
            jump_kind := UJump;
            jump_dest_1 := BB_next_num;
            jump_dest_2 := None;
            jump_condition := None
          |}
      |}). reflexivity.
      assert (BBnow' =
      {|
        block_num := BBnow.(block_num);
        commands := BBnow.(cmd);
        jump_info :=
          {|
            jump_kind := CJump;
            jump_dest_1 := BB_then_num;
            jump_dest_2 := Some BB_else_num;
            jump_condition := Some e
          |}
      |}). reflexivity.
      assert (lst_prop1: to_result (list_cmd_BB_gen cmd_BB_gen c1 (nil) BB_then (S BB_next_num)) =
      BB_now_then :: nil ++ BBs_then). {
        unfold to_result. subst BB_num1. pose proof H10. rewrite H10. simpl. reflexivity.
      }

      assert (lst_prop2: to_result (list_cmd_BB_gen cmd_BB_gen c2 nil BB_else BB_num2) =
      BB_now_else :: nil ++ BBs_else). {
        unfold to_result. rewrite H4. simpl. reflexivity.
      
      }

      assert (BB_num2_prop: BB_num2 = (list_cmd_BB_gen cmd_BB_gen c1 nil BB_then (S BB_next_num)).(next_block_num)).
      {
        subst BB_num1.  rewrite H7. simpl. reflexivity.
      }

      assert (BBnowthen_num_prop: BB_now_then.(block_num) = BB_then_num).
      {
        rewrite H9. simpl. reflexivity.
      }

      assert (BBnowelse_num_prop: BB_now_else.(block_num) = BB_else_num).
      {
        rewrite H3. simpl. reflexivity.
      }

      specialize (
        Qdif H15 H16 H14 H17 H18 H19 
        lst_prop1 lst_prop2 BB_num2_prop BBnowthen_num_prop BBnowelse_num_prop
        BBnow_num_prop BBnow_not_jmp_toself).
      clear H13 H15 H16 H14 H17 H18 H19.

      assert (BB_now_else.(block_num) = BB_else_num).
      {
        rewrite H3. reflexivity.
      }
      rewrite H13 in H5.
      intros. destruct H5. destruct H11. clear err_cequiv0 inf_cequiv0 err_cequiv inf_cequiv.
      specialize (nrm_cequiv a a0). destruct nrm_cequiv.
      specialize (nrm_cequiv0 a a0). destruct nrm_cequiv0.
      (*OK 到这一步就已经是分两部分走了, 开始看上面的命题，在jmp还是不jmp之间找共通，bs1，bs2的a和a0*)
       clear H16 H11.
      assert (BB_then.(cmd) = nil).  reflexivity. (*遇到if的话，BB_then里不会添加新的cmds了*)
      rewrite H11 in H8. (* BB_now_then.(cmd) = BB_cmds_then *)
      sets_unfold.


      pose proof BDenote_concat_equiv_BB_list_sem BBnow' BBs_wo_last_.

      remember ({|
      block_num := BBnow'.(block_num);
      commands := nil;
      jump_info := BBnow'.(jump_info)
    |}) as BB_jmp.

      my_destruct H14.
      pose proof (unfold_once (BB_jmp :: nil ++ BBs_wo_last_)).
      pose proof separate_step_aux1.
      specialize (H22 x1 x2 BB_jmp BBs_wo_last_).
      (*这里需要加入两条分离性质*)
      destruct Qdif as [separate_prop1 [separate_prop2 separate_prop3]].
      assert (separate_property BB_jmp BBs_wo_last_).
      {
        unfold separate_property.  unfold separate_property in separate_prop1.
        pose proof separate_prop1.
        (*BB_jmp的num和jmpinfo都和BBnow'一样*)
        assert (BBjmp_dest_set (BBnow' :: BBs_wo_last_) == BBjmp_dest_set (BB_jmp :: BBs_wo_last_)).
        pose proof (BBjmp_dest_set_separate BBnow'  BBs_wo_last_ ).
        pose proof (BBjmp_dest_set_separate BB_jmp  BBs_wo_last_ ).
        rewrite H24. rewrite H25. 
        assert (BBjmp_dest_set (BBnow' :: nil) == BBjmp_dest_set (BB_jmp :: nil)).
        {
          unfold BBjmp_dest_set. sets_unfold. split; intros.
          - my_destruct H26. simpl in H26. destruct H26.
            + exists BB_jmp. split. 
              * simpl. tauto. 
              * assert (jump_dest_1 x3.(jump_info) = jump_dest_1 BB_jmp.(jump_info)).
                rewrite HeqBB_jmp. cbn [jump_info]. rewrite H26. reflexivity.
                assert (jump_dest_2 x3.(jump_info) = jump_dest_2 BB_jmp.(jump_info)).
                rewrite HeqBB_jmp. cbn [jump_info]. rewrite H26. reflexivity.
                rewrite <- H28. rewrite <- H29. apply H27.
            + tauto.
          - my_destruct H26. simpl in H26. destruct H26.
            + exists BBnow'. split. 
              * simpl. tauto. 
              * assert (jump_dest_1 x3.(jump_info) = jump_dest_1 BBnow'.(jump_info)).
              rewrite <- H26.  rewrite HeqBB_jmp. cbn [jump_info]. reflexivity.
              assert (jump_dest_2 x3.(jump_info) = jump_dest_2 BBnow'.(jump_info)).
              rewrite <- H26.  rewrite HeqBB_jmp. cbn [jump_info]. reflexivity.
              rewrite <- H28. rewrite <- H29. apply H27.
            + tauto.
        }
        rewrite H26. reflexivity.
        assert (BBnum_set (BBnow' :: nil) == BBnum_set (BB_jmp :: nil)).
        {
          unfold BBnum_set. sets_unfold. split; intros.
          - my_destruct H25. 
            + exists BB_jmp. split. 
              * simpl. tauto. 
              * simpl in H25. destruct H25.
                ++ assert (block_num x3 = block_num BB_jmp).
                  rewrite HeqBB_jmp. cbn [block_num]. 
                  rewrite H25. tauto.
                  rewrite <- H27. apply H26.
                ++ tauto.
          - my_destruct H25. 
            + exists BBnow'. split. 
              * simpl. tauto. 
              * simpl in H25. destruct H25.
                ++ assert (block_num x3 = block_num BBnow').
                  rewrite <- H25. rewrite HeqBB_jmp. cbn [block_num]. reflexivity.
                  rewrite <- H27. apply H26.
                ++ tauto.
        }
        rewrite <- H25. rewrite <- H24. apply H23.
      }
      (*限制的一些性质*)
      assert (BB_restrict BB_jmp BBs_wo_last_ x1.(BB_num) x2.(BB_num)). 
      {
        assert (tmp_pre: BBs_wo_last_ <> nil). {
          subst BBs_wo_last_. simpl. discriminate.
        }
        pose proof BB_restrict_sound BBnow' BBs_wo_last_ x1 x2 H14 tmp_pre.
        clear tmp_pre.
        assert (t1: BBnow'.(block_num) = BB_jmp.(block_num)). rewrite HeqBB_jmp. reflexivity.
        assert (t2: BBnow'.(jump_info) = BB_jmp.(jump_info)). rewrite HeqBB_jmp. reflexivity.
        unfold BB_restrict. unfold BB_restrict in H24. rewrite t1 in H24.
        assert (t3: BBnum_set (BBnow' :: nil) == BBnum_set (BB_jmp :: nil)).
        sets_unfold. intros. split; intros; rename H25 into focus.
        - unfold BBnum_set in *. destruct focus as [f1 f2]. exists BB_jmp. split.
          + simpl. tauto.
          + destruct f2 as [cf1 cf2]. simpl in cf1. destruct cf1.
            ++ rewrite <- H25 in cf2. rewrite <- t1. tauto.
            ++ tauto.
        -  unfold BBnum_set in *. destruct focus as [f1 f2]. exists BBnow'. split.
          + simpl. tauto.
          + destruct f2 as [cf1 cf2]. simpl in cf1. destruct cf1.
            ++ rewrite <- H25 in cf2. rewrite t1. tauto.
            ++ tauto.
        - rename H24 into key.
          assert (key2: BBnum_set (BB_jmp :: nil) ∩ BBnum_set BBs_wo_last_ == ∅).
          {
            rewrite <- t3. tauto. 
          }
          tauto.
      }
      assert (((Rels.id ∪ Bnrm (BB_sem_union (BB_jmp :: nil ++ BBs_wo_last_)) ∘ Bnrm (BB_list_sem (BB_jmp :: nil ++ BBs_wo_last_))) x1 x2 :Prop)).
      {
      sets_unfold. right.
      unfold BDenote_concate in H14. cbn [Bnrm] in H14. apply sem_start_end_with in H14.
      destruct H14. exists x3. destruct H14. split.
      (*跨一步*)
      - sets_unfold. pose proof BB_sem_child_prop (BB_jmp::nil) (BB_jmp::nil ++ BBs_wo_last_) x1 x3.
        assert ((forall bb : BasicBlock,
        In bb (BB_jmp :: nil) -> In bb (BB_jmp::nil ++ BBs_wo_last_))).
        {
          intros. simpl. simpl in H27. destruct H27.
          - rewrite H27. left. reflexivity.
          - tauto.
        }
        pose proof H26 H27. clear H26.
        pose proof share_BBjmp_info_and_num_means_same BBnow' BB_jmp x1 x3.
        assert (BBnow'.(jump_info) = BB_jmp.(jump_info)). rewrite HeqBB_jmp. reflexivity.
        assert (BBnow'.(block_num) = BB_jmp.(block_num)). rewrite HeqBB_jmp. reflexivity.
        assert (BB_jmp.(commands) = nil).  rewrite HeqBB_jmp. reflexivity.
        pose proof H26 H29 H30 H31. pose proof H32 H14.
        assert (Bnrm (BB_sem_union (BB_jmp :: nil)) x1 x3).
        {
          unfold BB_sem_union. cbn [Bnrm]. sets_unfold. left. apply H33.
        }
        pose proof H28 H34.
        apply H35.
      (*再跨一步*)
      - pose proof BB_list_sem_child_prop BBs_wo_last_ (BB_jmp::nil ++ BBs_wo_last_) x3 x2.
        assert ((forall bb : BasicBlock,
        In bb BBs_wo_last_ -> In bb (BB_jmp::nil ++ BBs_wo_last_))).
        {
          intros. simpl. simpl in H27. destruct H27.
          - rewrite H27. right. left. tauto.
          - tauto.
        }
        pose proof H26 H27 H25. apply H28.
      }
    specialize (H22 H23 H24 H25).
    rename H15 into key1.  
    clear H23 H24 H25 H21 H16.
    pose proof true_or_false e a.
    assert (exists i : int64, EDenote.nrm (eval_expr e) a i). {
      pose proof No_err_and_inf_for_expr e x1. rewrite H17 in H16. tauto.
    }
    pose proof H15 H16.
    destruct H21. 
    ** left. (*如果test true*)
      exists a. split. 
      -- pose proof BB_true_jmp_iff_test_true_jmp e a. apply H23. apply H21.
      -- clear H5. apply key1. rename H22 into key2.
          set(bs1_ := {|
          BB_num := BB_then_num;
          st := a ;  
          |}).
          exists bs1_. exists x2. cbn [Bnrm]. repeat split.
          *** apply sem_start_end_with in key2.
              destruct key2 as [bs' [step1 step2]].
              clear H14.
              (* apply unfold_once in step2. apply separate_step_aux1 in step2. *)

              (*第二刀*)
              (*这里需要加入四条分离性质*)
              pose proof (separate_step_aux3 (BB_now_then::nil ++ BBs_then) (BB_now_else :: nil ++ BBs_else) bs1_ x2).
              assert (BBnum_set (BB_now_then :: nil ++ BBs_then) ∩ BBnum_set (BB_now_else :: nil ++ BBs_else) == ∅ ). tauto.
              assert ( ~ BB_num bs1_ ∈ BBnum_set (BB_now_else :: nil ++ BBs_else)). {
                subst bs1_. simpl. 
                assert (BBnum_set (BB_now_then :: nil ++ BBs_then) BB_then_num) as H_BB_then_num_aux1.
                unfold BBnum_set. exists BB_now_then. split.
                unfold In. left. tauto. apply H9.
                unfold not. intros. sets_unfold in H14. 
                specialize (H14 BB_then_num).
                destruct H14 as [? ?]. apply H14. split.
                apply H_BB_then_num_aux1. apply H22.
              }
              assert (BBjmp_dest_set (BB_now_then :: nil ++ BBs_then) ∩ BBnum_set (BB_now_else :: nil ++ BBs_else) == ∅). tauto.
              assert (BB_num x2 ∈ BBjmp_dest_set (BB_now_then :: nil ++ BBs_then)). {
                rewrite H20. sets_unfold. unfold BBjmp_dest_set. 
                pose proof H as key.
                destruct BBs_then eqn:? in key.
                - exists BB_now_then.
                  split. unfold In. left. tauto. clear key1. destruct key as [key1 key2].
                  rewrite key1. subst BB_then. left. simpl. tauto.
                - exists (list_cmd_BB_gen cmd_BB_gen c1 nil BB_then BB_num1).(BBn). split.
                  + pose proof H10 as list_prop. remember (list_cmd_BB_gen cmd_BB_gen c1 nil BB_then BB_num1).(BBn) as cur_bbn.
                    simpl in list_prop.
                    assert (tmp_pre: BB_now_then :: nil ++ BBs_then = BB_now_then :: BBs_then).
                    simpl. reflexivity.
                    rewrite tmp_pre.
                    pose proof as_a_part_then_in BasicBlock cur_bbn (list_cmd_BB_gen cmd_BB_gen c1 nil BB_then BB_num1).(BasicBlocks) (BB_now_then :: BBs_then) list_prop as in_prop .
                    tauto.
                  + rewrite H12. subst BB_then. simpl. left. tauto.
              }
              pose proof (H5 H14 H22 H23 H24). clear H14 H22 H23 H24 H5.
              assert (bs' = bs1_). {
                unfold BB_sem in step1.
                cbn [Bnrm] in step1.
                sets_unfold in step1.
                my_destruct step1.
                simpl in step1. rewrite HeqBB_jmp in step1. simpl in step1. sets_unfold in step1.
                pose proof BB_jmp_sem_simplify BB_jmp x3 bs' e BB_then_num BB_else_num. 
                assert ((BB_jmp.(jump_info) =
                {|
                  jump_kind := CJump;
                  jump_dest_1 := BB_then_num;
                  jump_dest_2 := Some BB_else_num;
                  jump_condition := Some e
                |}) /\ Bnrm (BB_jmp_sem BB_jmp) x3 bs'). {
                  split.
                  rewrite HeqBB_jmp. reflexivity.
                  apply H5.
                }
                pose proof H14 H22.
                destruct H23.
                + my_destruct H23.
                  rewrite HeqBB_jmp in H26. simpl in H26. assert (bs' = bs1_). 
                  {
                    rewrite <- step1 in H24. rewrite H17 in H24. pose proof compare_two_BB_state bs' bs1_.
                    apply H27. split. apply H26. apply H24.
                  }
                  apply H27.
                + my_destruct H23.
                pose proof true_or_false_classic1 e a H21.
                rewrite step1 in H17. rewrite H17 in H23. contradiction. 
              }
              rewrite H5 in step2.
              pose proof H25 step2. 
              assert ({|
              block_num := BB_now_then.(block_num);
              commands := BB_cmds_then;
              jump_info := BB_now_then.(jump_info)
            |} = BB_now_then). {
            apply compare_two_BasicBlock. repeat split.
              - simpl. rewrite H8. reflexivity.
            }
            rewrite H22. apply H14.
          *** apply H18.
          *** rewrite H9. reflexivity.
          *** apply H20.

    (*test false的情况*)
    ** right. exists a. split. (*test false的情况*)
    -- pose proof BB_false_jmp_iff_test_false_jmp e a. apply H23. apply H21.
    -- sets_unfold. clear key1. (* key1是then分支的情况 *)
        rename H5 into key1. apply key1. rename H22 into key2.
        set(bs1_ := {|
            BB_num := BB_else_num;
            st := a ;  
            |}).
        exists bs1_. exists x2. cbn [Bnrm]. repeat split.
      *** apply sem_start_end_with in key2.
          destruct key2 as [bs' [step1 step2]]. clear H14.

          assert (bs' = bs1_). {
            unfold BB_sem in step1.
            cbn [Bnrm] in step1.
            sets_unfold in step1.
            my_destruct step1.
            simpl in step1. rewrite HeqBB_jmp in step1. simpl in step1. sets_unfold in step1.
            pose proof BB_jmp_sem_simplify BB_jmp x3 bs' e BB_then_num BB_else_num. 
            assert ((BB_jmp.(jump_info) =
            {|
              jump_kind := CJump;
              jump_dest_1 := BB_then_num;
              jump_dest_2 := Some BB_else_num;
              jump_condition := Some e
            |}) /\ Bnrm (BB_jmp_sem BB_jmp) x3 bs'). {
              split.
              rewrite HeqBB_jmp. reflexivity.
              apply H5.
            }
            pose proof H14 H22.
            destruct H23.
            + pose proof true_or_false_classic2 e a H21.
              rewrite step1 in H17. rewrite H17 in H23.
              my_destruct H23. contradiction.
            + my_destruct H23.
              rewrite HeqBB_jmp in H25. simpl in H25. assert (bs' = bs1_). 
              {
                rewrite <- step1 in H24. rewrite H17 in H24. pose proof compare_two_BB_state bs' bs1_.
                apply H26. split. 
                - simpl. inversion H25. tauto.
                - apply H24.
              }
              apply H26.
          }

          (* 这里要理论上会简单一点？else对应的BBs_else本身和BBs_是连在一起的，这里不会再用到aux3了，但可能需要别的引理 *)
          admit.
      *** apply H18.
      *** rewrite H20. subst BB_else. reflexivity.
  - (*反方向*)
    intros. rename H1 into cmd_sem_prop.
    exists {| st := a; BB_num := BBnow.(block_num) |}.
    exists {| st := a0; BB_num := BB_next_num |}.
    repeat split; try tauto.
    remember ({| BB_num := BBnow.(block_num); st := a |} ) as bs1.
    remember ({| BB_num := BB_next_num; st := a0 |}) as bs2.
    unfold cmd_sem in cmd_sem_prop. sets_unfold in cmd_sem_prop.
    destruct cmd_sem_prop as [t1 | t2].
    (* test true -> then 分支*)
    + sets_unfold in t1. destruct t1 as [i [t11 t12]].
      exists {| st := a; BB_num := BB_then.(block_num) |}. split.

      (* Two parts. Initial jump and all the others *)

      -- unfold BB_jmp_sem. cbn[Bnrm]. unfold BJump_sem.
        subst BBnow'. simpl. destruct e.
        ++ unfold cjmp_sem. cbn[Bnrm]. 
            repeat split; subst bs1; subst bs2; try tauto.
            left. simpl. split. tauto. unfold test_true_jmp.
            * unfold test_true in t11. sets_unfold in t11.
              destruct t11 as [t111 t112]. destruct t111 as [x_ [aux1 aux2]]. exists x_. split.
              apply aux1. apply aux2.
            * simpl. lia.
        ++ unfold cjmp_sem. cbn[Bnrm]. 
          repeat split; subst bs1; subst bs2; try tauto.
          left. simpl. split. tauto. unfold test_true_jmp.
          * unfold test_true in t11. sets_unfold in t11.
          destruct t11 as [t111 t112]. destruct t111 as [x_ [aux1 aux2]]. exists x_. split.
          apply aux1. apply aux2.
          * simpl. lia. 

      -- my_destruct H. cbn[Bnrm]. sets_unfold.
         subst BBs_wo_last_.

         (* destruct H7. clear err_cequiv inf_cequiv. 
         pose proof nrm_cequiv x1 a0. clear nrm_cequiv.
         destruct H7. clear H7. pose proof H9 H2.
         my_destruct H7. simpl in H7. clear H9. *)
        (* Inconsistency here. *)
    (* test false -> else 分支*)
    + admit.
  - admit.  (*出错*)
  - admit. (*出错*)
  - admit. (*无限*)
Admitted.