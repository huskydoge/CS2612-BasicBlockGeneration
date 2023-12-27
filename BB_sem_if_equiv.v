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

(* TODO find a name for it! *)
Lemma no_name1:
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
        unfold not. intros. apply no_name1 in H3. 
        destruct H3. tauto. tauto.
      }
      pose proof H1 H3 H. tauto.
    - tauto. 
  }
  clear H1.
  pose proof BB_dest_in_BBsA_if_BBsA_BBsB_independent BBs1 BBs2 bs1 bs2.
  apply H1. apply H. apply H2. unfold not. apply H0.
Qed.


Lemma BB_then_num_not_in_BB_else: 
  forall (BBs1 BBs2: list BasicBlock)(bs1 bs2: BB_state),
  (BBnum_set BBs1) ∩ (BBnum_set BBs2) = ∅ ->
  not (BBnum_set BBs2 (BB_num bs1))->
  (BBjmp_dest_set BBs1) ∩ (BBnum_set BBs2) = ∅ ->
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
  assert(BB_num bs2 ∈( BBjmp_dest_set BBs1 ∩ BBnum_set BBs2)).
  {
    split. tauto. tauto.
  }
  rewrite H1 in H5.
  tauto.
Qed.





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


(* #TODO 切第二刀，把then和else切开来*)
Lemma separate_step_aux3:
  forall (BBs1 BBs2: list BasicBlock)(bs1 bs2: BB_state),
  (BBnum_set BBs1) ∩ (BBnum_set BBs2) = ∅ ->
  not ((BB_num bs1) ∈ (BBnum_set BBs2))  ->
  (BBjmp_dest_set BBs1) ∩ (BBnum_set BBs2) = ∅ ->
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
     -- pose proof BB_then_num_not_in_BB_else BBs1 BBs2 bs1 x0.
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
  assert ((Bnrm (BB_list_sem (BBnow' :: nil ++ BBs)) bs1 bs2) = 
  (Rels.id ∪ Bnrm (BB_sem_union (BBnow' :: nil ++ BBs)) ∘ Bnrm (BB_list_sem (BBnow' :: nil ++ BBs)))
  bs1 bs2). {
    specialize (H6 bs1 bs2). (*这里很奇怪*)
    admit.
  }
  rewrite H7.
  admit.
  
Admitted.

Search EDenote.

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


Lemma Q_if:
  forall (e: expr) (c1 c2: list cmd),
  P c1 (cmd_BB_gen) -> P c2 (cmd_BB_gen) -> Qb (CIf e c1 c2).
Proof.
  intros.
  unfold Qb. intros. right.
  pose proof Qd_if_sound e c1 c2 H H0. rename H1 into separate_auxs.
  unfold Qd_if in separate_auxs. specialize (separate_auxs (BBs) (BBnow) (BBnum)). 
  destruct separate_auxs as [BBnow' [BBs' [BB_num' [BBs_wo_last_ [BB_then_num [BB_else_num [BB_next_num [BB_then [BB_else [BBs_then [BBs_else [BB_now_then [BB_now_else [BB_num1 [?]]]]]]]]]]]]]]].

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
  (*此时已经生成的 BBs_ := BBs ++ BBnow'::nil ++ BB_then::nil, 注意这里的BB_then和BBnow不同！它里面的commands可能由于CAsgn有填充*)
  (*此时的BBnow则应该用BB_then了*)
  (*接下来要拿c1到生成的基本块列表后，对else分支做同样的事情*)
  (* Get correct num。 我们首先要拿到c1 gen之后，下一个用于分配的BBnum(即BB_num2)，所以要先destruct H，即从P c1的命题中得到这个信息 *)
  unfold P in H. specialize (H (BBs ++ BBnow'::nil) BB_then BB_num1). 
  
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
  (*此时已经生成的 BBs_ := BBs ++ BBnow::nil ++ BB_now_then ++ BBs_then, 注意这里的BB_then_now和BB_then不同！它里面的commands可能由于CAsgn有填充*)
  (*此时的BBnow则应该用BB_else了*)

  unfold P in H0. 
  specialize (H0 (BBs ++ BBnow'::nil ++ BB_now_then::nil ++ BBs_then) BB_else BB_num2).

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
  exists BBnow'. exists BBs'_. exists BB_next_num. exists (BBs_wo_last_).
  (* MAIN ========================================== *)
  repeat split.
  - cbn [cmd_BB_gen]. simpl. 
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
      + subst BBs'_ . simpl. unfold to_result. simpl. rewrite H4. simpl. rewrite <- H1. simpl in H10. 
        assert (BBs ++ BBnow' :: BB_now_then :: BBs_then = (BBs ++ BBnow' :: nil) ++ BB_now_then :: BBs_then).
        {
          rewrite <- app_assoc. simpl. reflexivity.
        }
        rewrite <- H13. rewrite H10. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. 
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
  - cbn [cmd_BB_gen]. simpl. admit. (*模仿上面的即可 #TODO, hard*)
  - my_destruct H0. my_destruct H.
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
         assert (separate_property BB_jmp BBs_wo_last_). admit. (*分离性质1*)
         assert (BB_restrict BB_jmp BBs_wo_last_ x1.(BB_num) x2.(BB_num)). admit. (*分离性质2, 这个感觉是可以直接写证明，就一个起点和终点约束*)
         assert (((Rels.id
         ∪ Bnrm (BB_sem_union (BB_jmp :: nil ++ BBs_wo_last_))
           ∘ Bnrm (BB_list_sem (BB_jmp :: nil ++ BBs_wo_last_))) x1 x2
        :
        Prop)). admit. (* TODO *)
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
               ***  apply sem_start_end_with in key2.
                    destruct key2 as [bs' [step1 step2]].
                    clear H14.
                    (* apply unfold_once in step2. apply separate_step_aux1 in step2. *)

                    (*第二刀*)
                    (*这里需要加入四条分离性质*)
                    pose proof (separate_step_aux3 (BB_now_then::nil ++ BBs_then) (BB_now_else :: nil ++ BBs_else) bs1_ x2).
                    assert (BBnum_set (BB_now_then :: nil ++ BBs_then) ∩ BBnum_set (BB_now_else :: nil ++ BBs_else) = ∅ ). admit. (*分离性质3*)
                    assert ( ~ BB_num bs1_ ∈ BBnum_set (BB_now_else :: nil ++ BBs_else)). admit. (*分离性质4*)
                    assert (BBjmp_dest_set (BB_now_then :: nil ++ BBs_then) ∩ BBnum_set (BB_now_else :: nil ++ BBs_else) = ∅). admit. (*分离性质5*)
                    assert (BB_num x2 ∈ BBjmp_dest_set (BB_now_then :: nil ++ BBs_then)). admit. (*分离性质6*)
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
                          - admit. (* 利用H25即可 *)
                          - apply H24.
                        }
                        apply H26.
                    }
                    
                    (* 这里要理论上会简单一点？else对应的BBs_else本身和BBs_是连在一起的，这里不会再用到aux3了，但可能需要别的引理 *)
                    admit.

        - admit.  (*反方向*)
        - admit.  (*出错*)
        - admit. (*出错*)
        - admit. (*无限*)
Admitted.
