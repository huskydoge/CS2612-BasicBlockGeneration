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
Require Import Main.BB_gen_properties.


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


Lemma P_nil: forall cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results,
  P nil (cmd_BB_gen).
Proof.
  unfold P. intros.
  exists nil. exists BBnow. exists nil. exists BBnum. exists BBnow.(block_num).
  repeat split; try tauto. 
  - rewrite append_nil_r. tauto.
  - rename H into jmp_prop. rename H0 into block_lt_bbnum.  rename H1 into not_jmp_toself.
    destruct jmp_prop as [jmp_prop1 [jmp_prop2 jmp_prop3]].
    assert(jmp_cond: jump_kind BBnow.(jump_info) = UJump /\ jump_dest_2 BBnow.(jump_info) = None).
    tauto. 
    intros. simpl. my_destruct H. cbn [Bnrm] in H.
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
      (*我要在这里用cond1和cond2推出矛盾，因为middle的num经过跳转一次之后，肯定不在BBnow的语义里了*)    
      pose proof simplify_listsem_with_mismatch_num middle x0 {|
      block_num := BBnow.(block_num);
      commands := nil;
      jump_info := BBnow.(jump_info)
    |} nil as steps.
    

    pose proof cond1 as backup.
    simpl in backup. sets_unfold in backup. destruct backup as [true | false].
    -- destruct true as [BB [b1 b2]].
      pose proof Jump_restrict BBnow BB middle b2 jmp_prop2 as main.

      destruct main as [pre1 pre2].
      
      pose proof (steps pre1 pre2 cond2) as p.
      clear steps.
      pose proof nil_sem middle x0 p. 
      simpl in cond1. sets_unfold in cond1. destruct cond1.
      ** destruct H4 as [i [cond11 cond12]].
        unfold BJump_sem in cond12.
        destruct (eval_cond_expr (jump_condition BBnow.(jump_info))).
        +++ destruct (jump_dest_2 BBnow.(jump_info)) eqn:? in cond12. 
          *** rewrite jmp_prop2 in Heqo. discriminate Heqo.
          *** unfold ujmp_sem in cond12. cbn [Bnrm] in cond12. destruct cond12. 
              rewrite <- cond11 in H4. rewrite H4 in H0.
              rewrite <- H in H1. rewrite H1 in H0. rewrite H0. tauto.
        +++ unfold ujmp_sem in cond12. cbn [Bnrm] in cond12. destruct cond12. 
            rewrite <- cond11 in H4. rewrite H4 in H0.
            rewrite <- H in H1. rewrite H1 in H0. rewrite H0. tauto. 
      ** tauto.
    -- tauto.
      
  - intros. exists {| st := a ; BB_num := BBnow.(block_num) |}.
    exists {| st := a0 ; BB_num := BBnow.(jump_info).(jump_dest_1) |}.
    repeat split; try tauto. cbn [Bnrm].
    destruct H as [jmp_prop1 [jmp_prop2 jmp_prop3]].
    simpl in H2. sets_unfold in H2. rewrite H2. 
    unfold BB_list_sem. cbn [Bnrm]. sets_unfold. exists (S O).
    unfold Iter_nrm_BBs_n. sets_unfold. exists {| BB_num := jump_dest_1 BBnow.(jump_info); st := a0 |}.
    split. 
      + unfold BB_sem_union. cbn [Bnrm]. simpl. 
        unfold BJump_sem. rewrite jmp_prop3. simpl. sets_unfold.
        simpl. left.
        exists {| BB_num := BBnow.(block_num); st := a0 |}.
        split; try tauto. 
      + tauto.

  - admit. (* err case *)
  - admit.  (* err case *)
  - admit. (* inf case *)
  - admit. (* inf case *) 
Admitted.


Lemma num_set_inclusive_if_BB_inclusive:
  forall (x: BasicBlock) (BBs: list BasicBlock),
    In x BBs -> x.(block_num) ∈ BBnum_set BBs.
Proof.
  intros. sets_unfold. unfold BBnum_set. exists x. split. apply H. tauto.
Qed.


(* 满足分离条件的BBnow和BBs，如果一开始在BBs中，就会一直在BBs中 *)
Lemma BB_list_sem_spin_in_BBs: 
  forall (BBnow : BasicBlock) (BBs: list BasicBlock) (bs1 bs2: BB_state),
    bs1.(BB_num) ∈ BBnum_set BBs 
  -> BBnum_set (BBnow :: nil) ∩ BBjmp_dest_set (BBnow :: BBs) == ∅ 
  -> Bnrm (BB_list_sem (BBnow :: BBs)) bs1 bs2 
  -> BBnum_set (BBnow :: nil) ∩ BBnum_set BBs == ∅ 
  -> Bnrm (BB_list_sem BBs) bs1 bs2.
Proof.
  intros. unfold BB_list_sem. cbn[Bnrm]. unfold BB_list_sem in H1. cbn[Bnrm] in H1.
  sets_unfold in H1. sets_unfold. my_destruct H1. revert bs1 H H1.
  induction x.
  - intros. simpl in H1. exists O. simpl. apply H1.
  - intros. cbn[Iter_nrm_BBs_n] in H1. sets_unfold in H1.
    my_destruct H1. unfold BB_sem_union in H1. cbn[Bnrm] in H1. sets_unfold in H1.
    destruct H1.
    + pose proof BB_sem_start_BB_num bs1 x0 BBnow H1.
      sets_unfold in H2. specialize (H2 bs1.(BB_num)). destruct H2. clear H5.
      assert (BBnum_set (BBnow :: nil) (BB_num bs1) /\ BBnum_set BBs (BB_num bs1)). {
        split. unfold BBnum_set. exists BBnow. split. unfold In. left. tauto. rewrite H4. tauto.  sets_unfold in H. apply H.
      }
      pose proof H2 H5. tauto.
    + specialize (IHx x0). 
      assert (x0 <> bs2 -> BB_num x0 ∈ BBnum_set BBs). {
        sets_unfold. 
        pose proof BBs_bs1_in_BB_num_set (BBnow :: BBs) x0 bs2.
        assert (Bnrm (BB_list_sem (BBnow :: BBs)) x0 bs2). { 
          unfold BB_list_sem. cbn[Bnrm]. sets_unfold. exists x. apply H3.
        }
        pose proof H4 H5. clear H4.
        pose proof BBs_sem_union_jmp_dest bs1 x0 BBs H1.
        (* 这个时候，我们就可以从H6中把BBnum x0在BBnow的情况试图排除了 *)
        destruct H6.
        - unfold BBnum_set in H6. my_destruct H6. unfold In in H6.
          destruct H6. (*此时有两种情况，有一种是矛盾的*)
          rewrite <- H6 in H7.
          sets_unfold in H0. specialize (H0 x0.(BB_num)). destruct H0.
          + clear H8. assert (False). {
              apply H0. split. unfold BBnum_set. exists BBnow.
              split. unfold In. left. tauto. apply H7.
              unfold BBjmp_dest_set. unfold BBjmp_dest_set in H4.
              my_destruct H4. exists x2. split. unfold In. right. apply H4.
              apply H8.
            }
            tauto.
          + unfold BBnum_set. exists x1. split. apply H6. apply H7.
        - intros. contradiction.
      }
      pose proof classic (x0 = bs2). destruct H5.
      * exists (S O). simpl. rewrite H5 in H1. sets_unfold. exists bs2.
        split. apply H1. tauto.
      * pose proof H4 H5 as H4. 
        pose proof IHx H4 H3. destruct H6.
        sets_unfold. exists (S x1). simpl. sets_unfold.
        exists x0. split. apply H1. apply H6.
Qed.


(* 对于满足分离条件的BBnow和BBs，从BBnow出发的BB_state最终会一直在BBs中 *)
Lemma BB_list_sem_unfold_bs1_and_simpl: 
  forall (BBnow : BasicBlock) (BBs: list BasicBlock) (bs1 bs2: BB_state),
    bs1.(BB_num) = BBnow.(block_num) -> bs1 <> bs2 
    -> BBnum_set (BBnow :: nil) ∩ BBjmp_dest_set (BBnow :: BBs) == ∅
    -> BBnum_set (BBnow :: nil) ∩ BBnum_set BBs == ∅ 
    -> Bnrm (BB_list_sem (BBnow :: BBs)) bs1 bs2 -> (exists x, Bnrm (BB_sem BBnow) bs1 x /\ Bnrm (BB_list_sem BBs) x bs2). 
Proof.
  intros. rename H2 into Ht. rename H3 into H2. 
  pose proof BBs_list_sem_exists_BB_bs1_x (BBnow :: BBs) bs1 bs2 H2.
  destruct H3 as [? | ?].
  - my_destruct H3. exists x0. split.
    + unfold In in H3. destruct H3 as [? | ?]. rewrite H3. apply H4.
      pose proof num_set_inclusive_if_BB_inclusive.
      specialize (H6 x BBs). pose proof H6 H3 as H6.
      sets_unfold in H6.
      pose proof BB_sem_start_BB_num bs1 x0 x H4.
      assert (BBnum_set BBs bs1.(BB_num)). {
        unfold BBnum_set. exists x. split. unfold In.
        apply H3. rewrite H7. tauto. 
      }

      assert (BBnum_set (BBnow :: nil) bs1.(BB_num)). {
        unfold BBnum_set. exists BBnow. split. unfold In. left. tauto.
        rewrite H. tauto.
      }

      sets_unfold in Ht. specialize (Ht bs1.(BB_num)). destruct Ht.
      clear H11. assert (BBnum_set (BBnow :: nil) (BB_num bs1) /\ BBnum_set BBs (BB_num bs1)). { 
        split. apply H9. apply H8.
      }

      pose proof H10 H11. tauto.
    + pose proof BB_list_sem_spin_in_BBs BBnow BBs x0 bs2.
      assert (x0 <> bs2 -> BB_num x0 ∈ BBnum_set BBs). {
        sets_unfold.
        pose proof BBs_bs1_in_BB_num_set (BBnow :: BBs) x0 bs2 H5.
        unfold In in H3. destruct H3.
        - rewrite <- H3 in H4. unfold BB_sem in H4. cbn[Bnrm] in H4.
          sets_unfold in H4. my_destruct H4.
          pose proof BB_jmp_sem_num_in_BBjmp_dest_set BBnow x1 x0 H8.
           (*有了这个条件之后就自然可以排除x0.(BB_num)为BBnow.(block_num)  *)
          destruct H7.
          + unfold BBnum_set in H7. my_destruct H7. unfold In in H7.
            destruct H7.
            * rewrite <- H7 in H10. sets_unfold in H1. specialize (H1 x0.(BB_num)).
              destruct H1. clear H11.
              assert (False). {
                apply H1. split. unfold BBnum_set. exists BBnow.
                unfold In. split. left. tauto. apply H10.
                sets_unfold in H9. unfold BBjmp_dest_set. 
                unfold BBjmp_dest_set in H9. my_destruct H9. exists x3.
                split. unfold In. left. unfold In in H9. destruct H9.
                apply H9. tauto. apply H11.
              }
              tauto.
            * intros. unfold BBnum_set. exists x2. split. apply H7. apply H10.
          + intros. contradiction.
        - pose proof BB_sem_start_BB_num bs1 x0 x H4. rewrite H in H8.
          destruct H7. 
          + intros. unfold BBnum_set in H7. my_destruct H7. unfold In in H7.
            destruct H7. 
            * rewrite <- H7 in H10. sets_unfold in Ht. unfold BBnum_set in Ht.
              specialize (Ht BBnow.(block_num)). destruct Ht. clear H12.
              assert (False). {
                apply H11. split.
                exists BBnow. unfold In. split. left. tauto. tauto.
                exists x. split. apply H3. rewrite H8. tauto.
              }
              tauto.
            * unfold BBnum_set. exists x1. split. apply H7. apply H10.
          + intros. contradiction. 
      }
      pose proof classic (x0 = bs2). destruct H8.
      rewrite H8. simpl. sets_unfold. exists O. simpl. sets_unfold. tauto.
      pose proof H7 H8 as H7. pose proof H6 H7 H1 H5 Ht. apply H9.
  - contradiction.
Qed.



(* 只拆分一个cmd *)
Lemma BBs_sem_Asgn_split:
  forall (BBnow: BasicBlock) (BBs: list BasicBlock) (BBcmds: list BB_cmd) (x: var_name) (e: expr) (bs1 bs2: BB_state),
    let BB1 := {|
      block_num := BBnow.(block_num);
      commands := {| X := x; E := e |} :: BBcmds;
      jump_info := BBnow.(jump_info)
    |} in
    let BB2 := {|
      block_num := BBnow.(block_num);
      commands := BBcmds;
      jump_info := BBnow.(jump_info)
    |} in
    let BBcmd := {| X := x ; E := e|} in
     bs1.(BB_num) = BBnow.(block_num) -> 
     BBnum_set (BB2 :: nil) ∩ BBjmp_dest_set (BB2 :: BBs) == ∅ ->
     (BBnum_set (BB2 :: nil) ∩ BBnum_set BBs == ∅) ->
     bs1 <> bs2 ->
     ~ bs2.(BB_num) ∈ BBnum_set (BB2 :: nil) ->
     ((Bnrm (BB_list_sem (BB1 :: BBs)) bs1 bs2) <-> (exists (x: BB_state), Bnrm (BAsgn_list_sem (BBcmd :: nil)) bs1 x /\ Bnrm (BB_list_sem (BB2 :: BBs)) x bs2)).
Proof.
  intros. rename H0 into Hn1. rename H1 into Hn2. 
  rename H2 into Hn3. rename H3 into Hn4. split.
  + intros. 
    assert ((exists x, Bnrm (BB_sem BB1) bs1 x /\ Bnrm (BB_list_sem BBs) x bs2)). {
      pose proof BB_list_sem_unfold_bs1_and_simpl BB1 BBs bs1 bs2.
      apply H1.
      - subst BB1. simpl. apply H.
      - apply Hn3.
      - admit. (*TODO lyz easy. BB2 and BB1 should behave the same. Consider sets_unfold everything *)
      - admit. (*TODO lyz easy. same*)
      - apply H0.    
    }
    my_destruct H1.
    unfold BB_sem in H1. cbn[Bnrm] in H1. sets_unfold in H1. my_destruct H1.
    unfold BB_cmds_sem in H1. cbn[Bnrm] in H1.
    assert (exists x: BB_state, Bnrm (BAsgn_list_sem (BBcmd :: nil)) bs1 x /\ Bnrm (BAsgn_list_sem BBcmds) x x1). {
      subst BB1. simpl in H1. sets_unfold in H1. 
      destruct H1 as [? [[? ?] ?]].
      exists x2. split. subst BBcmd. simpl. sets_unfold. exists x2. repeat split. apply H1. apply H4. apply H5.
    }
    my_destruct H4. exists x2. split. apply H4.
    assert ((exists bs: BB_state, Bnrm (BB_sem BB2) x2 bs /\ Bnrm (BB_list_sem BBs) bs bs2) -> Bnrm (BB_list_sem (BB2 :: BBs)) x2 bs2). {
      intros. my_destruct H6. unfold BB_list_sem. cbn[Bnrm]. sets_unfold.
      unfold BB_list_sem in H7. cbn[Bnrm] in H7. sets_unfold in H7. my_destruct H7.
      exists (S x4). cbn[Iter_nrm_BBs_n]. sets_unfold. exists x3.
      split. unfold BB_sem_union. cbn[Bnrm]. sets_unfold. left. apply H6.
      assert(forall (n: nat), Iter_nrm_BBs_n (BB_sem_union BBs) n ⊆ Iter_nrm_BBs_n (BB_sem_union (BB2 :: BBs)) n).
      {
        intros. induction n. simpl. sets_unfold. tauto.
        cbn[Iter_nrm_BBs_n] . sets_unfold. intros. my_destruct H8.
        exists x5. split. 
        + pose proof BB_sem_child_prop BBs (BB2::BBs) a x5. 
          apply H10. intros. unfold In. right. apply H11. apply H8.
        + sets_unfold in IHn. pose proof IHn x5 a0 H9. apply H10. 
      }
      specialize (H8 x4). sets_unfold in H8. specialize (H8 x3 bs2).
      pose proof H8 H7. apply H9.
    }
    apply H6.
    exists x0. split.
    -- unfold BB_sem. cbn[Bnrm]. sets_unfold. unfold BB_cmds_sem. cbn[Bnrm].
       exists x1. subst BB2. simpl. split. apply H5. apply H3.
    -- apply H2.
  + intros. my_destruct H0.
    unfold BB_list_sem in H1. cbn[Bnrm] in H1. sets_unfold in H1. destruct H1 as [? ?].
    pose proof BB_list_sem_unfold_bs1_and_simpl BB2 BBs x0 bs2.

    (* 先考虑x0 = bs2的特殊情况 *)
    pose proof classic (x0 = bs2) as Ht. destruct Ht as [Ht1 | Ht2].

    (* Ht1显然是不可以的 *)
    rewrite Ht1 in H0. rewrite Ht1 in H1. 
    assert (bs2.(BB_num) = BBnow.(block_num)). {
      unfold BAsgn_list_sem in H0. cbn[Bnrm] in H0. sets_unfold in H0.
      unfold BAsgn_denote in H0. cbn[Bnrm] in H0. my_destruct H0.
      rewrite <- H3. rewrite <- H4. apply H. 
    }

    unfold not in Hn4. sets_unfold in Hn4.
    assert (False). {
      apply Hn4. unfold BBnum_set. exists BB2. split.
      unfold In. left. tauto. rewrite H3. tauto.
    }
    tauto.

    (* 接下来考虑Ht2的情况 *)
    assert (x0 <> bs2). apply Ht2.
    assert (Bnrm (BB_list_sem (BB2 :: BBs)) x0 bs2). {
      unfold BB_list_sem. cbn[Bnrm]. sets_unfold. exists x1. apply H1.
    }
    assert (BB_num x0 = BB2.(block_num)). {
      unfold BAsgn_list_sem in H0. cbn[Bnrm] in H0. sets_unfold in H0.
      unfold BAsgn_denote in H0. cbn[Bnrm] in H0. my_destruct H0.
      rewrite H5 in H6. subst BB2. simpl. rewrite <- H. rewrite H6. tauto. 
    } 
    pose proof Hn1. pose proof Hn2.
    pose proof H2 H5 H3 H6 H7 H4. my_destruct H8.

    assert (exists x : BB_state, Bnrm (BB_sem BB1) bs1 x /\ Bnrm (BB_list_sem BBs) x bs2). {
      exists x2. split.
      - unfold BB_sem. cbn[Bnrm]. sets_unfold. 
        unfold BB_sem in H8. cbn[Bnrm] in H8. sets_unfold in H8. my_destruct H8.
        exists x3. unfold BB_cmds_sem.
        cbn[Bnrm]. subst BB1. split.
        + unfold BAsgn_list_sem. simpl.
          sets_unfold. exists x0. split. subst BBcmd. simpl in H0. 
          sets_unfold in H0. destruct H0 as [? [[? ?] ?]]. repeat split.
          rewrite <- H12. apply H0. rewrite <- H12. apply H11. apply H8.
        + apply H10.
      - apply H9. 
    }

    my_destruct H10.
    unfold BB_list_sem. cbn[Bnrm]. sets_unfold.
    unfold BB_list_sem in H11. cbn[Bnrm] in H11. sets_unfold in H11.
    my_destruct H11. exists (S x4). cbn[Iter_nrm_BBs_n].
    sets_unfold. exists x3. split. unfold BB_sem_union. cbn[Bnrm].
    sets_unfold. left. apply H10. 
    assert(forall (n: nat), Iter_nrm_BBs_n (BB_sem_union BBs) n ⊆ Iter_nrm_BBs_n (BB_sem_union (BB1 :: BBs)) n).
    {
      intros. induction n. simpl. sets_unfold. tauto.
      cbn[Iter_nrm_BBs_n] . sets_unfold. intros. my_destruct H12.
      exists x5. split. 
      + pose proof BB_sem_child_prop BBs (BB1::BBs) a x5. 
        apply H14. intros. unfold In. right. apply H15. apply H12.
      + sets_unfold in IHn. pose proof IHn x5 a0 H13. apply H14. 
    }

    specialize (H12 x4). sets_unfold in H12. specialize (H12 x3 bs2).
    pose proof H12 H11 as H12. apply H12.
Admitted.
    



Lemma P_cons:
  forall (c: cmd) (cmds: list cmd),
  Qb c -> P cmds cmd_BB_gen -> P (c :: cmds) (cmd_BB_gen).
Proof.
  intros.
  rename H into Qb_prop. rename H0 into P_prop. (* ! P_prop描述的是c::cmds中cmds的性质*)
  unfold Qb in Qb_prop. unfold P in P_prop. simpl in *.
  destruct c eqn:?.
  - unfold P. intros.
    (* 结论中的BBs'是表示c :: cmds在gen之后新的BBs
       而BBnow'则是c :: cmds在gen之后的对BBnow的cmds和jumpinfo进行改变之后的BBnow
       那么我们本质上是用Qb和P来拼接着生成c :: cmds
       最后再证明生成的结果符合某些性质
    *)

    specialize (Qb_prop BBs BBnow BBnum). (*P(c:cmds), Q(c), 所以Q的BBs用P引入的去填，正确*)
    destruct H as [bbnow_T1 [bbnow_T2 bbnow_T3]]. (*BBnow的jmpinfo*)
    assert (jump_kind BBnow.(jump_info) = UJump /\
    jump_dest_2 BBnow.(jump_info) = None) as bbnow_T4. split. apply bbnow_T1. apply bbnow_T2.
    pose proof Qb_prop bbnow_T4 H0 H1 bbnow_T3 as Qb_prop.

    (* Qb 会有两种情况来讨论，但是可以根据isasgn进行情况排除 *)
    destruct Qb_prop as [Qb_asgn | Qb_if_while ].
    + destruct Qb_asgn as [isAsgn [? [? [B1 [B2 H_asgn_equiv]]]]]. 
      unfold BB_generation.cmd_BB_gen in B1. simpl in B1.
      (* 
        从B1，B2中显然可以得到x0就是我们想要的完成了CAsgn移入的Block
        加入一条CAsgns是不会改变BBs的，所以原来的BBs会作为P cmds的输入
        同样不会改变的还有BBnum。
      *)
      specialize (P_prop BBs x0 BBnum).
      assert (jump_kind x0.(jump_info) = UJump /\
      jump_dest_2 x0.(jump_info) = None /\
      jump_condition x0.(jump_info) = None) as T1. {
        rewrite <- B1. tauto. 
      }

      assert ((x0.(block_num) < BBnum)%nat) as T2. rewrite <- B1. tauto.

      assert (x0.(block_num) <> jump_dest_1 x0.(jump_info)) as T3. rewrite <- B1. tauto.

      pose proof P_prop T1 T2 T3 as P_prop.
      clear T1 T2 T3. (*x0的jmp信息不会再用到了*)

      destruct P_prop as [BBs_ [BBnow'_ [BBcmds_ [BBnum'_ [BBendnum_ ?]]]]].

      exists BBs_. exists BBnow'_. exists ({|X := x; E := e|}::nil ++ BBcmds_). exists BBnum'_. exists BBendnum_. 
      
      (* 整理一下已知条件 *)
      destruct H as [C1 [C2 [C3 [C5 [C6 [H_cmd_equiv C7]]]]]].

      repeat split. 
      -- rewrite <- B1 in C1. simpl in C1. 
         destruct BBs_.
         ++ tauto.
         ++ cbn [JmpInfoMatching]. tauto.
      -- simpl. rewrite B1. tauto.
      -- rewrite <- B1 in C3. simpl in C3. rewrite <- app_assoc in C3. apply C3.
      -- rewrite C5. rewrite <- B1. simpl. tauto.
      -- simpl. rewrite B1. tauto.
      -- intros. (* BBsem -> cmd_sem *)
         destruct H as [? [? [H_sem_full [D1 [D2 [D3 D4]]]]]]. cbn[Bnrm] in H_sem_full.
         destruct H_asgn_equiv. clear err_cequiv inf_cequiv.
         sets_unfold in nrm_cequiv. rename nrm_cequiv into asgn_nrm_equiv.
         destruct H_cmd_equiv. clear err_cequiv inf_cequiv.
         sets_unfold in nrm_cequiv. rename nrm_cequiv into cmds_nrm_equiv.

         cbn[cmd_list_sem]. simpl. sets_unfold.
         (* asgn的语义是不涉及Jump的，所以我们希望先走一步CAsgn，再用cmds_nrm_equiv的结论来进行证明 *)
         (* 这个时候，就需要H_sem_full来拆出来这两步，用一个中间的state作为过渡 *)
         pose proof BBs_sem_Asgn_split BBnow'_ BBs_ BBcmds_ x e x2 x3 as T1.
         destruct T1 as [H T2]. apply D3.
         (* 使用这个定理的四个条件 *)
         admit.
         admit.
         admit.
         unfold not. intros. admit.
         destruct H as [? [H_step1 H_step2]]. apply H_sem_full. 
         exists x4.(st). split. 
         ++ unfold BAsgn_list_sem in H_step1. cbn[Bnrm] in H_step1.
            unfold BAsgn_denote in H_step1. cbn[Bnrm] in H_step1.
            sets_unfold in H_step1. simpl in H_step1.
            destruct H_step1 as [? [[H_step1_main H_step1_aux2] H_step1_aux1]].
            rewrite H_step1_aux1 in H_step1_main.
            rewrite D1 in H_step1_main. destruct H_step1_main as [? [H_step1_main1 [H_step1_main2 H_step1_main3]]].
            exists x6. repeat split. 
            apply H_step1_main1. apply H_step1_main2. intros. specialize (H_step1_main3 Y).
            pose proof H_step1_main3 H as T1. rewrite T1. tauto.  
        ++ specialize (cmds_nrm_equiv x4.(st) a0).
           destruct cmds_nrm_equiv as [H_cmds_equiv_forward T1]. clear T1.
           apply H_cmds_equiv_forward. cbn[Bnrm].
           exists x4. exists {| st := a0; BB_num := jump_dest_1 x0.(jump_info) |}.
           simpl. repeat split; try tauto.
           unfold BB_list_sem in H_step2. cbn[Bnrm] in H_step2.
           sets_unfold in H_step2. 
           assert ({| BB_num := jump_dest_1 x0.(jump_info); st := a0 |} = x3). {
            rewrite <- B1. destruct x3. simpl. simpl in D4. rewrite D4. 
            simpl in D2. rewrite D2. reflexivity.
            }
           rewrite H. apply H_step2.
           assert (x2.(BB_num) = x4.(BB_num)) as T1. {
            (* Use H_step1 easy lyz *)
            simpl in H_step1. sets_unfold in H_step1. destruct H_step1 as [BBstate_ cond].
            destruct cond as [[cond1 cond2] cond3]. rewrite cond2. rewrite cond3. tauto.
           }
           rewrite <- T1. rewrite <- D3. tauto.

      -- intros. rename H into H_cmds_sem_main. (* cmd_sem -> BB_sem *)
        
         unfold cmd_list_sem in H_cmds_sem_main. simpl in H_cmds_sem_main. sets_unfold in H_cmds_sem_main.
         destruct H_cmds_sem_main as [? [H_step1 H_step2]].
         exists {| st := a; BB_num := BBnow'_.(block_num) |}.
         exists {| st := a0; BB_num := jump_dest_1 BBnow.(jump_info) |}.
         repeat split; try tauto. cbn[Bnrm].
         remember ({| BB_num := BBnow'_.(block_num); st := a |}) as bs1.
         remember ({| BB_num := jump_dest_1 BBnow.(jump_info); st := a0 |}) as bs2.
         pose proof BBs_sem_Asgn_split BBnow'_ BBs_ BBcmds_ x e bs1 bs2 as T1. destruct T1 as [T2 H_cmds_equiv_inv]. subst bs1. simpl. tauto. 
         (* 使用这个定理的四个条件 *)
         admit.
         admit.
         admit.
         unfold not. intros. admit.       
         clear T2.
         apply H_cmds_equiv_inv. 

         destruct H_asgn_equiv. clear err_cequiv inf_cequiv.
         sets_unfold in nrm_cequiv. rename nrm_cequiv into asgn_nrm_equiv.
         destruct H_cmd_equiv. clear err_cequiv inf_cequiv.
         sets_unfold in nrm_cequiv. rename nrm_cequiv into cmds_nrm_equiv.

         clear H_cmds_equiv_inv.
         specialize (asgn_nrm_equiv a x2). destruct asgn_nrm_equiv as [T1 T2]. pose proof T2 H_step1 as H_asgn_equiv_inv. clear T1 T2.
         destruct H_asgn_equiv_inv as [? [? [H_asgn_main [A1 [A2 [A3 A4]]]]]].
         cbn[Bnrm] in H_asgn_main. destruct H_asgn_main as [? H_asgn_main].
         exists x5. split.
         ++ unfold BAsgn_list_sem. cbn[Bnrm]. unfold BAsgn_denote. cbn[Bnrm]. simpl. 
            sets_unfold. exists x4. destruct H_asgn_main as [[[? H_asgn_main3] H_asgn_main2] H_asgn_main1].
            assert (x1 = {| X := x; E := e|}) as T1. {
              rewrite <- B1 in B2. simpl in B2. 
              pose proof cut_eq_part_l BB_cmd {| X := x; E := e |} x1 BBnow.(cmd) nil B2.
              rewrite H. reflexivity.
            }
            rewrite T1 in H_asgn_main3. simpl in H_asgn_main3.
            repeat split. exists x6.
            rewrite A1 in H_asgn_main3. rewrite H_asgn_main1 in H_asgn_main3. subst bs1. simpl. apply H_asgn_main3.
            rewrite A4. subst bs1. simpl. rewrite C5. tauto.
            rewrite H_asgn_main1. tauto.
        ++ specialize (cmds_nrm_equiv x2 a0). destruct cmds_nrm_equiv as [T1 T2]. clear T1. pose proof T2 H_step2 as H_cmds_equiv_inv.
           clear T2.
           destruct H_cmds_equiv_inv as [? [? [H_cmds_main [D1 [D2 [D3 D4]]]]]]. cbn[Bnrm] in H_cmds_main.
           unfold BB_list_sem. cbn[Bnrm]. sets_unfold.
           assert (x6 = x5) as T1. 
           {
            destruct H_asgn_main as [[cond1 cond2] cond3]. rewrite cond3.
            destruct x6. destruct x4. simpl in A2. simpl in D1. rewrite <- A2 in D1. rewrite D1. 
            simpl in D3. rewrite C5 in D3. simpl in A4. rewrite <- A4 in D3. rewrite D3. reflexivity.
           }
           assert (bs2 = x7) as T2. {
            destruct x7. rewrite Heqbs2. simpl in D2. rewrite D2.
            simpl in D4. rewrite D4. rewrite <- B1. simpl. tauto.
           }
           
           
           rewrite <- T1. rewrite T2. apply H_cmds_main.
      -- admit. (* err case *)
      -- admit. (* err case *)
      -- admit. (* inf case *)
      -- admit. (* inf case *) 
      -- simpl. rewrite B1. pose proof JmpInfo_inherit_for_list BBs x0 BBnum cmds. rewrite H. rewrite <- B1.  simpl. tauto.
    + destruct Qb_if_while as [contra _]. unfold is_asgn in contra. tauto.
  - unfold P. intros.
    assert (endinfo_prop: not_eq_to_any_BBnum BBnow.(jump_info).(jump_dest_1)). {
    (* 我们需要让传入的BBnow的endinfo，其实不是任何num，更多的是像一种标志。这个性质会在后面用到。
      本来我们可以这样解决这个问题：让所有BBnum从1开始，把endinfo设置为0，这样在Q和P中仅仅加入一条
      jmp_dest_1 BBnow.(jump_info) < BBnow.(block_num) 就可以解决了。
    *)
    (* !然而, 在构思初期，我们就在BBgen里，让其顺序排为BBnum = BBthen_num < BBelse_num < BBnext_num, 
    导致在BBthen的跳转目标为BBnext_num的情况下，我们不能用同一个Q或P去推理。因为不满足jmp_dest_1 BBnow.(jump_info) < BBnow.(block_num) *)
      admit.  
    }
    specialize (Qb_prop BBs BBnow BBnum).
    destruct H as [bbnow_T1 [bbnow_T2 bbnow_T3]].
    assert (jump_kind BBnow.(jump_info) = UJump /\
    jump_dest_2 BBnow.(jump_info) = None) as bbnow_T4. split. apply bbnow_T1. apply bbnow_T2.
    pose proof Qb_prop bbnow_T4 H0 H1 bbnow_T3 as Qb_prop.
    destruct Qb_prop as [Qb_asgn | Qb_if_while ].
    + destruct Qb_asgn as [contra _]. unfold is_asgn in contra. tauto.
    + destruct Qb_if_while as [? [BBnow'_ [BBs'_ [BBnum'_ [BBswo_ [A2 [A3 [A4 A5]]]]]]]]. 
      remember ((BB_generation.cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn)) as BBnow_mid.
      specialize (P_prop (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_).

      assert (jump_kind BBnow_mid.(jump_info) = UJump /\
      jump_dest_2 BBnow_mid.(jump_info) = None /\
      jump_condition BBnow_mid.(jump_info) = None) as T1. {
        pose proof JmpInfo_inherit BBs BBnow BBnum (CIf e c1 c2) as inherit_jmp.
        rewrite <- HeqBBnow_mid in inherit_jmp. repeat split; rewrite inherit_jmp; tauto.
      }

      assert ((BBnow_mid.(block_num) < BBnum'_)%nat) as T2. {
        pose proof inherit_lt_num_prop BBs BBnow BBnum (CIf e c1 c2) H0 as tran.
        rewrite <- HeqBBnow_mid in tran. rewrite A4 in tran. tauto. 
      }

      assert (BBnow_mid.(block_num) <>
      jump_dest_1 BBnow_mid.(jump_info)) as T3. {
        pose proof inherit_not_jmp_to_self BBs BBnow BBnum (CIf e c1 c2) H1 as tran.
        rewrite <- HeqBBnow_mid in tran.  tauto.
      }

      pose proof P_prop T1 T2 T3 as P_prop. destruct P_prop as [BBs'_p [BBnow'_p [BBcmds'_p [BBnum'_p [BBendnum_ T4]]]]].

      destruct T4 as [B1 [B2 [B3 [B4 [B5 [H_cmd_equiv B6]]]]]].

      exists (BBswo_ ++ BBnow'_p :: BBs'_p).
      exists BBnow'_. exists nil. exists (list_cmd_BB_gen cmd_BB_gen (CIf e c1 c2 :: cmds) BBs BBnow BBnum).(next_block_num). exists BBendnum_. 
      simpl in A2. 
      remember (to_result
      (list_cmd_BB_gen cmd_BB_gen c1 nil
         {|
           block_num := BBnum;
           commands := nil;
           jump_info :=
             {|
               jump_kind := UJump;
               jump_dest_1 := S (S BBnum);
               jump_dest_2 := None;
               jump_condition := None
             |}
         |} (S (S (S BBnum))))) as then_res.
      remember (         
        to_result
      (list_cmd_BB_gen cmd_BB_gen c2 nil
         {|
           block_num := S BBnum;
           commands := nil;
           jump_info :=
             {|
               jump_kind := UJump;
               jump_dest_1 := S (S BBnum);
               jump_dest_2 := None;
               jump_condition := None
             |}
         |}
         (list_cmd_BB_gen cmd_BB_gen c1 nil
            {|
              block_num := BBnum;
              commands := nil;
              jump_info :=
                {|
                  jump_kind := UJump;
                  jump_dest_1 := S (S BBnum);
                  jump_dest_2 := None;
                  jump_condition := None
                |}
            |} (S (S (S BBnum)))).(next_block_num))) as else_res.
      rewrite <- app_assoc in A2.

      assert (BBnow'_prop: BBnow'_ = {|
        block_num := BBnow.(block_num);
        commands := BBnow.(cmd);
        jump_info :=
          {|
            jump_kind := CJump;
            jump_dest_1 := BBnum;
            jump_dest_2 := Some (S BBnum);
            jump_condition := Some e
          |}
      |}). {
        pose proof cut_eq_part_list_l BasicBlock BBs as eq.
        specialize (eq (({|
        block_num := BBnow.(block_num);
        commands := BBnow.(cmd);
        jump_info :=
          {|
            jump_kind := CJump;
            jump_dest_1 := BBnum;
            jump_dest_2 := Some (S BBnum);
            jump_condition := Some e
          |}
      |} :: then_res ++ else_res) ++ BBnow_mid :: nil) (BBnow'_ :: BBs'_) A2).
        simpl in eq. inversion eq. reflexivity.
      }
      repeat split.
      -- simpl. destruct (BBswo_ ++ BBnow'_p :: BBs'_p) eqn:?. 
         (*矛盾*)
         ++ pose proof if_wont_be_nil e c1 c2 BBs BBswo_ BBnow BBnow'_ BBnum A3.
            pose proof not_nil_l BasicBlock BBswo_ (BBnow'_p :: BBs'_p) H2. tauto.
         ++ (*BBswo_的头就是BBthen！成立的！*)
            (*引理1: 从Heql中得到b就是head BBswo_*)
            pose proof extract_head_from_list BasicBlock BBswo_ (BBnow'_p :: BBs'_p) l b empty_block Heql as head_wo.
            (*引理2: 用A3得到BBswo_的头就是BBthen*)
            pose proof if_head_prop e c1 c2 BBswo_ BBs BBnow BBnow'_ BBnum A3 as num_prop.
            rewrite <- head_wo in num_prop. rewrite num_prop. rewrite BBnow'_prop. simpl. reflexivity. 
      -- rewrite BBnow'_prop. simpl. rewrite app_nil_r. tauto.
      -- rewrite BBnow'_prop. simpl. tauto.
      -- (*Use B5*) 
          pose proof if_separate_for_pcons1 e c1 c2 cmds BBs BBswo_ BBnow BBnow'_ BBnow_mid BBnum BBnum'_ HeqBBnow_mid A3 A4 as pconif1.
          pose proof if_separate_for_pcons2 e c1 c2 cmds BBs BBswo_ BBnow BBnow'_ BBnow_mid BBnum BBnum'_ HeqBBnow_mid A3 A4 as pconif2.
          rewrite pconif1. rewrite pconif2. rewrite B5. rewrite app_assoc_reverse. simpl. reflexivity.
      --intros. destruct H2 as [bs1 [bs2 [H_sem_full [C1 [C2 [C3 C4]]]]]].
        cbn[Bnrm] in H_sem_full.
        pose proof A5 as key1. pose proof H_cmd_equiv as key2.
        clear A5 H_cmd_equiv.
        (* 
        用A5和H_cmd_equiv！
        * 这里很可能会用到(BBnow BBsthen BBselse) | BBs_others这一刀的性质，在H_sem_full里把它切割出来
        * 如果我们还是关注H_sem_full的话，就必然会遇到
        ` BBs1 + BBnow + BBs2 == BBs1 + BBnow_A + BBnowB + BBs2
          这个性质，其中BBnow_A为cmds为空的Block（即BBnext）
          实际上对于BBnow_A的语义处理 只需要让它的前继BB跳过来就行
        *)
        assert (BBnow_mid_num_prop: BBnow_mid.(block_num) = S (S BBnum)). {
        rewrite HeqBBnow_mid. simpl. reflexivity.
        }
        destruct key1. clear err_cequiv inf_cequiv.
        rename nrm_cequiv into H_step1. sets_unfold in H_step1.
        destruct key2. clear err_cequiv inf_cequiv.
        rename nrm_cequiv into H_step2. sets_unfold in H_step2. simpl in H_step2.
        remember ({|
        block_num := BBnow'_.(block_num);
        commands := nil;
        jump_info := BBnow'_.(jump_info) |}) as BBnow_start.

(* !Range的性质引入  ==========================================================================================  *)

      pose proof BBgen_range_list_soundness_correct cmds as P_prop.
      pose proof BBgen_range_single_soundness_correct c as Q_prop.
      unfold Q_BBgen_range in Q_prop. unfold P_BBgen_range in P_prop.
      specialize (Q_prop BBnum BBnum'_ BBs BBnow (BBnow'_ :: BBs'_)).
      assert (m1: jump_kind BBnow.(jump_info) = UJump /\ jump_dest_2 BBnow.(jump_info) = None). tauto.
      assert (m2: to_result (cmd_BB_gen c BBs BBnow BBnum) = BBs ++ BBnow'_ :: BBs'_). {
      pose proof Q_add_BBs_in_generation_reserves_BB_sound c BBs BBnow BBnum as nil_eq.
      rewrite nil_eq. rewrite <- A2. unfold to_result.
      assert(eq: (cmd_BB_gen c nil BBnow BBnum).(BasicBlocks) = ({|
        block_num := BBnow.(block_num);
        commands := BBnow.(cmd);
        jump_info :=
          {| jump_kind := CJump; jump_dest_1 := BBnum; jump_dest_2 := Some (S BBnum); jump_condition := Some e |}
        |} :: then_res ++ else_res)). {
        rewrite Heqthen_res. rewrite Heqelse_res. 
        rewrite Heqc0.
        cbn [cmd_BB_gen]. simpl. reflexivity.
        }
      rewrite eq. rewrite HeqBBnow_mid. rewrite Heqc0. reflexivity.
      }

      assert (wo_tran: BBswo_ ++ (cmd_BB_gen c BBs BBnow BBnum).(BBn)::nil = BBs'_).
      {
      unfold to_result in m2. rewrite Heqc0. rewrite Heqc0 in m2. 
      rewrite A3 in m2. 
      rewrite app_assoc_reverse in m2. 
      assert (mid: (BBs ++ BBnow'_ :: nil) ++ BBswo_ ++ (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil =
      (BBs ++ BBnow'_ :: nil) ++ BBs'_). {
        assert ((BBnow'_ :: BBswo_) = (BBnow'_ :: nil) ++ BBswo_). {
          simpl. reflexivity.
        }
        rewrite H2 in m2. rewrite app_assoc_reverse in m2. 
        assert (BBnow'_ :: BBs'_ = BBnow'_ :: nil ++ BBs'_). {
          simpl. reflexivity.
        }
        rewrite H3 in m2. rewrite app_assoc in m2. rewrite m2. simpl. rewrite <- app_assoc. reflexivity.
      }
      pose proof cut_eq_part_list_l BasicBlock (BBs ++
      BBnow'_ :: nil) (BBswo_ ++ (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil) BBs'_ mid. tauto.
      }

      symmetry in A4. rewrite <- Heqc0 in A4. specialize (Q_prop m1 A4 m2 H0).

      specialize (P_prop BBnum'_ BBnum'_p (BBs ++ BBnow'_ :: BBswo_) BBnow_mid (BBnow'_p :: BBs'_p)).
      assert(n1: jump_kind BBnow_mid.(jump_info) = UJump /\ jump_dest_2 BBnow_mid.(jump_info) = None). tauto.
      assert(n2: to_result (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_) =
      (BBs ++ BBnow'_ :: BBswo_) ++ BBnow'_p :: BBs'_p). {
        pose proof add_BBs_in_generation_reserves_BB cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_ as key.
        unfold to_result in key. simpl in key.
        rewrite key in B5. 
        unfold to_result. rewrite <- B5. rewrite key. reflexivity.
      }
      specialize (P_prop n1 B2 n2).


(* !Range的性质引入结束  ==========================================================================================  *)


        assert (neq_1_2: bs1 <> bs2). {
          destruct bs1. destruct bs2. simpl. unfold not. intros. inversion H2.
          simpl in C4.  simpl in C3. rewrite BBnow'_prop in C3. simpl in C3. rewrite C3 in H4. rewrite C4 in H4. tauto.
        }

        assert (disjoint_num_set: BBnum_set (BBnow_start :: nil ++ BBswo_) ∩ BBnum_set (BBnow'_p :: nil ++ BBs'_p) == ∅). {
          destruct P_prop as [P_prop1 [P_prop2 P_prop3]].
          destruct Q_prop as [Q_prop1 [Q_prop2 Q_prop3]].
          (*用Q_props和P_props*)
          sets_unfold. intros. split.
          - intros. rename H2 into key. 
            destruct key as [cond1 cond2].
            unfold BBnum_set in cond1. destruct cond1 as [cond1_BB cond1_conds].
            destruct cond1_conds as [cond1_1 cond1_2].
            unfold BBnum_set in cond2. destruct cond2 as [cond2_BB cond2_conds].
            destruct cond2_conds as [cond2_1 cond2_2].
            destruct cond1_1 as [case1 | case2].
            * destruct cond2_1 as [case1' | case2'].
              ++ rewrite <- cond1_2 in cond2_2. rewrite <- case1 in cond2_2. rewrite <- case1' in cond2_2. 
                 rewrite B4 in cond2_2. rewrite BBnow_mid_num_prop in cond2_2. rewrite HeqBBnow_start in cond2_2. simpl in cond2_2. 
                 rewrite BBnow'_prop in cond2_2. simpl in cond2_2. lia. 
              ++ simpl in case2'. simpl in P_prop1. unfold all_ge in P_prop1. specialize (P_prop1 cond2_BB.(block_num)).
                assert (t: BBnum_set BBs'_p cond2_BB.(block_num)). {
                  unfold BBnum_set. exists cond2_BB. split. tauto. tauto. 
                }
                specialize (P_prop1 t). 
                rewrite <- cond1_2 in cond2_2. rewrite <- case1 in cond2_2. rewrite cond2_2 in P_prop1. 
                rewrite HeqBBnow_start in P_prop1. simpl in P_prop1. rewrite BBnow'_prop in P_prop1. simpl in P_prop1. 
                rewrite BBnow_mid_num_prop in T2. lia.
            * destruct cond2_1 as [case1' | case2']. 
              simpl in case2. simpl in Q_prop2. unfold all_ge in Q_prop2. specialize (Q_prop2 cond1_BB.(block_num)).
              assert (t: BBnum_set BBs'_ cond1_BB.(block_num)).
              {
                unfold BBnum_set. exists cond1_BB. split. rewrite <- wo_tran. 
                pose proof In_tail_inclusive BBswo_ cond1_BB (cmd_BB_gen c BBs BBnow BBnum).(BBn) case2. tauto.
                tauto.
              }
              specialize (Q_prop2 t). rewrite <- cond1_2 in cond2_2.
              rewrite <- case1' in cond2_2. rewrite B4 in cond2_2. rewrite BBnow_mid_num_prop in cond2_2. 
              rewrite <- cond2_2 in Q_prop2. 
              rewrite BBnow_mid_num_prop in T2. 
              pose proof neq_ssnum BBs BBswo_ cond1_BB BBnow BBnow'_ BBnum e c1 c2 A3 case2. lia.
              simpl in case2. simpl in case2'. 
              unfold all_ge in P_prop1. specialize (P_prop1 cond2_BB.(block_num)).
              assert (t: BBnum_set BBs'_p cond2_BB.(block_num)). {
                unfold BBnum_set. exists cond2_BB. split. tauto. tauto. 
              }
              specialize (P_prop1 t).
              unfold all_lt in Q_prop2. specialize (Q_prop2 cond1_BB.(block_num)).
              assert (t': BBnum_set (tl (BBnow'_ :: BBs'_)) cond1_BB.(block_num)).
              {
                unfold BBnum_set. exists cond1_BB. split. rewrite <- wo_tran. 
                pose proof In_tail_inclusive BBswo_ cond1_BB (cmd_BB_gen c BBs BBnow BBnum).(BBn) case2. tauto.
                tauto.
              }
              specialize (Q_prop2 t').
              lia.
          - intros. tauto.
        }

        assert (disjoint_jmp_dest_set: BBjmp_dest_set (BBnow_start :: nil ++ BBswo_) ∩ BBjmp_dest_set (BBnow'_p :: nil ++ BBs'_p) == ∅).
        {
          destruct P_prop as [P_prop1 [P_prop2 P_prop3]].
          destruct Q_prop as [Q_prop1 [Q_prop2 Q_prop3]].
          (*用Q_props和P_props*)
          sets_unfold. intros. split.
          - intros. rename H2 into key. destruct key as [key1 key2].
            sets_unfold in P_prop3. specialize (P_prop3 a1 key2).
            sets_unfold in Q_prop3. specialize (Q_prop3 a1).
            assert (t: BBjmp_dest_set (BBnow'_ :: BBs'_) a1). {
              unfold BBjmp_dest_set in key1. destruct key1 as [key1_BB key1_conds].
              destruct key1_conds as [key1_1 key1_2].
              unfold BBjmp_dest_set. simpl in key1_1. destruct key1_1 as [case1 | case2] .
              exists BBnow'_. split. left. tauto. rewrite <- case1 in key1_2. rewrite HeqBBnow_start in key1_2. simpl in key1_2. tauto.
              exists key1_BB. split. right. 
              rewrite <- wo_tran. pose proof In_tail_inclusive BBswo_ key1_BB (cmd_BB_gen c BBs BBnow BBnum).(BBn) case2. tauto.
              tauto.
            }
            specialize (Q_prop3 t).
            destruct P_prop3 as [P_prop3_1 | P_prop3_2].
            assert (contra: BBjmp_dest_set (BBnow'_ :: nil ++ BBswo_) a1).
            {
              unfold BBjmp_dest_set. simpl.  
              unfold BBjmp_dest_set in key1.
              destruct key1 as [key1_BB key1_conds]. destruct key1_conds as [key1_1 key1_2].
              destruct key1_1 as [case1 | case2].
              exists BBnow'_. split.
              - left. tauto.
              - rewrite <- case1 in key1_2. rewrite HeqBBnow_start in key1_2. simpl in key1_2. tauto.
              - exists key1_BB. split.
                + right. simpl in case2. tauto. 
                + tauto. 
            }
            * destruct Q_prop3 as [Q_prop3_1 | Q_prop3_2]; unfold section in *.
              ++ lia.
              ++ unfold unit_set in Q_prop3_2. pose proof unique_endinfo_if BBs BBswo_  BBs'_ e c1 c2 BBnow BBnow'_ BBnum A3.
                symmetry in wo_tran. rewrite Heqc0 in wo_tran. specialize (H2 wo_tran  endinfo_prop). sets_unfold in H2.
                rewrite <- Q_prop3_2 in H2. 
                specialize (H2 contra). lia.
            * unfold unit_set in P_prop3_2. pose proof JmpInfo_inherit BBs BBnow BBnum c. rewrite Heqc0 in H2.
              assert (contra: BBjmp_dest_set (BBnow'_ :: nil ++ BBswo_) a1).
              {
                unfold BBjmp_dest_set. simpl.  
                unfold BBjmp_dest_set in key1.
                destruct key1 as [key1_BB key1_conds]. destruct key1_conds as [key1_1 key1_2].
                destruct key1_1 as [case1 | case2].
                exists BBnow'_. split.
                - left. tauto.
                - rewrite <- case1 in key1_2. rewrite HeqBBnow_start in key1_2. simpl in key1_2. tauto.
                - exists key1_BB. split.
                  + right. simpl in case2. tauto. 
                  + tauto. 
              }
              rewrite <- HeqBBnow_mid in H2. rewrite H2 in P_prop3_2.
              pose proof unique_endinfo_if BBs BBswo_  BBs'_ e c1 c2 BBnow BBnow'_ BBnum A3.
              symmetry in wo_tran. rewrite Heqc0 in wo_tran. specialize (H3 wo_tran  endinfo_prop). sets_unfold in H3.
              rewrite <- P_prop3_2 in H3. tauto.
          - tauto.
        }

        assert (in_prop1: BB_num bs1 ∈ BBnum_set (BBnow_start :: nil ++ BBswo_)).
        {
          admit.
          (*TODO easy lyz*)
        }

        assert (in_prop2: BB_num bs2 ∈ BBjmp_dest_set (BBnow'_p :: nil ++ BBs'_p)).
        {
          sets_unfold. unfold BBjmp_dest_set. simpl. destruct BBs'_p. 
          + simpl. exists BBnow'_p. split. left. tauto. simpl. left. destruct B1 as [B11 B12]. 
            rewrite B11. pose proof JmpInfo_inherit BBs BBnow BBnum (CIf e c1 c2) as inherit_jmp.
            rewrite <- HeqBBnow_mid in inherit_jmp. rewrite inherit_jmp.
             rewrite C4. tauto.
          + 
            exists (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_).(BBn).
            split.
            - right. pose proof exact_tail_from_list BasicBlock (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_).(BasicBlocks) (BBs ++ BBnow'_ :: BBswo_) (b :: BBs'_p).
              specialize (H2 (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_).(BBn) BBnow'_p).
              assert(not_nil: b :: BBs'_p <> nil). {
                unfold not. intros. discriminate H3.
              }
              specialize (H2 B5 not_nil). tauto.
            - pose proof JmpInfo_inherit_for_list (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_ cmds as jmp_info.
              rewrite jmp_info.  
              pose proof JmpInfo_inherit BBs BBnow BBnum (CIf e c1 c2) as inherit_jmp.
              rewrite <- HeqBBnow_mid in inherit_jmp. rewrite inherit_jmp.
              left. rewrite C4. tauto. 
        }

        
        assert (exists (x: BB_state), Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_)) bs1 x /\ Bnrm (BB_list_sem (BBnow'_p :: BBs'_p)) x bs2) as H_sep. {
          pose proof an_over_pass_bridge BBswo_ BBs'_p BBnow_start BBnow'_p bs1 bs2 H_sem_full neq_1_2 disjoint_num_set as bridge.
          specialize (bridge disjoint_jmp_dest_set).
          specialize (bridge in_prop1).
          specialize (bridge in_prop2).
          tauto.
        }

        destruct H_sep as [bb_mid [H_step1_main H_step2_main]].
        cbn[cmd_list_sem]. cbn[nrm]. sets_unfold. exists bb_mid.(st).
        (* 这个时候我们就分两步，分别使用H_step1和H_step2来走 *)
        specialize (H_step1 a bb_mid.(st)).


        assert (now_mid_block_num: BBnow_mid.(block_num) = (S (S BBnum))). {
        rewrite HeqBBnow_mid. simpl. reflexivity.
        }

        assert(key_num_eq: BB_num bb_mid = S (S BBnum)). {
        (*利用H_step2_main + 分离性质*)
        (* 
        1. 由H_step1_main得到BB_mid的num一定在(BBnow_start :: nil ++ BBswo_)的jmpdest之中，而我们有其范围
        2. 由H_step2_main得到BB_mid的num一定在((BBnow'_p :: BBs'_p)) 的num之中，而我们也有其范围。
        两个范围唯一的交点就是S (S BBnum)
        *)



        destruct Q_prop as [_ [_ Q_prop]]. destruct P_prop as [P_prop [_ _]].
        pose proof BBs_bs2_in_BB_jmp_set (BBnow_start :: nil ++ BBswo_) bs1 bb_mid H_step1_main as key1. 
        pose proof BBs_bs1_in_BB_num_set (BBnow'_p :: BBs'_p) bb_mid bs2 H_step2_main as key2.
        sets_unfold in Q_prop. specialize Q_prop with (BB_num bb_mid).
        unfold all_ge in P_prop. unfold tl in P_prop. 
        destruct key1 as [case_a | case_b].
        (*BBjmp_dest_set (BBnow_start :: nil ++ BBswo_) (BB_num bb_mid)*)
        + destruct key2 as [case_a' | case_b'].
          ++ assert (subseteq: BBjmp_dest_set (BBnow'_ :: BBs'_) (BB_num bb_mid)). {
          (* 显然成立，因为case_a*)
            unfold BBjmp_dest_set. simpl. 
            unfold BBjmp_dest_set in case_a. simpl in case_a. destruct case_a as [case_a_BB case_conds].
            destruct case_conds as [cond1_ cond2_].
            destruct cond1_ as [cond1_1 | cond1_2]. 
            * exists BBnow'_. rewrite <- cond1_1 in cond2_. rewrite HeqBBnow_start in cond2_. simpl in cond2_. split.
              ** left. tauto.
              **  tauto.
            * exists case_a_BB. split.
              ** right. pose proof In_tail_inclusive BBswo_ case_a_BB (cmd_BB_gen c BBs BBnow BBnum).(BBn) cond1_2. rewrite wo_tran in H2. tauto.
              ** tauto. 
          }
          specialize (Q_prop subseteq). 
          destruct Q_prop as [case1 | case2].
          (* section BBnum BBnum'_ (BB_num bb_mid) *)
          * unfold section in case1. simpl in case1. destruct case1 as [_ cond].
            pose proof destruct_in_BBnum_set BBnow'_p BBs'_p (BB_num bb_mid) case_a' as key.
            destruct key as [case1 | case2].
            ** rewrite B4 in case1. rewrite case1. tauto.
            ** specialize (P_prop (BB_num bb_mid) case2). lia.
          (* unit_set (jump_dest_1 BBnow.(jump_info)) (BB_num bb_mid) *)
          * unfold unit_set in case2. (* 需要证明BBnow的jmpinfo(即endinfo，最后只会在BBn中, 不会在任何其他block里。从而根据BBs'_ = BBswo_ ++ BBn::nil 导出矛盾*) 
            unfold not_eq_to_any_BBnum in endinfo_prop. specialize endinfo_prop with (BB_num bb_mid). lia.
          (* bb_mid = bs2, bs2的num就是endinfo，但是从case-a中知道，bb_mid不可能拿到endinfo，因为它并不在BBn的jmpdest里*)
            ++ symmetry in wo_tran. rewrite Heqc0 in wo_tran. pose proof unique_endinfo_if BBs BBswo_ BBs'_ e c1 c2 BBnow BBnow'_ BBnum A3 wo_tran endinfo_prop as key.
             sets_unfold in key. rewrite case_b' in case_a. rewrite C4 in case_a.
             assert (contra_: BBjmp_dest_set (BBnow'_ :: nil ++ BBswo_) (jump_dest_1 BBnow.(jump_info))). {
              rewrite HeqBBnow_start in case_a. unfold BBjmp_dest_set in case_a. 
              destruct case_a as [focus_bb cond]. 
              destruct cond as [cond1 cond2].
              destruct cond1 as [cond11 | cond12].
              unfold BBjmp_dest_set. simpl. exists BBnow'_. split.
              ** left. tauto.
              ** rewrite <- cond11 in cond2. simpl in cond2. tauto.
              ** unfold BBjmp_dest_set. simpl. exists focus_bb. split.
                -- right. tauto.
                -- tauto.
             }
             tauto.
             
        + (* case_b: bs1 = bb_mid*) destruct key2 as [case_a' | case_b'].
          * unfold BBnum_set in case_a'. destruct case_a' as [case_a'_bb case_a'_cond].
            specialize P_prop with (BB_num bb_mid).
            destruct case_a'_cond as [case_a'_cond1 case_a'_cond2].
            destruct case_a'_cond1 as [case_a'_cond1_1 | case_a'_cond1_2].
            - rewrite <- case_a'_cond1_1 in case_a'_cond2. rewrite B4 in case_a'_cond2. rewrite <- BBnow_mid_num_prop. rewrite case_a'_cond2. tauto.
            - assert (tran: BBnum_set BBs'_p (BB_num bb_mid)). {
              unfold BBnum_set. exists case_a'_bb. split.
              ** tauto.
              ** tauto.
              }
              specialize (P_prop tran). rewrite <- case_b in P_prop. rewrite C3 in P_prop. 
              rewrite BBnow'_prop in P_prop. simpl in P_prop. lia.
          * rewrite case_b' in case_b. 
            destruct bs1. destruct bs2. simpl in *. rewrite C3 in case_b. rewrite C4 in case_b. 
            inversion case_b. rename H3 into tmp. rewrite BBnow'_prop in tmp. simpl in tmp. tauto.
        }

        assert (wo_disjoint_prop: ~ BBnow_start.(block_num) ∈ BBnum_set (BBswo_)). {
          pose proof disjoint_num_prop_wo_last_if BBs BBswo_ BBnow BBnow'_ BBnum e c1 c2 A3 as key. rewrite HeqBBnow_start. simpl. simpl in key. rewrite BBnow'_prop.
          simpl. tauto.
        }

        sets_unfold in wo_disjoint_prop. unfold not in wo_disjoint_prop.

        assert (neq_bs1_bbmid: bs1 <> bb_mid).
        {
          intros contra. 
          rewrite <-  contra in key_num_eq. rewrite C3 in key_num_eq. rewrite BBnow'_prop in key_num_eq.
          cbn [block_num] in key_num_eq. lia.
        }

        assert (sep_prop: separate_property BBnow'_ BBs'_). {
        unfold separate_property.
        sets_unfold. intros.
        split.
        -  destruct Q_prop as [_ [_ focus]]. 
          sets_unfold in focus. specialize (focus a1). 
          intros. rename H2 into intr.
          destruct intr as [intr1 intr2].
          specialize (focus intr2). unfold BBnum_set in intr1. destruct intr1 as [iBB [cond1 cond2]].
          simpl in cond1. destruct cond1 as [cond11 | cond12].
          -- rewrite <- cond11 in cond2. rewrite BBnow'_prop in cond2. simpl in cond2. destruct focus as [case1 | case2].
            ** unfold section in case1. lia.
            ** unfold unit_set in case2. lia.
          -- tauto.
        - intros. tauto. 
      }

        assert (sep_prop_wo: separate_property BBnow'_ BBswo_). {
        unfold separate_property.
        unfold separate_property in sep_prop.
        sets_unfold. sets_unfold in sep_prop.
        intros.
        specialize (sep_prop a1).
        destruct sep_prop as [sep_prop1 sep_prop2].
        split. 
        - intros. rename H2 into wo_sep. assert (tmp: BBnum_set (BBnow'_ :: nil) a1 /\ BBjmp_dest_set (BBnow'_ :: BBs'_) a1).  admit. (*TODO, easy lyz use wo_sep*)
          tauto.
        - intros. tauto. 
        }

        assert (Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_)) bs1 bb_mid -> Bnrm (BDenote_concate (BB_jmp_sem BBnow'_) (BB_list_sem BBswo_)) bs1 bb_mid) as M1. {
        
        (* 
          思路:
          1. bs1不能是bb_mid, 所以一定要走一步
          2. 走一步的话，bs1的num是BBnow_start的num，所以只能从BBnow_start出发
        *)
        intros.
        rename H2 into pre.
        pose proof BBs_list_sem_exists_BB_bs1_x (BBnow_start :: nil ++ BBswo_) bs1 bb_mid pre as pre_stepin.
        clear pre.
        destruct pre_stepin as [case1 | case2].
        - destruct case1 as [case1_BB [case1_bbstate [case1_cond1 [case1_cond2 case1_cond3]]]].
          pose proof single_step_jmp_property_for_bs1 case1_BB bs1 case1_bbstate case1_cond2 as step1. 
          assert (tmp: case1_BB.(block_num) = BBnow_start.(block_num)). {
            rewrite HeqBBnow_start. simpl. rewrite step1. rewrite C3. reflexivity.
          }
          pose proof must_be_head_with_num_restriction BBnow_start case1_BB BBswo_ case1_cond1 tmp wo_disjoint_prop as step2.
          clear tmp. clear case1_cond1.
          rewrite step2 in *.
          unfold BDenote_concate. simpl. sets_unfold. exists case1_bbstate. split.
          + unfold BB_sem in case1_cond2. simpl in case1_cond2. sets_unfold in case1_cond2. 
            destruct case1_cond2 as [mid_x conds].
            destruct conds as [c1_ c2_].
            rewrite HeqBBnow_start in c1_. simpl in c1_. sets_unfold in c1_.
            rewrite <- c1_ in c2_. rewrite HeqBBnow_start in c2_. simpl in c2_. tauto.
          + pose proof simplify_listsem_with_mismatch_num case1_bbstate bb_mid BBnow_start BBswo_ as step3.
            assert (pre1: BBnow_start.(block_num) <> BB_num case1_bbstate). {
              rewrite HeqBBnow_start. simpl. unfold BB_sem in case1_cond2.
              simpl in case1_cond2. sets_unfold in case1_cond2. destruct case1_cond2 as [mid_x conds].
              destruct conds as [c1_ c2_]. rewrite HeqBBnow_start in c1_. simpl in c1_. sets_unfold in c1_.
              rewrite <- c1_ in c2_. rewrite HeqBBnow_start in c2_. simpl in c2_. unfold BJump_sem in c2_.
              admit. (*TODO easy lyz*)
            }

            assert (pre2: BBnum_set (BBnow_start :: nil) ∩ BBjmp_dest_set (BBnow_start :: BBswo_) == ∅). {

            unfold separate_property in sep_prop_wo. 
            admit. (*TODO, easy lyz*)
            }
            specialize (step3 pre1 pre2 case1_cond3). tauto.
        
        - tauto. (*矛盾*)
  
      } 

         assert(step1: (exists bs1 bs2 : BB_state,
         Bnrm (BDenote_concate (BB_jmp_sem BBnow'_) (BB_list_sem BBswo_)) bs1 bs2 /\
         st bs1 = a /\
         st bs2 = st bb_mid /\
         BB_num bs1 = BBnow.(block_num) /\ BB_num bs2 = S (S BBnum))). {
          exists bs1. exists bb_mid.
          repeat split; try tauto.
          rewrite C3. rewrite BBnow'_prop. simpl. reflexivity.
         }

        destruct H_step1 as [r _]. specialize (r step1). 
         
        split. tauto.

        (*分支2*)
        specialize (H_step2 bb_mid.(st) a0).
        destruct H_step2 as [H_step2_forward T4]. clear T4.
        apply H_step2_forward. exists bb_mid. exists bs2.
        simpl in H_step2_forward.
        cbn[Bnrm]. repeat split.
        * unfold BB_list_sem in H_step2_main. 
          cbn[Bnrm] in H_step2_main. sets_unfold in H_step2_main.
          assert (BBnow_mid.(cmd) = nil). {
            pose proof if_cmdgen_prop1 e c1 c2 BBs BBnow BBnum as t.
            rewrite <- HeqBBnow_mid in t. tauto.
            (*CIf性质 *)
          }
          rewrite H2 in B3. rewrite append_nil_l in B3.
          rewrite <- B3. apply H_step2_main.
        * apply C2.
        * rewrite B4. rewrite key_num_eq. pose proof if_BBn_num_prop e c1 c2 BBs BBnow BBnum as t.
          rewrite <- HeqBBnow_mid in t. rewrite t. reflexivity.
        * rewrite C4. pose proof JmpInfo_inherit BBs BBnow BBnum (CIf e c1 c2) as t. 
          rewrite <- HeqBBnow_mid in t. rewrite <- t. reflexivity.
      -- intros. (* 这半边应该是完全类似的 *)
         cbn[cmd_list_sem] in H2. cbn[nrm] in H2.
         sets_unfold in H2. destruct H2 as [? [H_step1_main H_step2_main]].
         exists {| st := a; BB_num := BBnow'_.(block_num) |}.
         exists {| st := a0; BB_num := jump_dest_1 BBnow.(jump_info) |}.
         repeat split. cbn[Bnrm].
         remember ({| BB_num := BBnow'_.(block_num); st := a |}) as bs1.
         remember ({| BB_num := jump_dest_1 BBnow.(jump_info); st := a0 |}) as bs2.
         remember ({|
          block_num := BBnow'_.(block_num);
          commands := nil;
          jump_info := BBnow'_.(jump_info) |}) as BBnow_start.
         (* 前一种情况切一刀的反向版本 *)
         assert ((exists (x: BB_state), Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_)) bs1 x /\ Bnrm (BB_list_sem (BBnow'_p :: BBs'_p)) x bs2) -> Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_ ++ BBnow'_p :: BBs'_p)) bs1 bs2) as H_sep. {
          intros.
          pose proof an_over_pass_bridge_reverse (BBnow_start :: nil ++ BBswo_) (BBnow'_p :: BBs'_p) bs1 bs2 as bridge.
          specialize (bridge H2). tauto.
         }
         apply H_sep. clear H_sep. 
         (* 这个时候就拿H_step1/H_step2的中间状态 *)
         exists {| st := x; BB_num := BBnow'_p.(block_num) |}.
         remember {| st := x; BB_num := BBnow'_p.(block_num) |} as bs3.
         pose proof A5 as key1. pose proof H_cmd_equiv as key2.
         clear A5 H_cmd_equiv.
         destruct key1. clear err_cequiv inf_cequiv.
         rename nrm_cequiv into H_step1. sets_unfold in H_step1.
         destruct key2. clear err_cequiv inf_cequiv.
         rename nrm_cequiv into H_step2. sets_unfold in H_step2.
         split.
         specialize (H_step1 a x). destruct H_step1 as [T4 H_step1_inv]. clear T4.
         pose proof H_step1_inv H_step1_main as H_step1_inv.
         destruct H_step1_inv as [? [? [C1 [C2 [C3 [C4 C5]]]]]].
         assert (x0 = bs1) as T4. {
          subst bs1. destruct x0. simpl in C2. rewrite C2. 
          simpl in C4. rewrite C4. rewrite BBnow'_prop. simpl. tauto.
         }
         assert (x1 = bs3) as T5. {
          subst bs3. destruct x1. simpl in C3. simpl in C5.
          rewrite C3. rewrite B4. rewrite C5.
          pose proof if_BBn_num_prop e c1 c2 BBs BBnow BBnum.
          rewrite <- H2. subst BBnow_mid. tauto.
         }
         rewrite T4 in C1. rewrite T5 in C1.
         assert (Bnrm (BDenote_concate (BB_jmp_sem BBnow'_) (BB_list_sem BBswo_)) bs1 bs3 -> Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_)) bs1 bs3) as M1. {
            intros.
            unfold BDenote_concate in H2. simpl in H2. sets_unfold in H2.
            rename H2 into pre.
            destruct pre as [pre_st pre_conds]. destruct pre_conds as [pre_conds1 pre_conds2].
            destruct pre_conds2 as [iter_n sem].
            rewrite HeqBBnow_start. simpl. sets_unfold.
            exists (S iter_n). simpl. sets_unfold. exists pre_st. split.
            - left. exists bs1. split.
              + tauto.
              + tauto.
            - pose proof Iter_shrink BBswo_ BBnow'_ iter_n pre_st bs3 sem. tauto.
         }
         apply M1. apply C1.

         (* 接下来考虑第二步的情况 *)
         specialize (H_step2 x a0).
         destruct H_step2 as [T4 H_step2_inv]. clear T4.
         pose proof H_step2_inv H_step2_main as H_step2_inv.
         destruct H_step2_inv as [? [? [C1 [C2 [C3 [C4 C5]]]]]].
         assert (x0 = bs3) as T4. {
          subst bs3. destruct x0. simpl in C2. rewrite C2. 
          simpl in C4. rewrite C4. tauto.
         }
         assert (x1 = bs2) as T5. {
          subst bs2. destruct x1. simpl in C3. simpl in C5. 
          rewrite C3. rewrite C5. 
          pose proof JmpInfo_inherit BBs BBnow BBnum (CIf e c1 c2).
          subst BBnow_mid. rewrite <- H2. tauto.
         }
         rewrite T4 in C1. rewrite T5 in C1.
         cbn[Bnrm] in C1.
         assert (BBcmds'_p = BBnow'_p.(cmd)) as T6. {
            (* BBnow_mid.(cmd)是nil，和上文类似*)
            pose proof if_cmdgen_prop1 e c1 c2 BBs BBnow BBnum as t.
            rewrite <- HeqBBnow_mid in t. rewrite t in B3. rewrite B3. reflexivity.
         }
         rewrite T6 in C1. apply C1.
      -- admit. (* err case *)
      -- admit. (* err case *)
      -- admit. (* inf case *)
      -- admit. (* inf case *)
      -- pose proof JmpInfo_inherit_for_list BBs BBnow BBnum (CIf e c1 c2 :: cmds). tauto.
    - admit. (* 2024/1/9，和老师沟通后，确认while地情况不需要在归纳或互递归中考虑。*)
Admitted. 


Section BB_sound.


Variable cmd_BB_gen_sound: forall (c: cmd), Qb c.

Fixpoint cmd_list_BB_gen_sound (cmds: list cmd): P cmds cmd_BB_gen :=
  match cmds with
  | nil => P_nil cmd_BB_gen
  | c :: cmds0 => P_cons c cmds0 (cmd_BB_gen_sound c) (cmd_list_BB_gen_sound cmds0)
  end.

End BB_sound.

Fixpoint cmd_BB_gen_sound (c: cmd): Qb c :=
  match c with
  | CAsgn x e => Q_asgn x e
  | CIf e cmds1 cmds2 =>
      Q_if e cmds1 cmds2
        (cmd_list_BB_gen_sound cmd_BB_gen_sound cmds1)
        (cmd_list_BB_gen_sound cmd_BB_gen_sound cmds2)
  | CWhile cmds1 e cmds2 =>
      Q_while cmds1 e cmds2
        (cmd_list_BB_gen_sound cmd_BB_gen_sound cmds1)
        (cmd_list_BB_gen_sound cmd_BB_gen_sound cmds2)
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