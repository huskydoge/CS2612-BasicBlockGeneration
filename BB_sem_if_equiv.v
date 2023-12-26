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



(*
如果满足几条分离性质，那么有
  (start, s1), (end, s2) \in (I U ((R1 U R234) o (R1 U R234))*  -> (start, s1), (end, s2) \in (R1 o (R234)*
**)
Lemma serperate_step_aux1:
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


Lemma serperate_step_aux2:
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


(* #TODO 切第二刀，把then和else切开来*)
Lemma serperate_step_aux3:
  forall (BBs1 BBs2: list BasicBlock)(bs1 bs2: BB_state),
  (BBnum_set BBs1) ∩ (BBnum_set BBs2) = ∅ ->
  (BB_num bs1) ∈ (BBnum_set BBs1) ->
  (BBjmp_dest_set BBs1) ∩ (BBnum_set BBs2) = ∅ ->
  (BB_num bs2) ∈ (BBjmp_dest_set BBs1) ->
  Bnrm (BB_list_sem (BBs1 ++ BBs2)) bs1 bs2 ->
  Bnrm (BB_list_sem (BBs1)) bs1 bs2.
Proof.
Admitted.



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
    ((BDenote_concate (BB_jmp_sem BBnow) (BB_list_sem BBs)).(Bnrm) bs1 bs2) = (BB_list_sem (BBnow' :: nil ++ BBs)).(Bnrm) bs1 bs2.
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
  pose proof serperate_step_aux1 bs1 bs2 BBnow' BBs H3 H4.
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




Lemma Q_if:
  forall (e: expr) (c1 c2: list cmd),
  P c1 (cmd_BB_gen) -> P c2 (cmd_BB_gen) -> Qb (CIf e c1 c2).
Proof.
  intros.
  unfold Qb. intros. right. 
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
  (*此时已经生成的 BBs_ := BBs ++ BBnow'::nil ++ BB_then::nil, 注意这里的BB_then和BBnow不同！它里面的commands可能由于CAsgn有填充*)
  (*此时的BBnow则应该用BB_then了*)
  (*接下来要拿c1到生成的基本块列表后，对else分支做同样的事情*)
  (* Get correct num。 我们首先要拿到c1 gen之后，下一个用于分配的BBnum(即BB_num2)，所以要先destruct H，即从P c1的命题中得到这个信息 *)
  unfold P in H. specialize (H (BBs ++ BBnow'::nil) BB_then BB_num1). 
  
  (*接下来要拿c1到生成的基本块列表后，对else分支做同样的事情*)
  (* Get correct num。 我们首先要拿到c1 gen之后，下一个用于分配的BBnum(即BB_num2)，所以要先destruct H，即从P c1的命题中得到这个信息 *)
  destruct H as [BBs_then [BB_then' [ BB_cmds_then [BB_num2 [?]]]]].
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
  (*此时已经生成的 BBs_ := BBs ++ BBnow::nil ++ BB_then' ++ BBs_then, 注意这里的BB_then'和BB_then不同！它里面的commands可能由于CAsgn有填充*)
  (*此时的BBnow则应该用BB_else了*)

  unfold P in H0. 
  specialize (H0 (BBs ++ BBnow'::nil ++ BB_then'::nil ++ BBs_then) BB_else BB_num2).

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
  set(BBs'_ := BB_then'::nil ++ BBs_then ++ BB_now_else::nil ++ BBs_else ++ BB_next::nil). (*这里BBs_else已经包括了else分支最后一个BB，然后就是无条件跳转到BBnext了，还要接上一个BBnext，*)
  set(BBs_wo_last_ := BB_then'::nil ++ BBs_then ++ BB_now_else::nil ++ BBs_else). 
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
        assert (BBs ++ BBnow' :: BB_then' :: BBs_then = (BBs ++ BBnow' :: nil) ++ BB_then' :: BBs_then).
        {
          rewrite <- app_assoc. simpl. reflexivity.
        }
        rewrite <- H13. rewrite H10. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. 
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
  - cbn [cmd_BB_gen]. simpl. admit. (*模仿上面的即可*)
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
      rewrite H11 in H8. (* BB_then'.(cmd) = BB_cmds_then *)
      sets_unfold.



      pose proof BDenote_concat_equiv_BB_list_sem BBnow' BBs_wo_last_.
      rewrite H16 in H14.
      remember ({|
      block_num := BBnow'.(block_num);
      commands := nil;
      jump_info := BBnow'.(jump_info)
    |}) as BB_jmp.
         my_destruct H14.
         pose proof (unfold_once (BB_jmp :: nil ++ BBs_wo_last_)).
         pose proof serperate_step_aux1.
         specialize (H22 x1 x2 BB_jmp BBs_wo_last_).
         assert (separate_property BB_jmp BBs_wo_last_). admit. (*分离性质1*)
         assert (BB_restrict BB_jmp BBs_wo_last_ x1.(BB_num) x2.(BB_num)). admit. (*分离性质2*)
         assert (((Rels.id
         ∪ Bnrm (BB_sem_union (BB_jmp :: nil ++ BBs_wo_last_))
           ∘ Bnrm (BB_list_sem (BB_jmp :: nil ++ BBs_wo_last_))) x1 x2
        :
        Prop)). admit.
        specialize (H22 H23 H24 H25).
        rename H15 into key1.  
        clear H23 H24 H25 H21 H16.


         pose proof true_or_false e a.
         assert (exists i : int64, EDenote.nrm (eval_expr e) a i). {
          admit. (* 不考虑出错或无穷的情况 *)
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
                    apply unfold_once in step2. apply serperate_step_aux1 in step2.
                    apply sem_start_end_with in step2. destruct step2 as [bs'' [step2 step3]].  
                    ++++ apply unfold_once. apply serperate_step_aux2. apply sem_start_end_with_2.
                      exists bs''. split. 
                      assert (bs1_ = bs'). admit. rewrite H5. 
                      assert (BB_then' = {|
                      block_num := BB_then'.(block_num);
                      commands := BB_cmds_then;
                      jump_info := BB_then'.(jump_info)
                      |}). admit.
                      rewrite H14 in step2. apply step2.
                    +++ (*第二刀*)
                      apply serperate_step_aux3 in step3.
                      apply step3.
                      admit. admit. admit. admit.
                    ++++ admit. (*只要是从一个Block开始，新生成的block，那它就满足分离性质*)
                    ++++ admit. (*只要是从一个Block开始，新生成的block，那它就满足分离性质*)
                    
               *** apply H18.
               *** rewrite H9. reflexivity.
               *** apply H20.
               (* BB_then_num的语义 *)

          ** admit. (*test false的情况*)
        - admit. 
        - admit. 
        - admit. 
        - admit. 
        - admit.
Admitted.
