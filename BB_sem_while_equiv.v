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
Require Import Main.BB_gen_properties.

Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.
Import BDenote.

(* seperate_sem_union_aux is same as if *)
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
to separate BBnow, same as if_equiv
 *)
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

(* Disjoint properties needed *)
Definition Qd_while (e: expr) (pre body: list cmd): Prop :=
  forall(BBs: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat),
  let res := cmd_BB_gen(CWhile pre e body) BBs BBnow BBnum in
  let BBres := res.(BasicBlocks) ++ (res.(BBn) :: nil) in
  
(* The jump info of BBnow *)
  (BBnow.(jump_info).(jump_kind) = UJump /\ BBnow.(jump_info).(jump_dest_2) = None) ->
(* CWhile Conditions *)
  forall BBnow' BBs' BBs_wo_last
    BB_pre_num BB_body_num BB_next_num
    BB_pre BB_body BBs_pre BBs_body
    BB_now_pre BB_now_body
    BB_num1 BB_num2,
(* BBs property *)
res.(BasicBlocks) ++ (res.(BBn) :: nil) =  BBs ++ (BBnow' :: nil) ++ BBs' -> res.(BasicBlocks) =  BBs ++ (BBnow' :: nil) ++ BBs_wo_last ->
(* number property 1 *)
BB_pre_num = BBnum -> BB_body_num = S(BB_pre_num) -> BB_next_num = S(BB_body_num) -> BB_num1 = S(BB_next_num)->
(* Special BasicBlocks *)
BB_pre = {|block_num := BB_pre_num; commands := nil;
        jump_info := {|
          jump_kind := CJump;
          jump_dest_1 := BB_body_num; 
          jump_dest_2 := Some BB_next_num; 
          jump_condition := Some e
          |};
        |} ->
BB_body = {|block_num := BB_body_num;
        commands := nil;
        jump_info := {|
          jump_kind := UJump;
          jump_dest_1 := BB_pre_num; 
          jump_dest_2 := None; 
          jump_condition := None
          |};
        |} ->
BBnow' = {|block_num := BBnow.(block_num);
      commands := BBnow.(commands);
      jump_info := {|
         jump_kind := UJump;
         jump_dest_1 := BB_pre_num; 
         jump_dest_2 := None; 
         jump_condition := None
         |};
      |} ->
(* Generated List BasicBlock Properties *)
to_result (list_cmd_BB_gen cmd_BB_gen pre (nil) BB_pre BB_num1) =  BB_now_pre::nil ++ BBs_pre ->
to_result (list_cmd_BB_gen cmd_BB_gen body (nil) BB_body BB_num2) =  BB_now_body::nil ++ BBs_body ->
(* Number Property 2*)
BB_num2 = (list_cmd_BB_gen cmd_BB_gen pre (nil) BB_pre BB_num1).(next_block_num) ->
BB_now_pre.(block_num) = BB_pre_num ->
BB_now_body.(block_num) = BB_body_num ->
lt BBnow.(block_num) BBnum  -> (*BBnow的num小于下一个分配的num*)
BBnow.(block_num) <> jump_dest_1 BBnow.(jump_info) -> (*BBnow不会无条件跳转到自身*)
(* Other info needed can be written here *)

(* disjoint properties can be added here *)
  (separate_property BBnow' BBs_wo_last).

Lemma Qd_while_sound:
  forall (e: expr) (pre body: list cmd),
    Qd_while e pre body.
Proof.
Admitted.

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
  remember(to_result(BB_pre_generated_results) ++ to_result(BB_body_generated_results)) as BBs_wo_last. 
  remember(BBs_wo_last ++ BB_next :: nil) as BBs'.
  exists BBnow'. exists BBs'. exists BB_next_num. exists BBs_wo_last.

  (*assert 1*)
  assert (BBs_prop: (cmd_BB_gen (CWhile pre e body) BBs BBnow BB_pre_num).(BasicBlocks) ++
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
  assert (BBs_wo_last_prop:(cmd_BB_gen (CWhile pre e body) BBs BBnow BB_pre_num).(BasicBlocks) = BBs ++ (BBnow' :: nil) ++ BBs_wo_last).
  {
  cbn[cmd_BB_gen]. simpl.
   subst BB_pre_num. subst BB_body_num. subst BB_next_num. subst BB_num1.
  rewrite <- HeqBBnow'.  rewrite <- HeqBB_pre. 
  rewrite <- HeqBB_pre_generated_results. subst BB_num2. rewrite <- HeqBB_body.
  rewrite <- HeqBB_body_generated_results. rewrite HeqBBs_wo_last. reflexivity.
  }

  (*assert 3*)
  assert(BBn_block_num_prop: ((cmd_BB_gen (CWhile pre e body) BBs BBnow BB_pre_num).(BBn)).(block_num) = BB_next_num).
  {
  cbn[cmd_BB_gen]. simpl. subst BB_pre_num. subst BB_next_num. reflexivity.
  }

  repeat split.
  + tauto.
  + tauto.

(* You may use these methods:
  (*cmd推BB*)
  + intros. rename H1 into main_prop.
    destruct main_prop as [bs1 [bs2 [sem_cons [ st_cond1 [st_cond2 [num_cond1 num_cond2]]]]]].
    cbn [cmd_sem]. cbn [nrm].
    admit.
  (*BB推cmd*)
  + intros. rename H1 into main_prop. admit.

  (*! DONT CARE: err and inf*)
  + admit.
  + admit.
  + admit.
  + admit.
 *)
Admitted.