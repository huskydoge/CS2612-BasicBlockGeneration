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


(* ! Check correctness, important *)
Lemma BBs_sem_Asgn_split:
  forall (BBnow: BasicBlock) (BBs: list BasicBlock) (x: var_name) (e: expr) (bs1 bs2: BB_state),
    let BB_delta := {|
      block_num := BBnow.(block_num);
      commands := {| X := x; E := e |} :: nil;
      jump_info := BBnow.(jump_info)
    |} in
    Bnrm (BB_list_sem (BB_delta :: BBs)) bs1 bs2 -> bs1.(BB_num) = BBnow.(block_num) -> (exists (x: BB_state), Bnrm (BB_sem BB_delta) bs1 x /\ Bnrm (BB_list_sem BBs) x bs2).
Proof.
  Admitted.



Lemma P_cons:
  forall (c: cmd) (cmds: list cmd) (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results),
  Qb c -> P cmds cmd_BB_gen -> P (c :: cmds) (cmd_BB_gen).
Proof.
  intros.
  rename H into Qb_prop. rename H0 into P_prop.
  unfold Qb in Qb_prop. unfold P in P_prop. simpl in *.
  destruct c.
  - unfold P. intros.
    exists BBs. exists {|
      block_num := BBnow.(block_num);
      commands := BBnow.(cmd) ++ {| X:= x; E:= e|} :: nil;
      jump_info := BBnow.(jump_info);
    |}. exists ({| X := x; E := e|} :: nil).
    exists (list_cmd_BB_gen cmd_BB_gen (CAsgn x e :: cmds) BBs BBnow BBnum).(next_block_num).
    exists BBnow.(block_num). intros. repeat split.
    + simpl. admit.
    + admit.
    + intros. rename H2 into key1. simpl. sets_unfold.
      specialize (Qb_prop BBs BBnow BBnum).
      remember ({|
      block_num := BBnow.(block_num);
      commands := BBnow.(cmd) ++ {| X := x; E := e |} :: nil;
      jump_info := BBnow.(jump_info) |}) as BBnow'.

      destruct H as [H_aux1 [H_aux2 H_aux3]].
      destruct Qb_prop as [Qb_aux1 | Qb_aux2].
      repeat split. apply H_aux1. apply H_aux2.
      apply H0. apply H1. apply H_aux3.
      -- destruct Qb_aux1 as [? [? [Qb_1 [Qb_2 Qb_3]]]].
         destruct Qb_3. clear err_cequiv inf_cequiv.
         sets_unfold in nrm_cequiv. 
         cbn[Bnrm] in key1. unfold cmd_sem in nrm_cequiv. 
         unfold asgn_sem in nrm_cequiv. cbn[nrm] in nrm_cequiv. 
         (* Fetch the states from key1. This should derive Asgn *)
         destruct key1 as [? [? [B1 [B2 [B3 [B4 B5]]]]]].
         pose proof BBs_sem_Asgn_split BBnow' BBs x e x2 x3 B1 B4 as H_Asgn_split.
         destruct H_Asgn_split as [? [H_step1 H_step2]].

         unfold BB_sem in H_step1.
         cbn[Bnrm] in H_step1. sets_unfold in H_step1.
         destruct H_step1 as [? [H_step1_aux1 H_step1_aux2]].
         unfold BB_cmds_sem in H_step1_aux1. cbn[Bnrm] in H_step1_aux1.
         unfold BAsgn_list_sem in H_step1_aux1. simpl in H_step1_aux1. sets_unfold in H_step1_aux1.
         destruct H_step1_aux1 as [? ?].
        
         specialize (nrm_cequiv a x5.(st)). destruct nrm_cequiv as [H_forward H_backward]. clear H_backward.
         cbn[Bnrm] in H_forward.

         
         assert (exists i : int64, (eval_expr e).(nrm) a i /\ st x5 x = Vint i /\ (forall Y : var_name, x <> Y -> st x5 Y = a Y)) as H_step1_final. {
            apply H_forward.
            exists x2. exists x5. split. exists x6. 
            assert (x1 = {| X := x; E := e|}). admit. (*TODO *)
            rewrite H2. simpl. apply H.
            unfold BB_generation.cmd_BB_gen in Qb_1. simpl in Qb_1. subst BBnow'. simpl in B4.
            repeat split. apply B2. rewrite <- Qb_1. simpl. apply B4. 
            rewrite <- Qb_1. simpl. my_destruct H. rewrite H2 in H3. rewrite <- H3. apply B4. 
         }
         
         exists x5.(st). split. apply H_step1_final.

         (* x2: 起始状态 *)
         (* x5: 走完了Asgn *)
         (* x4: 走完Jump *)
         (* x3: 走完BBs *)

         (* Here we should use step2 *)
         (* 本质上是希望说明: 只包含Jump的BBnow'+BBs == cmds *)
         remember {|
            block_num := BBnow'.(block_num);
            commands := nil;
            jump_info := BBnow'.(jump_info)
         |} as BBnow_step2.
         specialize (P_prop BBs BBnow_step2 BBnum).
         destruct P_prop as [BBs'_ [BBnow'_ [BBcmds_ [BBnum'_ [BBendnum_ ?]]]]]. destruct H2.
         subst BBnow_step2. simpl. repeat split; subst BBnow'; simpl. apply H_aux1. apply H_aux2. apply H_aux3.
         subst BBnow_step2. simpl. subst BBnow'; simpl. apply H0.
         subst BBnow_step2. simpl. subst BBnow'; simpl. apply H1.
         
         destruct H3 as [? [? [? [? [key2 ?]]]]].

         destruct key2. clear err_cequiv inf_cequiv.
         sets_unfold in nrm_cequiv.
         specialize (nrm_cequiv x5.(st) a0). destruct nrm_cequiv as [H_forward_ H_backward_]. clear H_backward_. apply H_forward_.

         exists x5. exists {| st := a0; BB_num := jump_dest_1 BBnow_step2.(jump_info) |}.
         repeat split; try tauto. cbn[Bnrm]. 
         (* 第一个branch用H_step2和H_step1_aux2 *)
         ++ remember ({|
          block_num := BBnow'.(block_num);
          commands := {| X := x; E := e |} :: nil;
          jump_info := BBnow'.(jump_info) |}) as BBnow_1to2.
            assert (Bnrm (BDenote_concate (BB_jmp_sem
            BBnow_1to2) (BB_list_sem BBs)) x5 x3) as H_sem_concat. {
              unfold BDenote_concate. cbn[Bnrm]. sets_unfold.
              exists x4. split. apply H_step1_aux2. apply H_step2.
            }
            pose proof BDenote_concat_equiv_BB_list_sem BBnow_1to2 BBs x5 x3 as H_BBs_equiv_aux.

            (* Separate property. *)
            assert (separate_property BBnow_1to2 BBs) as H_sep_1. admit.

            assert (BB_restrict BBnow_1to2 BBs (BB_num x5) (BB_num x3)) as H_sep_2. admit.

            assert (BBnow_1to2.(block_num) <> jump_dest_1 BBnow_1to2.(jump_info) /\
            Some BBnow_1to2.(block_num) <> jump_dest_2 BBnow_1to2.(jump_info)) as H_sep_3. admit.

            pose proof H_BBs_equiv_aux H_sep_1 H_sep_2 H_sep_3 as H_BBs_equiv. clear H_BBs_equiv_aux.

            destruct H_BBs_equiv as [H_BBs_equiv tmp]. clear tmp.

            pose proof H_BBs_equiv H_sem_concat as H_final.
            
            (* 到这里就有点奇怪了，我不太清楚这个地方该怎么处理BB_cmds，这里的的BB_cmds应该是来源于BBs而不是一开始的Asgn；前半段我证明了CAsgn <-> 一个手动添加的只有一个指令的Block；后半段我理论上希望证明的是cmds <-> BBs；而现在好像出现了一点不一致 *)

            assert (BBnow_1to2 = BBnow'_). {
              admit. (* 理论上BBnow'_中不会再加cmd了? *)
            }
            
            rewrite H8 in H_final.
            assert ({| BB_num := jump_dest_1 BBnow_step2.(jump_info); st := a0 |} = x3). {
              admit. (* 这一步是显然的 *)
            }


         ++ rewrite H5. subst BBnow_step2. simpl. subst BBnow'. 
            simpl. my_destruct H. rewrite H8 in H9. rewrite <- H9. apply B4. 
         

      -- admit. (* Qb_aux2 is for if and while, shouldn't be here *)
    + intros.
      repeat split; try tauto. cbn[Bnrm]. 
      remember ({|
        block_num := BBnow.(block_num);
        commands := BBnow.(cmd) ++ {| X := x; E := e |} :: nil;
        jump_info := BBnow.(jump_info) |}) as BBnow'.
      exists {| st := a; BB_num := BBnow'.(block_num) |}.
      exists {| st := a0; BB_num := jump_dest_1 BBnow.(jump_info) |}.
      repeat split; try tauto. admit.
    + admit. (* err case*)
    + admit. (* err case *)
    + admit. (* inf case *)
    + admit. (* inf case *)

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