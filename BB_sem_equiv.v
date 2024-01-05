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


(* Changed how we split everything *)
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
     bs1.(BB_num) = BBnow.(block_num) -> ((Bnrm (BB_list_sem (BB1 :: BBs)) bs1 bs2) <-> (exists (x: BB_state), Bnrm (BAsgn_list_sem (BBcmd :: nil)) bs1 x /\ Bnrm (BB_list_sem (BB2 :: BBs)) x bs2)).
Proof.
  intros. split.
  + admit.
  + intros. my_destruct H0.
    unfold BB_list_sem. cbn[Bnrm]. sets_unfold.
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
    (* 结论中的BBs'是表示c :: cmds在gen之后新的BBs
       而BBnow'则是c :: cmds在gen之后的BBn
       那么我们本质上是用Qb和P来拼接着生成c :: cmds
       最后再证明生成的结果符合某些性质
    *)

    specialize (Qb_prop BBs BBnow BBnum).
    destruct H as [T1 [T2 T3]].
    assert (jump_kind BBnow.(jump_info) = UJump /\
    jump_dest_2 BBnow.(jump_info) = None) as T4. split. apply T1. apply T2.
    pose proof Qb_prop T4 H0 H1 T3 as Qb_prop.
    clear T1 T2 T3 T4.
    (* Qb 会有两种情况来讨论 *)
    destruct Qb_prop as [Qb_asgn | Qb_if_while ].
    + destruct Qb_asgn as [? [? [B1 [B2 H_asgn_equiv]]]]. 
      unfold BB_generation.cmd_BB_gen in B1. simpl in B1.
      (* 从B1，B2中显然可以得到x0就是我们想要的完成了CAsgn移入的Block
         加入一条CAsgns是不会改变BBs的，所以原来的BBs会作为P cmds的输入
         同样不会改变的还有BBnum
      *)
      specialize (P_prop BBs x0 BBnum).
      assert (jump_kind x0.(jump_info) = UJump /\
      jump_dest_2 x0.(jump_info) = None /\
      jump_condition x0.(jump_info) = None) as T1. admit.

      assert ((x0.(block_num) < BBnum)%nat) as T2. admit.

      assert (x0.(block_num) <> jump_dest_1 x0.(jump_info)) as T3. admit.

      pose proof P_prop T1 T2 T3 as P_prop.
      clear T1 T2 T3.

      destruct P_prop as [BBs_ [BBnow'_ [BBcmds_ [BBnum'_ [BBendnum_ ?]]]]].

      exists BBs_. exists BBnow'_. exists ({|X := x; E := e|}::nil ++ BBcmds_). exists BBnum'_. exists BBendnum_. 
      
      (* 整理一下已知条件 *)
      destruct H as [C1 [C2 [C3 [C5 [C6 [H_cmd_equiv C7]]]]]].

      repeat split. 
      -- rewrite <- B1 in C1. simpl in C1. admit. (*TODO fix here, why C1 is different? *)
      -- admit. (*TODO use C2 *)
      -- rewrite <- B1 in C3. simpl in C3. rewrite <- app_assoc in C3. apply C3.
      -- rewrite C5. rewrite <- B1. simpl. tauto.
      -- admit. (*TODO perhaps not very difficult *)
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
           assert ({| BB_num := jump_dest_1 x0.(jump_info); st := a0 |} = x3). admit. (*TODO easy*)
           rewrite H. apply H_step2.
           assert (x2.(BB_num) = x4.(BB_num)) as T1. admit. (*TODO H_step1 easy *)
           rewrite <- T1. rewrite <- D3. tauto.

      -- intros. rename H into H_cmds_sem_main. (* cmd_sem -> BB_sem *)
         unfold cmd_list_sem in H_cmds_sem_main. simpl in H_cmds_sem_main. sets_unfold in H_cmds_sem_main.
         destruct H_cmds_sem_main as [? [H_step1 H_step2]].
         exists {| st := a; BB_num := BBnow'_.(block_num) |}.
         exists {| st := a0; BB_num := jump_dest_1 BBnow.(jump_info) |}.
         repeat split; try tauto. cbn[Bnrm].
         remember ({| BB_num := BBnow'_.(block_num); st := a |}) as bs1.
         remember ({| BB_num := jump_dest_1 BBnow.(jump_info); st := a0 |}) as bs2.
         pose proof BBs_sem_Asgn_split BBnow'_ BBs_ BBcmds_ x e bs1 bs2 as T1. destruct T1 as [T2 H_cmds_equiv_inv]. subst bs1. simpl. tauto. clear T2.
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
            assert (x1 = {| X := x; E := e|}) as T1. admit. (*TODO easy*)
            rewrite T1 in H_asgn_main3. simpl in H_asgn_main3.
            repeat split. exists x6.
            rewrite A1 in H_asgn_main3. rewrite H_asgn_main1 in H_asgn_main3. subst bs1. simpl. apply H_asgn_main3.
            rewrite A4. subst bs1. simpl. rewrite C5. tauto.
            rewrite H_asgn_main1. tauto.
        ++ specialize (cmds_nrm_equiv x2 a0). destruct cmds_nrm_equiv as [T1 T2]. clear T1. pose proof T2 H_step2 as H_cmds_equiv_inv.
           clear T2.
           destruct H_cmds_equiv_inv as [? [? [H_cmds_main [D1 [D2 [D3 D4]]]]]]. cbn[Bnrm] in H_cmds_main.
           unfold BB_list_sem. cbn[Bnrm]. sets_unfold.
           assert (x6 = x5) as T1. admit. (*TODO easy *)
           assert (bs2 = x7) as T2. admit. (*TODO easy*)
           rewrite <- T1. rewrite T2. apply H_cmds_main.
      -- admit. (* err case *)
      -- admit. (* err case *)
      -- admit. (* inf case *)
      -- admit. (* inf case *) 
      -- admit. (*TODO simple *)
    + admit.
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