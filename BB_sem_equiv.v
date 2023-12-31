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
            (*Use H_step1 easy *)
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

      (* ! Check. *)
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
      -- intros. destruct H2 as [bs1 [bs2 [H_sem_full [C1 [C2 [C3 C4]]]]]].
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
         destruct key1. clear err_cequiv inf_cequiv.
         rename nrm_cequiv into H_step1. sets_unfold in H_step1.
         destruct key2. clear err_cequiv inf_cequiv.
         rename nrm_cequiv into H_step2. sets_unfold in H_step2.
         remember ({|
          block_num := BBnow'_.(block_num);
          commands := nil;
          jump_info := BBnow'_.(jump_info) |}) as BBnow_start.
         assert (exists (x: BB_state), Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_)) bs1 x /\ Bnrm (BB_list_sem (BBnow'_p :: BBs'_p)) x bs2) as H_sep. admit. (*TODO hard and important*)

         destruct H_sep as [bb_mid [H_step1_main H_step2_main]].
         cbn[cmd_list_sem]. cbn[nrm]. sets_unfold. exists bb_mid.(st).
         (* 这个时候我们就分两步，分别使用H_step1和H_step2来走 *)
         specialize (H_step1 a bb_mid.(st)).

         assert (now_mid_block_num: BBnow_mid.(block_num) = (S (S BBnum))). {
          rewrite HeqBBnow_mid. simpl. reflexivity.
         }

         assert(key_num_eq: BB_num bb_mid = S (S BBnum)). {
         (*利用H_step2_main + 分离性质*)
         (*TODO 这个可能会超级麻烦
         1. 由H_step1_main得到BB_mid的num一定在(BBnow_start :: nil ++ BBswo_)的jmpdest之中，而我们有其范围
         2. 由H_step2_main得到BB_mid的num一定在((BBnow'_p :: BBs'_p)) 的num之中，而我们也有其范围。
          两个范围唯一的交点就是S (S BBnum)
         *)
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
          symmetry in A4. rewrite <- Heqc0 in A4. specialize (Q_prop m1 A4 m2 H0).
          
          specialize (P_prop BBnum'_ BBnum'_p (BBs ++ BBnow'_ :: BBswo_) BBnow_mid (BBnow'_p :: BBs'_p)).
          assert(n1: jump_kind BBnow_mid.(jump_info) = UJump /\ jump_dest_2 BBnow_mid.(jump_info) = None). tauto.
          assert(n2: to_result (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_) =
          (BBs ++ BBnow'_ :: BBswo_) ++ BBnow'_p :: BBs'_p). {
            admit. (* TODO Same, just use list version of Q_add_BBs_in_generation_reserves_BB_sound *)
          }
          specialize (P_prop n1 B2 n2).
          destruct Q_prop as [_ [_ Q_prop]]. destruct P_prop as [P_prop [_ _]].
          pose proof BBs_bs2_in_BB_jmp_set (BBnow_start :: nil ++ BBswo_) bs1 bb_mid H_step1_main as key1. 
          pose proof BBs_bs1_in_BB_num_set (BBnow'_p :: BBs'_p) bb_mid bs2 H_step2_main as key2.
          sets_unfold in Q_prop. specialize Q_prop with (BB_num bb_mid).
          unfold all_ge in P_prop. unfold tl in P_prop. 
          destruct key1 as [case_a | case_b].
          + destruct key2 as [case_a' | case_b'].
            ++ assert (subseteq: BBjmp_dest_set (BBnow'_ :: BBs'_) (BB_num bb_mid)). {
            (*TODO 显然成立，因为case_a*)
              admit.
            }
            specialize (Q_prop subseteq). 
            destruct Q_prop as [case1 | case2].
            * unfold section in case1. simpl in case1. destruct case1 as [_ cond].
              pose proof destruct_in_BBnum_set BBnow'_p BBs'_p (BB_num bb_mid) case_a' as key.
              destruct key as [case1 | case2].
              ** rewrite B4 in case1. rewrite case1. tauto.
              ** specialize (P_prop (BB_num bb_mid) case2). lia.
            * unfold unit_set in case2. (* ! 需要证明BBnow的jmpinfo最后只会在BBn中, 不妨假设输入的BBnow的跳转目的地是一个最小的BBnum TODO HARD*) admit.
            ++ assert (subseteq: BBjmp_dest_set (BBnow'_ :: BBs'_) (BB_num bb_mid)). {
            (*TODO 显然成立，因为case_a*)
              admit.
            }


         }
         
         destruct H_step1 as [H_step1_forward T4]. clear T4. split. apply H_step1_forward.
         exists bs1. exists bb_mid.
         assert (sep_prop: separate_property BBnow'_ BBs). {
          unfold separate_property. 
          (*A2*) 
          admit.
         }
         assert (Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_)) bs1 bb_mid -> Bnrm (BDenote_concate (BB_jmp_sem BBnow'_) (BB_list_sem BBswo_)) bs1 bb_mid) as M1. {
            (*TODO
              使用引理BDenote_concat_equiv_BB_list_sem
              转换关系应该是对的，但是需要把前提都找出来
              *)
            pose proof BDenote_concat_equiv_BB_list_sem BBnow'_ BBs bs1 bb_mid sep_prop.
            pose proof BB_restrict_sound.  (*这里要考虑c1和c2到底能不能是不是空*)
            admit.
         }
         repeat split. apply M1. apply H_step1_main.
         apply C1. rewrite C3. rewrite BBnow'_prop. simpl. reflexivity.

         apply key_num_eq.

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
         assert ((exists (x: BB_state), Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_)) bs1 x /\ Bnrm (BB_list_sem (BBnow'_p :: BBs'_p)) x bs2) -> Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_ ++ BBnow'_p :: BBs'_p)) bs1 bs2) as H_sep. admit. (*TODO 可能比上一种情况简单一点*)
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
         assert (x0 = bs1) as T4. admit. (*TODO easy*)
         assert (x1 = bs3) as T5. admit. (*TODO easy*)
         rewrite T4 in C1. rewrite T5 in C1.
         assert (Bnrm (BDenote_concate (BB_jmp_sem BBnow'_) (BB_list_sem BBswo_)) bs1 bs3 -> Bnrm (BB_list_sem (BBnow_start :: nil ++ BBswo_)) bs1 bs3) as M1. {
            admit. (*TODO 同上，应该是对的*)
         }
         apply M1. apply C1.

         (* 接下来考虑第二步的情况 *)
         specialize (H_step2 x a0).
         destruct H_step2 as [T4 H_step2_inv]. clear T4.
         pose proof H_step2_inv H_step2_main as H_step2_inv.
         destruct H_step2_inv as [? [? [C1 [C2 [C3 [C4 C5]]]]]].
         assert (x0 = bs3) as T4. admit. (*TODO easy*)
         assert (x1 = bs2) as T5. admit. (*TODO easy*)
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
    - admit.
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