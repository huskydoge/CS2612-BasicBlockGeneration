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


Lemma cut_eq_part_l:
  forall (A: Type) (a b: A) (l1 l2: list A),
  l1 ++ a :: l2 = l1 ++ b :: l2 -> a = b.
Proof.
  intros.
  induction l1.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. inversion H. apply IHl1. apply H1.
Qed.

Lemma cut_eq_part_r:
  forall (A: Type) (a b: A) (l1 l2: list A),
  l1 ++ a :: l2 = l1 ++ b :: l2 -> a = b.
Proof.
  intros.
  induction l1.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. inversion H. apply IHl1. apply H1.
Qed.

Lemma cut_eq_part_list_l:
  forall (A: Type) (l1 l2 l3: list A),
  l1 ++ l2 = l1 ++ l3 -> l2 = l3.
Proof.
  intros.
  induction l1.
  - simpl in H. inversion H. reflexivity.
  - simpl in H. inversion H. apply IHl1. apply H1.
Qed.


Lemma cut_eq_part_list_r:
  forall (A: Type) (l1 l2 l3: list A),
  l2 ++ l1 = l3 ++ l1 -> l2 = l3.
Proof.
  intros.
  induction l1.
  - simpl in H. rewrite app_nil_r in H. rewrite app_nil_r in H. apply H.
  - simpl in H. apply IHl1.
Admitted.


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

(*BBnumset BBs >= num*)
Definition BB_all_ge (BBs: list BasicBlock)(num: nat): Prop :=
    forall BB, In BB BBs -> Nat.le num BB.(block_num) \/ BBs = nil.
(*BBnumset BBs < num*)
Definition BB_all_lt (BBs: list BasicBlock)(num: nat): Prop :=
    forall BB, In BB BBs -> Nat.lt BB.(block_num) num \/ BBs = nil.

Definition all_ge (natset: nat -> Prop)(num: nat): Prop :=
    forall n, natset n -> Nat.le num n \/ natset == ∅.
  
Definition all_lt (natset: nat -> Prop)(num: nat): Prop :=
    forall n, natset n -> Nat.lt n num \/ natset == ∅.

(*定义自然数区间*)
Definition section (startnum endnum: nat) : nat -> Prop :=
  fun BBnum => Nat.le startnum BBnum /\ Nat.le BBnum endnum.

Definition unit_set (BBnum: nat): BB_num_set :=
  fun BBnum' => BBnum' = BBnum.

(* Lemma In_eq_set:
  forall (s1 s2: BBnum_set) (n: nat), *)

Definition P_BBgen_range (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results)(cmds: list cmd): Prop :=
    forall startnum endnum BBs BBnow BBdelta,
    let res := (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow startnum) in
    let basicblocks := to_result res in
    (BBnow.(jump_info).(jump_kind) = UJump /\ BBnow.(jump_info).(jump_dest_2) = None) ->
    endnum = res.(next_block_num)
    -> 
      basicblocks = BBs ++ BBdelta ->
    (
      all_ge (BBnum_set(tl BBdelta)) startnum /\
      all_lt (BBnum_set(tl BBdelta)) endnum /\ 
      BBjmp_dest_set BBdelta ⊆  (section startnum endnum) ∪ unit_set (BBnow.(jump_info).(jump_dest_1))
    ).

Definition Q_BBgen_range (c: cmd): Prop :=
    forall startnum endnum BBs BBnow BBdelta,
    let res := (cmd_BB_gen c BBs BBnow startnum) in
    let basicblocks := to_result res in
    (BBnow.(jump_info).(jump_kind) = UJump /\ BBnow.(jump_info).(jump_dest_2) = None) ->
    endnum = res.(next_block_num) ->

     basicblocks = BBs  ++ BBdelta ->
     (
      all_ge (BBnum_set(tl BBdelta)) startnum /\
      all_lt (BBnum_set(tl BBdelta)) endnum /\ 
      BBjmp_dest_set BBdelta ⊆  (section startnum endnum) ∪ unit_set (BBnow.(jump_info).(jump_dest_1))
    ).

(*如果一个元素在一个列表里，它要么是这个列表的第一个，要么就在后续部分里*)
Lemma In_head_or_body:
  forall (A: Type) (a: A)(empty: A)(l: list A),
  In a l -> a = hd empty l \/ In a (tl l).
Proof.
  intros.
  induction l.
  - simpl in H. tauto.
  - simpl in H. destruct H.
    + left. rewrite H. reflexivity.
    + right. apply H.
Qed.

Definition empty_block := {|
  block_num := 0;
  commands := nil;
  jump_info := {|
      jump_kind := UJump;
      jump_dest_1 := 0;
      jump_dest_2 := None;
      jump_condition := None
    |}
|}.


Lemma option_eq_some:
  forall (A: Type) (a b: A),
  a = b <->  Some a = Some b.
Proof.
  intros. split; intros.
  - rewrite H. reflexivity.
  - inversion H. reflexivity.
Qed.


Lemma add_BBs_in_generation_reserves_BB:
  forall (cmds : list cmd) (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),

  to_result (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum) 
  = BBs ++ to_result (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).
Proof.
  intros.
   
Admitted.


Lemma add_BBs_in_generation_retains_next_block_num:
  forall (cmds : list cmd) (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
    (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(next_block_num) =
    (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(next_block_num).
Proof.
  intros.
Admitted.


(* Used In aux proof.v *)
Lemma bbnow_num_lt_next_num:
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: list cmd),
    (lt BBnow.(block_num) BBnum) -> lt BBnow.(block_num) (list_cmd_BB_gen cmd_BB_gen c BBs BBnow BBnum).(next_block_num).
Proof.
  intros. induction c.
  - simpl. lia.
  - cbn [list_cmd_BB_gen].
    unfold list_cmd_BB_gen.
    destruct a.
    + simpl. admit.
Admitted. (*TODO *)

(*x在 l1 ++ l2中，那么必然在至少其中之一*)
Lemma In_a_or_b:
  forall (A: Type) (x: A) (l1 l2: list A),
  In x (l1 ++ l2) -> In x l1 \/ In x l2.
Proof.
  intros.
  induction l1.
  - simpl in H. right. apply H.
  - simpl in H. destruct H.
    + left. rewrite H. simpl. left. reflexivity.
    + pose proof IHl1 H. destruct H0.
      * left. simpl. right. apply H0.
      * right. apply H0.
Qed.

Lemma In_a_or_b_or_c:
  forall (A: Type) (x: A) (l1 l2 l3: list A),
  In x (l1 ++ l2 ++ l3) -> In x l1 \/ In x l2 \/ In x l3.
Proof.
  intros.
  induction l1.
  - simpl in H. right. apply In_a_or_b. apply H.
  - simpl in H. destruct H.
    + left. rewrite H. simpl. left. reflexivity.
    + pose proof IHl1 H. destruct H0.
      * left. simpl. right. apply H0.
      * right. apply H0.
Qed.

Lemma In_sublist_then_in_list_head:
  forall (A: Type) (x: A) (l1 l2: list A),
  In x l1 -> In x (l1 ++ l2).
Proof.
  intros.
  induction l1.
  - simpl in H. tauto.
  - simpl in H. destruct H.
    + left. apply H.
    + right. apply IHl1. apply H.
Qed.

Lemma In_sublist_then_in_list_middle:
  forall (A: Type) (x: A) (l1 l2 l3: list A),
  In x l1 -> In x (l2 ++ l1 ++ l3).
Proof.
  intros.
  induction l2.
  - simpl. apply In_sublist_then_in_list_head. apply H.
  - simpl. right. apply IHl2.
Qed.

Lemma In_sublist_then_in_list_last:
  forall (A: Type) (x: A) (l1 l2: list A),
  In x l1 -> In x (l2 ++ l1).
Proof.
  intros.
  induction l2.
  - simpl. tauto.
  - simpl. right. apply IHl2.
Qed.

(*一个元素x在一个列表里，那么在列表头部加一个元素h，x仍然在列表里*)
Lemma In_add_one_list:
  forall (A: Type) (x h: A) (l: list A),
  In x l -> In x (h::l).
Proof.
  intros.
  simpl. right. apply H.
Qed.

(*TODO IMPORTANT!!*)
Lemma BBgen_head_prop:
  forall (cmds : list cmd)(BBnow : BasicBlock) (BBnum : nat),
  let res := (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum) in
  (hd empty_block (res.(BasicBlocks) ++ res.(BBn)::nil)).(block_num) = BBnow.(block_num).
Proof.
  intros.
  unfold res.
  unfold list_cmd_BB_gen.
  induction cmds.
  - simpl. reflexivity.
  - admit.
Admitted.


Lemma Q_if_BBgen_range:
forall (e: expr) (c1 c2: list cmd),
    P_BBgen_range cmd_BB_gen c1  ->
    P_BBgen_range cmd_BB_gen c2  ->
    Q_BBgen_range (CIf e c1 c2).
Proof.
  intros.
  rename H into c1_prop.
  rename H0 into c2_prop.
  unfold P_BBgen_range in c1_prop.
  unfold P_BBgen_range in c2_prop.
  unfold Q_BBgen_range.
  intros.
  rename H into BBnow_jump_kind.
  rename H0 into endnum_eq.
  rename H1 into BBs_eq.
  unfold to_result in BBs_eq.
  set(then_start_num := S (S (S startnum))). (* S BBnextnum *)
  set(BB_then_now := {|
      block_num := startnum;
      commands := nil;
      jump_info := {|
        jump_kind := UJump;
        jump_condition := None; 
        jump_dest_1 := (S (S startnum)); (* BBnextnum*)
        jump_dest_2 := None |} ;
      |}).

  set(then_res := (list_cmd_BB_gen cmd_BB_gen c1 nil BB_then_now then_start_num)).
  set(then_delta := (then_res).(BasicBlocks) ++ (then_res).(BBn)::nil).
  set(then_end_num := (then_res).(next_block_num)).
  
  set(BB_else_now := {|
  block_num := (S startnum);
  commands := nil;
  jump_info := {|
    jump_kind := UJump;
    jump_condition := None; 
    jump_dest_1 := (S (S startnum)); (* BBnextnum*)
    jump_dest_2 := None |} ;
  |}).
  set(else_res := (list_cmd_BB_gen cmd_BB_gen c2 nil BB_else_now then_end_num)).
  set(else_delta := (else_res).(BasicBlocks) ++ (else_res).(BBn)::nil).
  set(else_end_num := (else_res).(next_block_num)).
  set(BB_next := {|
    block_num := (S (S startnum));
    commands := nil;
    jump_info := BBnow.(jump_info);
    |}).
  set(BBnow' := 
      {|
      block_num := BBnow.(block_num);
      commands := BBnow.(cmd);
      jump_info :=
        {|
          jump_kind := CJump;
          jump_dest_1 := startnum;
          jump_dest_2 := Some (S startnum);
          jump_condition := Some e
        |}
      |}
  ).
  
  specialize (c1_prop then_start_num then_end_num BBs BB_then_now then_delta).
  assert (c1_aux1 : (BB_then_now.(jump_info).(jump_kind) = UJump /\ BB_then_now.(jump_info).(jump_dest_2) = None) ). tauto.
  assert (c1_aux2 : then_end_num = (list_cmd_BB_gen cmd_BB_gen c1 BBs BB_then_now then_start_num).(next_block_num)). admit.
  assert (c1_aux3 : (to_result (list_cmd_BB_gen cmd_BB_gen c1 BBs BB_then_now then_start_num) = BBs ++ then_delta)). admit.
  specialize (c1_prop c1_aux1 c1_aux2 c1_aux3).
  clear c1_aux1 c1_aux2 c1_aux3.
  
  specialize (c2_prop then_end_num endnum BBs BB_else_now else_delta).
  assert (c2_aux1 : (BB_else_now.(jump_info).(jump_kind) = UJump /\ BB_else_now.(jump_info).(jump_dest_2) = None)). admit.
  assert (c2_aux2 : endnum = (list_cmd_BB_gen cmd_BB_gen c2 BBs BB_else_now then_end_num).(next_block_num)). admit.
  assert (c2_aux3 : (to_result (list_cmd_BB_gen cmd_BB_gen c2 BBs BB_else_now then_end_num) = BBs ++ else_delta)). admit.
  specialize (c2_prop c2_aux1 c2_aux2 c2_aux3).
  clear c2_aux1 c2_aux2 c2_aux3.

  destruct c1_prop as [c1_prop1 [c1_prop2 c1_prop3]].
  destruct c2_prop as [c2_prop1 [c2_prop2 c2_prop3]].

  assert (eq_tl_delta_prop: tl BBdelta = then_delta ++ else_delta ++ BB_next :: nil).
  {
    cbn [cmd_BB_gen] in BBs_eq. cbn [BasicBlocks] in BBs_eq. cbn [BBn] in BBs_eq. 
    rewrite <- app_assoc in BBs_eq. apply app_inv_head in BBs_eq.
    rewrite <- BBs_eq. simpl. subst BB_next. rewrite app_assoc_reverse.
    assert (then_eq: to_result
    (list_cmd_BB_gen cmd_BB_gen c1 nil
       {|
         block_num := startnum;
         commands := nil;
         jump_info :=
           {|
             jump_kind := UJump;
             jump_dest_1 := S (S startnum);
             jump_dest_2 := None;
             jump_condition := None
           |}
       |} (S (S (S startnum)))) = then_delta).
    {
      reflexivity.
    }
    rewrite then_eq. 
    assert (else_eq: to_result
    (list_cmd_BB_gen cmd_BB_gen c2 nil
       {|
         block_num := S startnum;
         commands := nil;
         jump_info :=
           {|
             jump_kind := UJump;
             jump_dest_1 := S (S startnum);
             jump_dest_2 := None;
             jump_condition := None
           |}
       |}
       (list_cmd_BB_gen cmd_BB_gen c1 nil
          {|
            block_num := startnum;
            commands := nil;
            jump_info :=
              {|
                jump_kind := UJump;
                jump_dest_1 := S (S startnum);
                jump_dest_2 := None;
                jump_condition := None
              |}
          |} (S (S (S startnum)))).(next_block_num)) = else_delta).
    {
      assert (then_res_p: (list_cmd_BB_gen cmd_BB_gen c1 nil
      {|
        block_num := startnum;
        commands := nil;
        jump_info :=
          {|
            jump_kind := UJump;
            jump_dest_1 := S (S startnum);
            jump_dest_2 := None;
            jump_condition := None
          |}
      |} (S (S (S startnum)))) = then_res). reflexivity. rewrite then_res_p.
      reflexivity.
      }
    rewrite else_eq. reflexivity.
  }

  assert (eq_delta_prop: BBdelta = BBnow' :: then_delta ++ else_delta ++ BB_next :: nil).
  {
  cbn [cmd_BB_gen] in BBs_eq. cbn [BasicBlocks] in BBs_eq. cbn [BBn] in BBs_eq. 
  rewrite <- app_assoc in BBs_eq. apply app_inv_head in BBs_eq.
  rewrite <- BBs_eq. simpl. subst BB_next. rewrite app_assoc_reverse.
  assert (then_eq: to_result
  (list_cmd_BB_gen cmd_BB_gen c1 nil
     {|
       block_num := startnum;
       commands := nil;
       jump_info :=
         {|
           jump_kind := UJump;
           jump_dest_1 := S (S startnum);
           jump_dest_2 := None;
           jump_condition := None
         |}
     |} (S (S (S startnum)))) = then_delta).
  {
    reflexivity.
  }
  rewrite then_eq. 
  assert (else_eq: to_result
  (list_cmd_BB_gen cmd_BB_gen c2 nil
     {|
       block_num := S startnum;
       commands := nil;
       jump_info :=
         {|
           jump_kind := UJump;
           jump_dest_1 := S (S startnum);
           jump_dest_2 := None;
           jump_condition := None
         |}
     |}
     (list_cmd_BB_gen cmd_BB_gen c1 nil
        {|
          block_num := startnum;
          commands := nil;
          jump_info :=
            {|
              jump_kind := UJump;
              jump_dest_1 := S (S startnum);
              jump_dest_2 := None;
              jump_condition := None
            |}
        |} (S (S (S startnum)))).(next_block_num)) = else_delta).
  {
    assert (then_res_p: (list_cmd_BB_gen cmd_BB_gen c1 nil
    {|
      block_num := startnum;
      commands := nil;
      jump_info :=
        {|
          jump_kind := UJump;
          jump_dest_1 := S (S startnum);
          jump_dest_2 := None;
          jump_condition := None
        |}
    |} (S (S (S startnum)))) = then_res). reflexivity. rewrite then_res_p.
    reflexivity.
    }
  rewrite else_eq. reflexivity.
  }

  (*拆分BBdelta, 去掉头部的number后， BBdelta里有BBnow的num，还有剩下所有新增的num，其中包括BBthendelta，BBelsedelta，以及BBnext*)
  assert (separate_delta_num: 
  BBnum_set (tl BBdelta) ==  BBnum_set then_delta ∪ BBnum_set else_delta ∪ unit_set(S (S startnum))
  ). {
    rewrite eq_tl_delta_prop.
    repeat split; sets_unfold; intros.
    - destruct H as [x_ [cond1 cond2]].
      pose proof (In_a_or_b BasicBlock x_ (then_delta ++ else_delta) (BB_next :: nil)).
      rewrite app_assoc_reverse in H. pose proof H cond1. destruct H0 as [c1_ | c2_].
      pose proof (In_a_or_b BasicBlock x_ then_delta else_delta c1_).
      destruct H0 as [c1__ | c2__].
      * left. left. unfold BBnum_set. exists x_. split. tauto. tauto.
      * left. right. unfold BBnum_set. exists x_. split. tauto. tauto.
      * right. unfold unit_set. subst BB_next. simpl in c2_. 
        destruct c2_ as [c2_ | c2_].
        ** rewrite <- c2_ in cond2. simpl in cond2. lia.
        ** tauto. 
    - destruct H as [[case1 | case2] | case3].
      * unfold BBnum_set in case1. destruct case1 as [x_ [cond1 cond2]].
        unfold BBnum_set. exists x_. split. 
        ** pose proof In_sublist_then_in_list_head BasicBlock x_ then_delta (else_delta ++ BB_next :: nil) cond1. tauto.
        ** tauto.
      * unfold BBnum_set in case2. destruct case2 as [x_ [cond1 cond2]].
        unfold BBnum_set. exists x_. split. 
        ** pose proof In_sublist_then_in_list_middle BasicBlock x_ else_delta then_delta (BB_next :: nil) cond1. tauto.
        ** tauto.
      * unfold BBnum_set. exists BB_next. split.
        ** assert (In BB_next (BB_next::nil)). simpl. tauto.
            pose proof In_sublist_then_in_list_last BasicBlock BB_next (BB_next :: nil) (then_delta ++ else_delta) H. rewrite <- app_assoc in H0. tauto.
        **  unfold unit_set in case3. subst BB_next. cbn [block_num]. lia.
  }

  (*拆分BBdelta的jump dest. jumpdest里包含，一个是来自BBnow的预定跳转信息，另一个是BBthennum和BBelsenum*)
  assert (separate_delta_jump_dest:
  BBjmp_dest_set BBdelta == unit_set(BBnow.(jump_info).(jump_dest_1)) ∪ BBjmp_dest_set then_delta ∪ BBjmp_dest_set else_delta ∪ unit_set(startnum) ∪ unit_set(S startnum)
  ).
  {
    rewrite eq_delta_prop. split; intros; sets_unfold.
    - destruct H as [x_ [cond1 cond2]].
      simpl in cond1. destruct cond1 as [head | tail].
      * destruct cond2.
        ** left. right. unfold unit_set. rewrite <- head in H. simpl in H. lia.
        ** right. unfold unit_set. rewrite <- head in H. subst BBnow'. cbn [jump_info] in H. simpl in H. 
           pose proof option_eq_some nat ((S startnum)) (a) as key.
           destruct key as [_ key]. pose proof (key H) as key. lia.
      * pose proof In_a_or_b_or_c BasicBlock x_ then_delta else_delta (BB_next :: nil) tail.
        destruct H as [c1_ | [c2_ | c3_]].
        ** left. left. left. right. unfold BBjmp_dest_set. exists x_. split. tauto. tauto.
        ** left. left. right. unfold BBjmp_dest_set. exists x_. split. tauto. tauto.
        ** destruct cond2 as [cond2 | cond2].
           *** left. left. left. left. unfold unit_set. subst BB_next. simpl in c3_. 
                destruct c3_ as [c3_ | c3_].
                **** rewrite <- c3_ in cond2. simpl in cond2. lia.
                **** tauto.
           *** simpl in c3_. destruct c3_ as [c3_ | c3_].
                **** rewrite <- c3_ in cond2. simpl in cond2. destruct BBnow_jump_kind as [p1 p2].
                    rewrite p2 in cond2. discriminate cond2.
                **** tauto.
    - destruct H as [[[[case1 | case2] | case3] | case4] | case5].
      * unfold BBjmp_dest_set. exists BB_next. split.
        ** assert (In BB_next (BB_next::nil)). simpl. tauto.
            pose proof In_sublist_then_in_list_last BasicBlock BB_next (BB_next :: nil) (BBnow'::then_delta ++ else_delta) H. 
            assert (naive: (BBnow' :: then_delta ++ else_delta) ++ BB_next :: nil = BBnow' :: then_delta ++ else_delta ++ BB_next :: nil).
            {
              rewrite app_assoc. reflexivity.
            }
            rewrite naive in H0. tauto.
        **  unfold unit_set in case1. subst BB_next. cbn [jump_info]. lia.
      * unfold BBjmp_dest_set in case2. destruct case2 as [x_ [cond1 cond2]].
        unfold BBjmp_dest_set. exists x_. split. 
        ** pose proof In_sublist_then_in_list_head BasicBlock x_ then_delta (else_delta ++ BB_next :: nil) cond1.
           pose proof In_add_one_list BasicBlock x_ BBnow' (then_delta ++ else_delta ++ BB_next :: nil) H. tauto.
        ** tauto.
      * unfold BBjmp_dest_set in case3. destruct case3 as [x_ [cond1 cond2]].
        unfold BBjmp_dest_set. exists x_. split. 
        ** pose proof In_sublist_then_in_list_middle BasicBlock x_ else_delta then_delta (BB_next :: nil) cond1.
           pose proof In_add_one_list BasicBlock x_ BBnow' (then_delta ++ else_delta ++ BB_next :: nil) H. tauto.
        ** tauto.
      * unfold BBjmp_dest_set. exists BBnow'. split.
        ** simpl. tauto.
        ** unfold unit_set in case4. subst BBnow'. cbn [jump_info]. left. cbn [jump_dest_1]. lia.
      * unfold BBjmp_dest_set. exists BBnow'. split.
        ** simpl. tauto.
        ** unfold unit_set in case5. subst BBnow'. cbn [jump_info]. right. cbn [jump_dest_2]. rewrite case5. reflexivity. 
  }

  assert (head_then: (hd empty_block then_delta).(block_num) = BB_then_now.(block_num)).
  {  
    pose proof BBgen_head_prop c1 BB_then_now then_start_num. rewrite <- H. reflexivity.
  }

  assert (head_else: (hd empty_block else_delta).(block_num) = BB_else_now.(block_num)).
  {  
    pose proof BBgen_head_prop c2 BB_else_now then_end_num. rewrite <- H. reflexivity.
  }

  (*BBnow < startnum = BBthennum < BBelsenum < BBnextnum < then_end_num < else_endnum = endnum, TODO IMPORTANT*)
  assert (le_chain: lt BBnow.(block_num) startnum /\ lt then_end_num endnum /\ lt startnum then_end_num /\ lt (S (S startnum)) endnum).
  {
    admit.
  }

  repeat split.
  (*branch 1: 证明去掉头部的number后， BBdelta的所有num都大于等于startnum*)
  - left. rename H into A. unfold BBnum_set in A. destruct A as [BB A]. destruct A as [A1 A2].
    sets_unfold in separate_delta_num. 
    unfold unit_set in separate_delta_num. 
    sets_unfold in separate_delta_num. 
    unfold BBnum_set in separate_delta_num.
    specialize (separate_delta_num n).
    destruct separate_delta_num as [separate_delta_num separate_delta_num2].
    clear separate_delta_num2.
    assert (temp: (exists BB : BasicBlock, In BB (tl BBdelta) /\ BB.(block_num) = n) ).
    {
      exists BB. split. tauto. tauto.
    }
    specialize (separate_delta_num temp).
    clear temp.
    destruct separate_delta_num as [[case1 | case2] | case3 ]. 
    + destruct case1 as [x [cond1 cond2]].
      unfold all_ge in c1_prop1. specialize (c1_prop1 n).
      pose proof In_head_or_body BasicBlock x empty_block then_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2.  rewrite head_then in cond2. rewrite <- cond2. subst BB_then_now. cbn [block_num]. lia.
      ** assert(temp: BBnum_set (tl then_delta) n).
          {
            unfold BBnum_set. exists x. split. tauto. tauto.
          }
          specialize (c1_prop1 temp). destruct c1_prop1 as [c1_prop1 | c1_prop1].
          *** lia.
          *** pose proof c1_prop1. sets_unfold in H. specialize (H n). tauto.
    + destruct case2 as [x [cond1 cond2]].
      unfold all_ge in c2_prop1. specialize (c2_prop1 n).
      pose proof In_head_or_body BasicBlock x empty_block else_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2. rewrite head_else in cond2. rewrite <- cond2. subst BB_else_now. cbn [block_num]. lia. (*使用 c1_prop2*)
      ** assert(temp: BBnum_set (tl else_delta) n).
          {
            unfold BBnum_set. exists x. split. tauto. tauto.
          }
          specialize (c2_prop1 temp). destruct c2_prop1 as [c2_prop1 | c2_prop1].
          *** lia. (* c2_prop1和c1_prop2 *)
          *** pose proof c2_prop1. sets_unfold in H. specialize (H n). tauto.
    + lia.
  (*branch 2: 证明去掉头部的number后， BBdelta的所有num都小于endnum*) 
  - admit.
  (*branch 3: 证明BBdelta的所有jump dest都在[startnum, endnum] ∪ 预定跳转信息里*)
  - clear c1_prop1 c1_prop2 c2_prop1 c2_prop2.
    sets_unfold. intros. rename H into A. unfold BBjmp_dest_set in A. destruct A as [BB A]. destruct A as [A1 A2]. 
    unfold unit_set in separate_delta_jump_dest.
    sets_unfold in separate_delta_jump_dest.
    unfold BBjmp_dest_set in separate_delta_jump_dest.
    specialize (separate_delta_jump_dest a).
    destruct separate_delta_jump_dest as [separate_delta_jump_dest separate_delta_jump_dest2].
    clear separate_delta_jump_dest2.
    assert (temp: (exists BB : BasicBlock, In BB BBdelta /\ (jump_dest_1 BB.(jump_info) = a \/ jump_dest_2 BB.(jump_info) = Some a)) ).
    {
      exists BB. split. tauto. tauto.
    }
    specialize (separate_delta_jump_dest temp).
    clear temp.
    destruct separate_delta_jump_dest as [[[[case1 | case2]| case3] | case4] | case5].
    + right. unfold unit_set. tauto.
    +   (*用c1_prop3*)
      destruct case2 as [x [cond1 cond2]]. 
      unfold BBjmp_dest_set in c1_prop3. specialize (c1_prop3 a). sets_unfold in c1_prop3.
      assert (temp: (exists BB : BasicBlock, In BB then_delta /\ (jump_dest_1 BB.(jump_info) = a \/ jump_dest_2 BB.(jump_info) = Some a))).
      {
        exists x. split. tauto. tauto.
      }
      specialize (c1_prop3 temp).
      destruct c1_prop3 as [c1_prop3 | c1_prop3].
      *  left. split.
        unfold section in c1_prop3.  lia.
        unfold unit_set in c1_prop3. subst BB_then_now. simpl in c1_prop3. unfold section in c1_prop3. lia.
      *  left. unfold section. unfold unit_set in c1_prop3. subst BB_then_now. simpl in c1_prop3. split.
        ** lia.
        ** lia.
    + (*用c2_prop3*)
      destruct case3 as [x [cond1 cond2]].
      unfold BBjmp_dest_set in c2_prop3. specialize (c2_prop3 a). sets_unfold in c2_prop3.
      assert (temp: (exists BB : BasicBlock, In BB else_delta /\ (jump_dest_1 BB.(jump_info) = a \/ jump_dest_2 BB.(jump_info) = Some a))).
      {
        exists x. split. tauto. tauto.
      }
      specialize (c2_prop3 temp).
      destruct c2_prop3 as [c2_prop3 | c2_prop3].
      *  left. split.
        unfold section in c2_prop3.  lia.
        unfold unit_set in c2_prop3. subst BB_else_now. simpl in c2_prop3. unfold section in c2_prop3. lia.
      *  left. unfold section. unfold unit_set in c2_prop3. subst BB_else_now. simpl in c2_prop3. split.
        ** lia.
        ** lia.
    + left. unfold section. lia.
    + left. unfold section. lia.
Admitted.

Lemma Q_while_BBgen_range:
forall (e: expr) (c1 c2: list cmd),

    P_BBgen_range cmd_BB_gen c1 ->
    P_BBgen_range cmd_BB_gen c2 ->

    Q_BBgen_range (CWhile c1 e c2).
Proof.
  Admitted.

Lemma length_eq : forall (A : Type) (xs ys : list A),
  xs = ys -> length xs = length ys.
Proof.
  intros A xs ys H.
  rewrite H.
  reflexivity.
Qed.

(*这个肯定成立，没有新的block*)
Lemma Q_asgn_BBgen_range:
forall  (x: var_name) (e: expr),
    Q_BBgen_range (CAsgn x e).
Proof.
  intros. unfold Q_BBgen_range. intros. simpl in H0.
  unfold to_result in H1. simpl in H1. apply cut_eq_part_list_l in H1. 
  repeat split.
  - unfold all_ge. intros. right. rewrite <- H1. simpl. unfold BBnum_set. sets_unfold.
    intros. split.
    + intros. destruct H3 as [BB [H3 H4]]. simpl in H3. tauto.
    + intros. tauto.
  - unfold all_lt. intros. right. rewrite <- H1. simpl. unfold BBnum_set. sets_unfold.
    intros. split.
    + intros. destruct H3 as [BB [H3 H4]]. simpl in H3. tauto.
    + intros. tauto.
  - unfold BBjmp_dest_set. sets_unfold. intros. 
    destruct H2 as [BB [H2 H3]].
    destruct H3 as [H3 | H3].
    + right. unfold unit_set. subst BBdelta. simpl in H2. destruct H2. subst BB. simpl in H3. rewrite H3. 
      tauto. 
      tauto.
    + right.
      unfold unit_set. subst BBdelta. simpl in H2. destruct H2. subst BB. simpl in H3. destruct H. rewrite H1 in H3.
      discriminate H3. tauto.
Qed.

Lemma P_BBgen_nil: forall (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results),
    P_BBgen_range cmd_BB_gen nil.
Proof.
  intros. unfold P_BBgen_range. intros. simpl in H0. unfold to_result in H0. simpl in H0. 



(* {
  destruct BBdelta. tauto. pose proof length_eq BasicBlock (BBnow :: nil) (BBnow' :: b :: BBdelta) H1. discriminate.
} 
  rewrite H2. split.

  - unfold BB_all_ge. intros. tauto.
  - unfold BB_all_lt. intros. split. 
    + intros. tauto.
    + simpl. 
  *)

Admitted.

Lemma P_BBgen_con:
    forall (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results) (c: cmd) (cmds: list cmd),
    Q_BBgen_range c ->
    P_BBgen_range cmd_BB_gen cmds ->
    P_BBgen_range cmd_BB_gen (c::cmds).
Proof.
Admitted.


Section BB_gen_range_sound.

Variable cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results.
Variable BB_gen_range_soundness: forall (c: cmd), Q_BBgen_range c.

Fixpoint BBgen_list_range_soundness (cmds: list cmd): P_BBgen_range cmd_BB_gen cmds :=
  match cmds with
  | nil => P_BBgen_nil cmd_BB_gen
  | c :: cmds0 => P_BBgen_con cmd_BB_gen c cmds0 (BB_gen_range_soundness c) (BBgen_list_range_soundness cmds0)
  end.

End BB_gen_range_sound.

Fixpoint BB_gen_range_soundness (c: cmd): Q_BBgen_range c :=
  match c with
  | CAsgn x e => Q_asgn_BBgen_range x e
  | CIf e cmds1 cmds2 =>
      Q_if_BBgen_range e cmds1 cmds2
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds1)
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds2)
  | CWhile cmds1 e cmds2 =>
      Q_while_BBgen_range e cmds1 cmds2
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds1)
        (BBgen_list_range_soundness cmd_BB_gen BB_gen_range_soundness cmds2)
  end.


Lemma BBgen_range_single_soundness_correct:
    forall (c: cmd),
    Q_BBgen_range c.
Proof.
    apply BB_gen_range_soundness.
Qed.

Lemma BBgen_range_list_soundness_correct:
    forall (cmds: list cmd),
    P_BBgen_range cmd_BB_gen cmds.
Proof.
    apply BBgen_list_range_soundness.
    pose proof BBgen_range_single_soundness_correct.
    apply H.
Qed.



