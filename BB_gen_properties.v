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
Require Import Main.utils.

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
    (forall n, natset n -> Nat.le num n).

Definition all_gt (natset: nat -> Prop)(num: nat): Prop :=
  (forall n, natset n -> Nat.lt num n).
  
Definition all_lt (natset: nat -> Prop)(num: nat): Prop :=
    (forall n, natset n -> Nat.lt n num).

(*定义自然数区间*)
Definition section (startnum endnum: nat) : nat -> Prop :=
  fun BBnum => Nat.le startnum BBnum /\ Nat.lt BBnum endnum.

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
    (BBnow.(block_num) < startnum)%nat ->
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
    lt BBnow.(block_num) startnum ->
     (
      all_ge (BBnum_set(tl BBdelta)) startnum /\
      all_lt (BBnum_set(tl BBdelta)) endnum /\ 
      BBjmp_dest_set BBdelta ⊆  (section startnum endnum) ∪ unit_set (BBnow.(jump_info).(jump_dest_1))
    ).

Definition P_BBgen_range_wo (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results)(cmds: list cmd): Prop :=
  forall startnum endnum BBs BBnow BBdelta,
  let res := (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow startnum) in
  let basicblocks := res.(BasicBlocks) in
  (BBnow.(jump_info).(jump_kind) = UJump /\ BBnow.(jump_info).(jump_dest_2) = None) ->
  endnum = res.(next_block_num)
  -> 
    basicblocks = BBs ++ BBdelta ->
  (BBnow.(block_num) < startnum)%nat ->
  (
    all_ge (BBnum_set(tl BBdelta)) startnum /\
    all_lt (BBnum_set(tl BBdelta)) endnum /\ 
    BBjmp_dest_set BBdelta ⊆  (section startnum endnum)
  ).

Definition Q_BBgen_range_wo (c: cmd): Prop :=
  forall startnum endnum BBs BBnow BBdelta,
  let res := (cmd_BB_gen c BBs BBnow startnum) in
  let basicblocks := res.(BasicBlocks) in
  (BBnow.(jump_info).(jump_kind) = UJump /\ BBnow.(jump_info).(jump_dest_2) = None) ->
  endnum = res.(next_block_num) ->
  basicblocks = BBs  ++ BBdelta ->
  lt BBnow.(block_num) startnum ->
    (
    all_gt (BBnum_set(tl BBdelta)) startnum /\
    all_lt (BBnum_set(tl BBdelta)) endnum /\ 
    BBjmp_dest_set BBdelta ⊆  (section startnum endnum)
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

(*如果一个元素在一个列表里，它要么是这个列表的最后一个，要么就在前半部分里*)
Lemma In_pre_or_tail:
  forall (A: Type) (a b: A)(l: list A),
  In a (l ++ b::nil) -> a = b \/ In a l.
Proof.
  intros. induction l.
  - simpl in H. destruct H as [? | ?]. left. rewrite H. tauto. tauto.
  - simpl in H. destruct H as [? | ?]. right. rewrite H. unfold In. left. tauto.
    pose proof IHl H. destruct H0. left. tauto. right. unfold In. right. tauto. 
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

(* ======================================================================================================================================= *)

(*对于一个cmd，无论它是否传入已经生成的BBs，在其他情况相同的情况下，其拿到的BBn都是一样的*)
Lemma eq_BBn:
  forall (BBs: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat)(c: cmd),
  (cmd_BB_gen c BBs BBnow BBnum).(BBn) = (cmd_BB_gen c nil BBnow BBnum).(BBn).
Proof.
  intros.
  unfold cmd_BB_gen.
  destruct c.
  - simpl. reflexivity.
  - cbn [BBn]. reflexivity.
  - cbn [BBn]. reflexivity.
Qed.

(*对于一个cmd，无论传入的BBs如何，在其他情况相同的情况下，其拿到的BBn都是一样的*)
Lemma eq_BBn2:
  forall (BBs1 BBs2: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat)(c: cmd),
  (cmd_BB_gen c BBs1 BBnow BBnum).(BBn) = (cmd_BB_gen c BBs2 BBnow BBnum).(BBn).
Proof.
  intros.
  unfold cmd_BB_gen.
  destruct c.
  - simpl. reflexivity.
  - cbn [BBn]. reflexivity.
  - cbn [BBn]. reflexivity.
Qed.

(*对于一个cmd，无论它是否传入已经生成的BBs，在其他情况相同的情况下，其拿到的nextblocknum都是一样的*)
Lemma eq_next_block_num:
  forall (BBs: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat)(c: cmd),
  (cmd_BB_gen c BBs BBnow BBnum).(next_block_num) = (cmd_BB_gen c nil BBnow BBnum).(next_block_num).
Proof.
  intros.
  unfold cmd_BB_gen.
  destruct c.
  - simpl. reflexivity.
  - cbn [next_block_num]. reflexivity.
  - cbn [next_block_num]. reflexivity.
Qed.

(*对于一个cmd，无论传入的BBs如何，在其他情况相同的情况下，其拿到的nextblocknum都是一样的*)
Lemma eq_next_block_num2:
  forall (BBs1 BBs2: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat)(c: cmd),
  (cmd_BB_gen c BBs1 BBnow BBnum).(next_block_num) = (cmd_BB_gen c BBs2 BBnow BBnum).(next_block_num).
Proof.
  intros.
  unfold cmd_BB_gen.
  destruct c.
  - simpl. reflexivity.
  - cbn [next_block_num]. reflexivity.
  - cbn [next_block_num]. reflexivity.
Qed.

(*(*对于一个cmd list，无论传入的BBs如何，在其他情况相同的情况下，其拿到的BBn都是一样的*)*)
Lemma eq_BBn_list:
  forall (BBs1 BBs2: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat)(c: list cmd),
  (list_cmd_BB_gen cmd_BB_gen c BBs1 BBnow BBnum).(BBn) = (list_cmd_BB_gen cmd_BB_gen c BBs2 BBnow BBnum).(BBn).
Proof.
  intros. revert BBs1. revert BBs2. revert BBnow. revert BBnum.
  induction c.
  - simpl. reflexivity.
  - intros. cbn [list_cmd_BB_gen].
    assert (eq_prop_BBn: (cmd_BB_gen a BBs1 BBnow BBnum).(BBn) = (cmd_BB_gen a BBs2 BBnow BBnum).(BBn)).
    {
      apply eq_BBn2.
    }
    rewrite eq_prop_BBn.
    assert (eq_prop_next_block_num: (cmd_BB_gen a BBs1 BBnow BBnum).(next_block_num) = (cmd_BB_gen a BBs2 BBnow BBnum).(next_block_num)).
    {
      apply eq_next_block_num2.
    }
    rewrite eq_prop_next_block_num.
    specialize (IHc (cmd_BB_gen a BBs2 BBnow BBnum).(next_block_num) (cmd_BB_gen a BBs2 BBnow BBnum).(BBn)).
    specialize (IHc (cmd_BB_gen a BBs2 BBnow BBnum).(BasicBlocks)).
    specialize (IHc (cmd_BB_gen a BBs1 BBnow BBnum).(BasicBlocks)).
    tauto.
Qed.

(*(*对于一个cmd list，无论传入的BBs如何，在其他情况相同的情况下，其拿到的nextblocknum都是一样的*)*)
Lemma eq_next_block_num_list:
  forall (BBs1 BBs2: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat)(c: list cmd),
  (list_cmd_BB_gen cmd_BB_gen c BBs1 BBnow BBnum).(next_block_num) = (list_cmd_BB_gen cmd_BB_gen c BBs2 BBnow BBnum).(next_block_num).
Proof.
  intros. revert BBs1. revert BBs2. revert BBnow. revert BBnum.
  induction c.
  - simpl. reflexivity.
  - intros. cbn [list_cmd_BB_gen].
    assert (eq_prop_BBn: (cmd_BB_gen a BBs1 BBnow BBnum).(BBn) = (cmd_BB_gen a BBs2 BBnow BBnum).(BBn)).
    {
      apply eq_BBn2.
    }
    rewrite eq_prop_BBn.
    assert (eq_prop_next_block_num: (cmd_BB_gen a BBs1 BBnow BBnum).(next_block_num) = (cmd_BB_gen a BBs2 BBnow BBnum).(next_block_num)).
    {
      apply eq_next_block_num2.
    }
    rewrite eq_prop_next_block_num.
    specialize (IHc (cmd_BB_gen a BBs2 BBnow BBnum).(next_block_num) (cmd_BB_gen a BBs2 BBnow BBnum).(BBn)).
    specialize (IHc (cmd_BB_gen a BBs2 BBnow BBnum).(BasicBlocks)).
    specialize (IHc (cmd_BB_gen a BBs1 BBnow BBnum).(BasicBlocks)).
    tauto.
Qed.

(* ======================================================================================================================================= *)

(*对于一个cmd，它产生的Basicblocks的结果等于传入的BBs ++ 新生成的，新生成的部分可以用(cmd_BB_gen c nil BBnow BBnum) 来表示*)
Lemma Q_add_BBs_in_generation_reserves_BB_sound(c: cmd):
forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
  to_result (cmd_BB_gen c BBs BBnow BBnum) = BBs ++ to_result (cmd_BB_gen c nil BBnow BBnum).
Proof.
  intros.
  destruct c.
  - simpl. reflexivity.
  - unfold to_result. 
    assert ((cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil = (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BBn) :: nil).
    {
      reflexivity.
    }
    rewrite H.
    assert (eq: (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) = BBs ++
    (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BasicBlocks)).
    {
      unfold cmd_BB_gen.
      simpl.
      reflexivity.
    }
    rewrite eq. apply app_assoc_reverse.
  - unfold to_result.
    assert ((cmd_BB_gen (CWhile pre e body) BBs BBnow BBnum).(BBn) :: nil = (cmd_BB_gen (CWhile pre e body) nil BBnow BBnum).(BBn) :: nil).
    {
      reflexivity.
    }
    rewrite H.
    assert (eq: (cmd_BB_gen (CWhile pre e body) BBs BBnow BBnum).(BasicBlocks) = BBs ++
    (cmd_BB_gen (CWhile pre e body) nil BBnow BBnum).(BasicBlocks)).
    {
      unfold cmd_BB_gen.
      simpl.
      reflexivity.
    }
    rewrite eq. apply app_assoc_reverse.
Qed.

(* 对于一串cmds，在生成基本块的时候，BBs ++ 不传BBs得到的结果 = 传BBs的结果；BBs是已经产生的基本块列表*)
Lemma add_BBs_in_generation_reserves_BB:
forall (cmds: list cmd)(BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
  to_result (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum) = BBs ++ to_result (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).
Proof.
  intros. revert BBs BBnow BBnum.
  induction cmds.
  - simpl. reflexivity.
  - intros. cbn [list_cmd_BB_gen].
    assert (eq_prop_BBn: (cmd_BB_gen a BBs BBnow BBnum).(BBn) = (cmd_BB_gen a nil BBnow BBnum).(BBn)).
    {
      apply eq_BBn2.
    }
    rewrite eq_prop_BBn.
    assert (eq_prop_next_block_num: (cmd_BB_gen a BBs BBnow BBnum).(next_block_num) = (cmd_BB_gen a nil BBnow BBnum).(next_block_num)).
    {
      apply eq_next_block_num2.
    }
    rewrite eq_prop_next_block_num.
    unfold to_result in IHcmds.
    assert (IH_prop: (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BBn) :: nil = (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(BBn) :: nil).
    {
      apply cut_nil_r. apply eq_BBn_list.
    }
    pose proof (IHcmds ((cmd_BB_gen a BBs BBnow BBnum).(BasicBlocks)) (cmd_BB_gen a nil BBnow BBnum).(BBn) (cmd_BB_gen a nil BBnow BBnum).(next_block_num)) as key1.
    assert (IH_prop2: ((list_cmd_BB_gen cmd_BB_gen cmds (cmd_BB_gen a BBs BBnow BBnum).(BasicBlocks)
    (cmd_BB_gen a nil BBnow BBnum).(BBn) (cmd_BB_gen a nil BBnow BBnum).(next_block_num)).(BBn) :: nil) = (list_cmd_BB_gen cmd_BB_gen cmds nil (cmd_BB_gen a nil BBnow BBnum).(BBn)
    (cmd_BB_gen a nil BBnow BBnum).(next_block_num)).(BBn) :: nil).
    {
      apply cut_nil_r. apply eq_BBn_list.
    }
    rewrite IH_prop2 in key1.
 
    pose proof (cut_eq_part_list_r BasicBlock ((list_cmd_BB_gen cmd_BB_gen cmds nil (cmd_BB_gen a nil BBnow BBnum).(BBn)
    (cmd_BB_gen a nil BBnow BBnum).(next_block_num)).(BBn) :: nil) ((list_cmd_BB_gen cmd_BB_gen cmds (cmd_BB_gen a BBs BBnow BBnum).(BasicBlocks)
    (cmd_BB_gen a nil BBnow BBnum).(BBn) (cmd_BB_gen a nil BBnow BBnum).(next_block_num)).(BasicBlocks)) ((cmd_BB_gen a BBs BBnow BBnum).(BasicBlocks) ++
    (list_cmd_BB_gen cmd_BB_gen cmds nil (cmd_BB_gen a nil BBnow BBnum).(BBn)
       (cmd_BB_gen a nil BBnow BBnum).(next_block_num)).(BasicBlocks))).
    rewrite app_assoc in key1. pose proof H key1 as key. clear H IH_prop2.
    unfold to_result. rewrite key.
    remember (cmd_BB_gen a nil BBnow BBnum) as a_nil_res.
    remember (cmd_BB_gen a BBs BBnow BBnum) as a_res.
    pose proof (IHcmds a_nil_res.(BasicBlocks) a_nil_res.(BBn) a_nil_res.(next_block_num)) as key3.
    assert(eq2: (list_cmd_BB_gen cmd_BB_gen cmds a_nil_res.(BasicBlocks) a_nil_res.(BBn)
    a_nil_res.(next_block_num)).(BBn) :: nil =  (list_cmd_BB_gen cmd_BB_gen cmds nil a_nil_res.(BBn) a_nil_res.(next_block_num)).(BBn) :: nil).
    {
      apply cut_nil_r. apply eq_BBn_list.
    }
    rewrite eq2 in key3.
    pose proof (cut_eq_part_list_r BasicBlock ((list_cmd_BB_gen cmd_BB_gen cmds nil a_nil_res.(BBn) a_nil_res.(next_block_num)).(BBn) :: nil) (list_cmd_BB_gen cmd_BB_gen cmds a_nil_res.(BasicBlocks) a_nil_res.(BBn)
    a_nil_res.(next_block_num)).(BasicBlocks) (a_nil_res.(BasicBlocks) ++
    (list_cmd_BB_gen cmd_BB_gen cmds nil a_nil_res.(BBn) a_nil_res.(next_block_num)).(BasicBlocks))).
    rewrite app_assoc in key3. pose proof H key3 as key4. clear H eq2. clear key3. rename key4 into key2.
    rewrite key2.
    rewrite app_assoc_reverse.
    rewrite app_assoc_reverse.
    assert (eq3: a_res.(BasicBlocks) = BBs ++ a_nil_res.(BasicBlocks)).
    {
      rewrite Heqa_res. rewrite Heqa_nil_res.
      pose proof Q_add_BBs_in_generation_reserves_BB_sound a BBs BBnow BBnum as key3.
      unfold to_result in key3.
      assert(eq3: (cmd_BB_gen a BBs BBnow BBnum).(BBn) :: nil  = (cmd_BB_gen a nil BBnow BBnum).(BBn) :: nil).
      {
        apply cut_nil_r. apply eq_BBn2.
      }
      rewrite eq3 in key3. 
      pose proof (cut_eq_part_list_r BasicBlock ((cmd_BB_gen a nil BBnow BBnum).(BBn) :: nil) (cmd_BB_gen a BBs BBnow BBnum).(BasicBlocks) (BBs ++ (cmd_BB_gen a nil BBnow BBnum).(BasicBlocks))).
      rewrite app_assoc in key3. pose proof H key3 as key4. clear H eq3. clear key3. rename key4 into key3.
      tauto.
    }
    rewrite eq3.
    rewrite app_assoc_reverse.
    pose proof (IHcmds (BBs ++ a_nil_res.(BasicBlocks)) a_nil_res.(BBn) a_nil_res.(next_block_num)) as key3.
    pose proof eq_BBn_list (BBs ++ a_nil_res.(BasicBlocks)) a_nil_res.(BasicBlocks) a_nil_res.(BBn) a_nil_res.(next_block_num) cmds.
    rewrite H.
    reflexivity.
Qed.


(*如果cmd是CIf，那么新生成的BBs的最后一个Block，也就是BBnext，它的cmd为空*)
Lemma if_cmdgen_prop1:
  forall (e: expr) (c1 c2: list cmd) (BBs: list BasicBlock)(BBnow: BasicBlock)(BBnum : nat),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn).(cmd) = nil.
Proof.
  intros.
  cbn [cmd_BB_gen]. simpl. reflexivity.
Qed.

(*如果cmd是CIf，那么新生成的BBs的最后一个就是BBnext，它的num就是 BBnum*)
Lemma if_BBn_num_prop:
  forall (e: expr) (c1 c2: list cmd) (BBs: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn).(block_num) = BBnum.
Proof. 
  intros.
  cbn [cmd_BB_gen]. simpl. reflexivity.
Qed.


(* 对于一串cmds，在生成基本块的时候，BBs ++ 不传BBs得到的结果 = 传BBs的结果；BBs是已经产生的基本块列表, 排除BBn的版本*)
Lemma add_BBs_in_generation_reserves_BB_wo:
forall (cmds: list cmd)(BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
  (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BasicBlocks) = BBs ++ (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(BasicBlocks).
Proof.
  intros.
  pose proof add_BBs_in_generation_reserves_BB.
  specialize (H cmds BBs BBnow BBnum).
  unfold to_result in H.
  pose proof cut_eq_part_list_r BasicBlock ((list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(BBn) :: nil) (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BasicBlocks)  (BBs ++
  (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(BasicBlocks)).
  apply H0.
  rewrite app_assoc_reverse. rewrite <- H. 
  assert ((list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(BBn) :: nil = (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BBn) :: nil).
  {
    apply cut_nil_r. apply eq_BBn_list.
  }
  rewrite H1. reflexivity.
Qed.


(* ======================================================================================================================================= *)


(*这里说的是，在生成基本块的时候，无论是否传BBs，只要BBnum一样，那么最后的next_block_num都一样*)
Lemma add_BBs_in_generation_retains_next_block_num:
  forall (cmds : list cmd) (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
    (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(next_block_num) =
    (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(next_block_num).
Proof.
  intros.
  pose proof eq_next_block_num_list nil BBs BBnow BBnum cmds.
  tauto.
Qed.

(*如果传入的BBnow的num小于BBnum（似乎不需要用到），那么BBnum的num小于等于next_block_num ====================================================================================================== *)
(*要写成互递归了，因为要拿到c1中间的结果进行比较*)

(*如果BBnow的num小于分配的num，那么总有最后所在的BB的num小于下一个分配的num*)

Definition Q_inherit_lt_num_prop_mutual (c: cmd): Prop :=
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
    (lt BBnow.(block_num) BBnum) -> (is_asgn(c) /\ le BBnum (cmd_BB_gen c BBs BBnow BBnum).(next_block_num)) \/ (~is_asgn(c)) /\ lt BBnum (cmd_BB_gen c BBs BBnow BBnum).(next_block_num).

Definition P_inherit_lt_num_prop_mutual (cmds: list cmd): Prop := 
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
    (lt BBnow.(block_num) BBnum) -> le BBnum (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(next_block_num).

Lemma Q_inherit_lt_num_prop_mutual_asgn: 
  forall (x: var_name) (e: expr),
    Q_inherit_lt_num_prop_mutual (CAsgn x e).
Proof.
  intros. unfold Q_inherit_lt_num_prop_mutual. intros.
  cbn[cmd_BB_gen]. simpl. lia.
Qed.

Lemma Q_inherit_lt_num_prop_mutual_if:
  forall (e: expr) (c1: list cmd) (c2: list cmd),
    P_inherit_lt_num_prop_mutual c1 -> P_inherit_lt_num_prop_mutual c2 -> Q_inherit_lt_num_prop_mutual (CIf e c1 c2).
Proof.
  intros. unfold P_inherit_lt_num_prop_mutual in H. 
  unfold P_inherit_lt_num_prop_mutual in H0.
  unfold Q_inherit_lt_num_prop_mutual. intros.
  cbn[cmd_BB_gen]. simpl.
  remember ({|
              block_num := S (S BBnum);
              commands := nil;
              jump_info := {|
                          jump_kind := UJump;
                          jump_dest_1 := BBnum;
                          jump_dest_2 := None;
                          jump_condition := None |} |}) as BBnow_else.
  remember ({|
              block_num := S BBnum;
              commands := nil;
              jump_info := {|
                            jump_kind := UJump;
                            jump_dest_1 := BBnum;
                            jump_dest_2 := None;
                            jump_condition := None |} |}) as BBnow_then.
  remember ((list_cmd_BB_gen cmd_BB_gen c1 nil BBnow_then (S (S (S BBnum)))).(next_block_num)) as BBnum'.
  specialize (H0 nil BBnow_else BBnum'). 
  specialize (H nil BBnow_then (S (S (S BBnum)))).

  assert ((BBnum < BBnum')%nat). {
    assert ((BBnow_then.(block_num) < S (S (S BBnum)))%nat). {
      subst BBnow_then. simpl. lia.
    }
    pose proof H H2 as H. lia.
  }

  right. split.
  - tauto.
  - 

  assert(m: (BBnow_then.(block_num) < S (S (S BBnum)))%nat). {
    subst BBnow_then. simpl. lia.
  }

  specialize (H m).
  rewrite <- HeqBBnum' in H.

  assert ((BBnow_else.(block_num) < BBnum')%nat). {
    subst BBnow_else. simpl. lia. 
  }

  assert ((BBnum' <= (list_cmd_BB_gen cmd_BB_gen c2 nil BBnow_else BBnum').(next_block_num))%nat). {
    apply H0. subst BBnow_else. simpl. lia. 
  }
  lia.
Qed.


Lemma Q_inherit_lt_num_prop_mutual_while:
  forall (e: expr) (c1: list cmd) (c2: list cmd),
    P_inherit_lt_num_prop_mutual c1 -> P_inherit_lt_num_prop_mutual c2 -> Q_inherit_lt_num_prop_mutual (CWhile c1 e c2).
Proof.
Admitted. (*DONT CARE ABOUT WHILE*)

Lemma P_inherit_lt_num_prop_mutual_nil:
  P_inherit_lt_num_prop_mutual nil.
Proof.
  unfold P_inherit_lt_num_prop_mutual. intros. simpl. lia.
Qed. 

Lemma P_inherit_lt_num_prop_mutual_cons:
  forall (c: cmd) (cmds: list cmd),
    Q_inherit_lt_num_prop_mutual c ->
    P_inherit_lt_num_prop_mutual cmds ->
    P_inherit_lt_num_prop_mutual (c :: cmds).
Proof.
  intros. unfold P_inherit_lt_num_prop_mutual. intros.
  simpl. 
  unfold Q_inherit_lt_num_prop_mutual in H.
  specialize (H BBs BBnow BBnum H1).
  unfold P_inherit_lt_num_prop_mutual in H0.
  remember (cmd_BB_gen c BBs BBnow BBnum).(next_block_num) as midnum.

  specialize (H0 ((cmd_BB_gen c BBs BBnow BBnum).(BasicBlocks)) ((cmd_BB_gen c BBs BBnow BBnum).(BBn)) midnum).

  assert(((cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num) < midnum)%nat). {
    simpl.
    destruct c.
    - simpl. simpl in Heqmidnum. lia.
    - 
      assert(((cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn)).(block_num) = BBnum). {
        cbn [cmd_BB_gen]. simpl. reflexivity. 
      }
        destruct H. destruct H. simpl in H. lia.
        destruct H.
        rewrite H2 in H0. lia.
    - admit. (*DONT CARE ABOUT WHILE*)
    }
  pose proof H0 H2 as H0. lia.
Admitted. (*DONT CARE ABOUT WHILE, no other admits*)




Section inherit_lt_num_prop_mutual.

Variable inherit_lt_num_prop_mutual: forall (c: cmd), Q_inherit_lt_num_prop_mutual c.

Fixpoint inherit_lt_num_prop_mutual_list (cmds: list cmd): P_inherit_lt_num_prop_mutual cmds :=
  match cmds with
  | nil => P_inherit_lt_num_prop_mutual_nil
  | c :: cmds0 => P_inherit_lt_num_prop_mutual_cons c cmds0 (inherit_lt_num_prop_mutual c) (inherit_lt_num_prop_mutual_list cmds0)
  end.

End inherit_lt_num_prop_mutual.

Fixpoint inherit_lt_num_prop_mutual (c: cmd): Q_inherit_lt_num_prop_mutual c :=
  match c with 
  | CAsgn x e => Q_inherit_lt_num_prop_mutual_asgn x e
  | CIf e cmds1 cmds2 =>
      Q_inherit_lt_num_prop_mutual_if e cmds1 cmds2
        (inherit_lt_num_prop_mutual_list inherit_lt_num_prop_mutual cmds1)
        (inherit_lt_num_prop_mutual_list inherit_lt_num_prop_mutual cmds2)
  | CWhile cmds1 e cmds2 =>
      Q_inherit_lt_num_prop_mutual_while e cmds1 cmds2
        (inherit_lt_num_prop_mutual_list inherit_lt_num_prop_mutual cmds1)
        (inherit_lt_num_prop_mutual_list inherit_lt_num_prop_mutual cmds2)
  end.



Lemma inherit_lt_num_prop_mutual_sound:
  forall (c: cmd),
    Q_inherit_lt_num_prop_mutual c.
Proof.
  apply inherit_lt_num_prop_mutual.
Qed.

Lemma inherit_lt_num_prop_mutual_list_sound:
  forall (cmds: list cmd),
    P_inherit_lt_num_prop_mutual cmds.
Proof.
  apply inherit_lt_num_prop_mutual_list.
  pose proof inherit_lt_num_prop_mutual_sound.
  apply H.
Qed.

(*如果BBnow的num小于分配的num，那么总有最后所在的BB的num小于下一个分配的num*)
Lemma inherit_lt_num_prop:
  forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: cmd),
    (lt BBnow.(block_num) BBnum) -> (lt (cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num) (cmd_BB_gen c BBs BBnow BBnum).(next_block_num)).
Proof.
  intros. destruct c. 
  - simpl. lia.
  - assert (((cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn)).(block_num) = BBnum). simpl. lia. 
    rewrite H0.
    pose proof inherit_lt_num_prop_mutual_sound (CIf e c1 c2). 
    unfold Q_inherit_lt_num_prop_mutual in H1. 
    specialize (H1 BBs BBnow BBnum H).
    destruct H1. destruct H1. simpl in H1. lia.
    destruct H1. tauto.
  - admit. (*DONT CARE ABOUT WHILE*)
Admitted. (* QED *)


Lemma inherit_lt_num_prop_list:
  forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: list cmd),
    (lt BBnow.(block_num) BBnum) -> (lt (list_cmd_BB_gen cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num) (list_cmd_BB_gen cmd_BB_gen c BBs BBnow BBnum).(next_block_num)).
Proof.
  intros. revert BBs BBnow BBnum H.
  induction c; intros.
  - simpl. tauto.
  - cbn[list_cmd_BB_gen].
    remember ((cmd_BB_gen a BBs BBnow BBnum).(BasicBlocks)) as BBs_a.
    remember ((cmd_BB_gen a BBs BBnow BBnum).(BBn)) as BBnow_a.
    remember ((cmd_BB_gen a BBs BBnow BBnum).(next_block_num)) as BBnum_a.
    specialize (IHc BBs_a BBnow_a BBnum_a).
    pose proof inherit_lt_num_prop BBs BBnow BBnum a H.
    subst BBnow_a. subst BBnum_a.
    pose proof IHc H0. tauto.
Qed.




Lemma bbnum_le_next_num:
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: list cmd),
    (lt BBnow.(block_num) BBnum) -> le BBnum (list_cmd_BB_gen cmd_BB_gen c BBs BBnow BBnum).(next_block_num).
Proof.
  intros BBs BBnow BBnum c. revert BBs BBnow BBnum. induction c.
  - simpl. lia.
  - cbn [list_cmd_BB_gen].
    destruct a.
    + simpl. intros. specialize (IHc BBs {|
    block_num := BBnow.(block_num);
    commands := BBnow.(cmd) ++ {| X := x; E := e |} :: nil;
    jump_info := BBnow.(jump_info) |} BBnum). simpl in IHc. specialize (IHc H). tauto.
    + intros. specialize (IHc ((cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks)) ((cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn)) ((cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num))).
      pose proof Q_inherit_lt_num_prop_mutual_if e c1 c2.
      pose proof inherit_lt_num_prop_mutual_list_sound c1.
      pose proof inherit_lt_num_prop_mutual_list_sound c2.
      specialize (H0 H1 H2). unfold Q_inherit_lt_num_prop_mutual in H0. specialize (H0 BBs BBnow BBnum H). 
      pose proof inherit_lt_num_prop BBs BBnow BBnum (CIf e c1 c2) H.
      specialize (IHc H3). lia.
    + intros. specialize (IHc ((cmd_BB_gen (CWhile pre e body) BBs BBnow BBnum).(BasicBlocks)) ((cmd_BB_gen (CWhile pre e body) BBs BBnow BBnum).(BBn)) ((cmd_BB_gen (CWhile pre e body) BBs BBnow BBnum).(next_block_num))).
      pose proof Q_inherit_lt_num_prop_mutual_while e pre body.
      pose proof inherit_lt_num_prop_mutual_list_sound pre.
      pose proof inherit_lt_num_prop_mutual_list_sound body.
      specialize (H0 H1 H2). unfold Q_inherit_lt_num_prop_mutual in H0. specialize (H0 BBs BBnow BBnum H). 
      pose proof inherit_lt_num_prop BBs BBnow BBnum (CWhile pre e body) H.
      specialize (IHc H3). lia.
Qed.

Lemma bbnum_le_next_num_single_cmd:
  forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: cmd),
    (lt BBnow.(block_num) BBnum) -> (le BBnum (cmd_BB_gen c BBs BBnow BBnum).(next_block_num) ).
Proof.
  intros. destruct c. 
  - simpl. lia.
  - pose proof inherit_lt_num_prop BBs BBnow BBnum (CIf e c1 c2) H.
    pose proof if_BBn_num_prop e c1 c2 BBs BBnow BBnum. lia. 
  - admit. (*DONT CARE ABOUT WHILE*)
Admitted. (* QED *)



(* Used In aux proof.v *)
(*如果传入的BBnow的num小于BBnum，那么BBnow的num小于next_block_num*)
Lemma bbnow_num_lt_next_num:
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: list cmd),
    (lt BBnow.(block_num) BBnum) -> lt BBnow.(block_num) (list_cmd_BB_gen cmd_BB_gen c BBs BBnow BBnum).(next_block_num).
Proof.
  intros.
  pose proof (bbnum_le_next_num BBs BBnow BBnum c H).
  lia.
Qed. 


Lemma bbnow_num_le_BBn_num_single_cmd:
  forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: cmd),
    (lt BBnow.(block_num) BBnum) -> (le BBnow.(block_num)  (cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num) ).
Proof.
  intros. destruct c. 
  - simpl. lia.
  - assert (((cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn)).(block_num) = BBnum). simpl. lia. 
    rewrite H0. lia.
  - admit. (*DONT CARE ABOUT WHILE*)
Admitted. (* QED *)


Lemma bbnow_num_le_bbn_num:
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: list cmd),
    (lt BBnow.(block_num) BBnum) -> le BBnow.(block_num) (list_cmd_BB_gen cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num).
Proof.
  intros. revert BBs BBnow BBnum H. induction c; intros.
  - simpl. lia.  
  - cbn[list_cmd_BB_gen].
    pose proof bbnow_num_le_BBn_num_single_cmd BBs BBnow BBnum a H.
    specialize (IHc (cmd_BB_gen a BBs BBnow BBnum).(BasicBlocks) (cmd_BB_gen a BBs BBnow BBnum).(BBn) (cmd_BB_gen a BBs BBnow BBnum).(next_block_num)).
    pose proof inherit_lt_num_prop BBs BBnow BBnum a H.
    pose proof IHc H1. lia.
Qed.
(*END:  ====================================================================================================== *)


(* ======================================================================================================================================== *)


Definition Q_inherit_not_jmp_to_self (c: cmd): Prop :=
  forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
    (gt BBnow.(block_num) (jump_dest_1 BBnow.(jump_info))) ->
    (gt BBnum BBnow.(block_num)) ->
    gt (cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num) (jump_dest_1 (cmd_BB_gen c BBs BBnow BBnum).(BBn).(jump_info)).

Definition P_inherit_not_jmp_to_self(cmds: list cmd): Prop :=
  forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
  (gt BBnow.(block_num) (jump_dest_1 BBnow.(jump_info))) ->
  (gt BBnum BBnow.(block_num)) ->
  gt (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BBn).(block_num) (jump_dest_1 (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BBn).(jump_info)).

Lemma Q_inherit_not_jmp_to_self_asgn: 
  forall  (x: var_name) (e: expr),
  Q_inherit_not_jmp_to_self (CAsgn x e).
Proof. 
  unfold Q_inherit_not_jmp_to_self. intros.
  simpl.
  tauto.
Qed.

Lemma Q_inherit_not_jmp_to_self_if:
  forall  (e: expr) (c1: list cmd) (c2: list cmd),
  P_inherit_not_jmp_to_self (c1) -> P_inherit_not_jmp_to_self (c2) ->
  Q_inherit_not_jmp_to_self (CIf e c1 c2).
Proof.
  intros. unfold Q_inherit_not_jmp_to_self. intros.
  unfold P_inherit_not_jmp_to_self in H.
  unfold P_inherit_not_jmp_to_self in H0.
  cbn[cmd_BB_gen]. simpl.
  specialize (H BBs BBnow BBnum). pose proof H H1 as H.
  lia.
Qed.

Lemma Q_inherit_not_jmp_to_self_while:
  forall  (e: expr) (c1: list cmd) (c2: list cmd),
  P_inherit_not_jmp_to_self (c1) -> P_inherit_not_jmp_to_self (c2) ->
  Q_inherit_not_jmp_to_self (CWhile c1 e c2).
Proof.
Admitted.  (* DONT CARE ABOUT while *)

Lemma P_inherit_not_jmp_to_self_nil:
  P_inherit_not_jmp_to_self nil.
Proof.
  unfold P_inherit_not_jmp_to_self. intros. cbn[list_cmd_BB_gen]. simpl. apply H.
Qed.


Lemma P_inherit_not_jmp_to_self_cons:
forall (c: cmd) (cmds: list cmd),
  Q_inherit_not_jmp_to_self c ->
  P_inherit_not_jmp_to_self cmds ->
  P_inherit_not_jmp_to_self (c :: cmds).
Proof.
  unfold P_inherit_not_jmp_to_self. unfold Q_inherit_not_jmp_to_self. intros.
  cbn[list_cmd_BB_gen]. specialize (H BBs BBnow BBnum H1).
  specialize (H H2). 
  remember (cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num) as BBn.
  remember (jump_dest_1 ((cmd_BB_gen c BBs BBnow BBnum).(BBn)).(jump_info)) as dest1.
  specialize (H0  ((cmd_BB_gen c BBs BBnow BBnum).(BasicBlocks))  ((cmd_BB_gen c BBs BBnow BBnum).(BBn)) ((cmd_BB_gen c BBs BBnow BBnum).(next_block_num))).
  rewrite <- HeqBBn in *. rewrite <- Heqdest1 in *.
  assert(tmp: ((cmd_BB_gen c BBs BBnow BBnum).(next_block_num) > BBn)%nat). {
    rewrite HeqBBn. 
    pose proof inherit_lt_num_prop BBs BBnow BBnum c. 
    assert((BBnow.(block_num) < BBnum)%nat). lia. 
    specialize (H3 H4). lia.
  }
  pose proof H0 H tmp. 
  tauto.
Qed. 

Section inherit_not_jmp_to_self_sound.

Variable inherit_not_jmp_to_self_sound: forall (c: cmd), Q_inherit_not_jmp_to_self c.

Fixpoint inherit_list_not_jmp_to_self_sound (cmds: list cmd): P_inherit_not_jmp_to_self cmds :=
  match cmds with
  | nil => P_inherit_not_jmp_to_self_nil 
  | c :: cmds0 => P_inherit_not_jmp_to_self_cons c cmds0 (inherit_not_jmp_to_self_sound c) (inherit_list_not_jmp_to_self_sound cmds0)
  end.

End inherit_not_jmp_to_self_sound.

Fixpoint inherit_not_jmp_to_self_sound (c: cmd): Q_inherit_not_jmp_to_self c :=
  match c with
  | CAsgn x e => Q_inherit_not_jmp_to_self_asgn x e
  | CIf e cmds1 cmds2 =>
      Q_inherit_not_jmp_to_self_if e cmds1 cmds2
        (inherit_list_not_jmp_to_self_sound inherit_not_jmp_to_self_sound cmds1)
        (inherit_list_not_jmp_to_self_sound inherit_not_jmp_to_self_sound cmds2)
  | CWhile cmds1 e cmds2 =>
      Q_inherit_not_jmp_to_self_while e cmds1 cmds2
        (inherit_list_not_jmp_to_self_sound inherit_not_jmp_to_self_sound cmds1)
        (inherit_list_not_jmp_to_self_sound inherit_not_jmp_to_self_sound cmds2)
  end.

Lemma inherit_not_jmp_to_self_soundness_correct:
  forall (c: cmd),
  Q_inherit_not_jmp_to_self c.
Proof.
  apply inherit_not_jmp_to_self_sound.
Qed.

Lemma inherit_list_not_jmp_to_self_soundness_correct:
  forall (cmds: list cmd),
  P_inherit_not_jmp_to_self cmds.
Proof.
  apply inherit_list_not_jmp_to_self_sound.
  pose proof inherit_not_jmp_to_self_soundness_correct.
  apply H.
Qed.



(*如果BBnow不会jmp到他自己，那么其继承者也不会*)
Lemma inherit_not_jmp_to_self:
  forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: cmd),
    gt BBnow.(block_num) (jump_dest_1 BBnow.(jump_info)) ->
    gt BBnum BBnow.(block_num) ->
    gt (cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num) (jump_dest_1 (cmd_BB_gen c BBs BBnow BBnum).(BBn).(jump_info)).
Proof.
  pose proof inherit_not_jmp_to_self_soundness_correct.
  intros.
  unfold Q_inherit_not_jmp_to_self in H.
  specialize (H c BBs BBnow BBnum H0).
  specialize (H H1). tauto. 
Qed.





(* END ===================================================================================================*)


(*START：列表集合的一些性质 ==================================================================================================================================================================================================================== *)

Lemma head_eq_prop:
  forall (A: Type) (l1 l2: list A) (a b: A),
  a::l1 = b::l2 -> a = b.
Proof.
  intros. inversion H. reflexivity.
Qed.


Lemma tl_eq_prop:
  forall (A: Type) (l1 l2: list A) (a b: A),
  l1 ++ a :: nil  = l2 ++ b :: nil -> a = b.
Proof.
  apply tail_eq_prop.
Qed.

Lemma if_wont_be_nil:
  forall (e: expr) (c1 c2: list cmd) (BBs BBswo_: list BasicBlock) (BBnow BBnow'_: BasicBlock) (BBnum : nat),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) = BBs ++ BBnow'_ :: BBswo_
  ->
  BBswo_ <> nil.
Proof.
  intros. 
  pose proof Q_add_BBs_in_generation_reserves_BB_sound (CIf e c1 c2) BBs BBnow BBnum.
  unfold to_result in H0.
  pose proof cut_eq_part_list_r BasicBlock ((cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BBn) :: nil) (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) (BBs ++
  (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BasicBlocks)).
  rewrite <- app_assoc in H1. pose proof H1 H0 as H1. clear H0.
  rewrite H1 in H. apply cut_eq_part_list_l in H.
  cbn[cmd_BB_gen] in H. simpl in H.
  remember ({|
              block_num := BBnow.(block_num);
              commands := BBnow.(cmd);
              jump_info := {|
                jump_kind := CJump;
                jump_dest_1 := S BBnum;
                jump_dest_2 := Some (S (S(BBnum)));
                jump_condition := Some e |} |}) as BBnow_.
  remember ({|
            block_num := S BBnum;
            commands := nil;
            jump_info := {|
                         jump_kind := UJump;
                         jump_dest_1 := BBnum;
                         jump_dest_2 := None;
                         jump_condition := None |} |}) as BBnow_then.
  remember ({|
            block_num := S(S BBnum);
            commands := nil;
            jump_info := {|
                         jump_kind := UJump;
                         jump_dest_1 := BBnum;
                         jump_dest_2 := None;
                         jump_condition := None |} |}) as BBnow_else.
  remember (list_cmd_BB_gen cmd_BB_gen c1 nil BBnow_then
  (S (S (S BBnum)))) as BBgen_then_result.
  pose proof H.
  apply head_eq_prop in H. rewrite <- H in H0.
  assert (to_result BBgen_then_result ++
          to_result
          (list_cmd_BB_gen cmd_BB_gen c2 nil BBnow_else
            BBgen_then_result.(next_block_num)) = BBswo_). {
  inversion H0. tauto.
            
  }
  unfold to_result.
  pose proof not_nil_l BasicBlock ((BBgen_then_result.(BasicBlocks) ++ BBgen_then_result.(BBn) :: nil)) ((list_cmd_BB_gen cmd_BB_gen c2 nil BBnow_else BBgen_then_result.(next_block_num)).(BasicBlocks) ++
  (list_cmd_BB_gen cmd_BB_gen c2 nil BBnow_else BBgen_then_result.(next_block_num)).(BBn) :: nil).
  assert(tmp:  BBgen_then_result.(BasicBlocks) ++ BBgen_then_result.(BBn) :: nil <> nil).
  {
    pose proof not_nil_r BasicBlock BBgen_then_result.(BasicBlocks) (BBgen_then_result.(BBn) :: nil).
    assert (BBgen_then_result.(BBn) :: nil <> nil).
    {
      intros contra. inversion contra.
    }
    specialize (H4 H5). tauto.
  }
  specialize (H3 tmp). clear tmp. unfold to_result in H2. rewrite H2 in H3. tauto.
Qed.


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

(*x在 l1 ++ l2 ++ l3 中，那么必然在至少其中之一*)
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

(*x在 l1 中，那么必然在l1 ++ l2中 *)
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

(*x在 l1 中，那么必然在l2 ++ l1中 *)
Lemma In_sublist_then_in_list_last:
  forall (A: Type) (x: A) (l1 l2: list A),
  In x l1 -> In x (l2 ++ l1).
Proof.
  intros.
  induction l2.
  - simpl. tauto.
  - simpl. right. apply IHl2.
Qed.

(*在l1中，那么必然在l2 ++ l1 ++ l3中 *)
Lemma In_sublist_then_in_list_middle:
  forall (A: Type) (x: A) (l1 l2 l3: list A),
  In x l1 -> In x (l2 ++ l1 ++ l3).
Proof.
  intros.
  induction l2.
  - simpl. apply In_sublist_then_in_list_head. apply H.
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


(* 如果l1不为空，那么l1 ++ l2的第一个元素等于l1的第一个元素 *)
Lemma hd_A_and_B_is_hd_A_if_A_not_nil:
  forall (l1 l2: list BasicBlock),
  l1 <> nil -> hd empty_block (l1 ++ l2) = hd empty_block l1.
Proof.
  intros. induction l2.
  - simpl. rewrite append_nil_r. tauto.
  - simpl. unfold hd. destruct l1.
    + tauto.
    + reflexivity.
Qed.

(*END：列表集合的一些性质 =============================================================================================================================================================== *)

(* Jmp Info的继承性质  ============================================================================================================ *)

(*Jmp Info是会被继承下去的！*)
Lemma JmpInfo_inherit:
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum: nat) (c: cmd),
  ((cmd_BB_gen c BBs BBnow BBnum).(BBn)).(jump_info) = BBnow.(jump_info).
Proof.
  destruct c. 
  + reflexivity.
  + cbn [cmd_BB_gen]. simpl. reflexivity.
  + cbn [cmd_BB_gen]. simpl. reflexivity.
Qed.

Lemma JmpInfo_inherit_for_list:
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum: nat) (cmds: list cmd),
  ((list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BBn)).(jump_info) = BBnow.(jump_info).
Proof.
  intros. revert BBs BBnow BBnum.
  induction cmds; intros.
  + cbn[list_cmd_BB_gen]. simpl. tauto.
  + cbn[list_cmd_BB_gen].
    pose proof JmpInfo_inherit BBs BBnow BBnum a. 
    specialize (IHcmds (cmd_BB_gen a BBs BBnow BBnum).(BasicBlocks) (cmd_BB_gen a BBs BBnow BBnum).(BBn)  (cmd_BB_gen a BBs BBnow BBnum).(next_block_num)).
    rewrite IHcmds. apply H.
Qed.

(* ============================================================================================================ *)



(*START: BBgen Head ==============================================================================================================================*)
Lemma BBgen_head_prop_single_cmd:
  forall (c : cmd)(BBnow : BasicBlock) (BBnum : nat),
  let res := (cmd_BB_gen c nil BBnow BBnum) in
  (hd empty_block (res.(BasicBlocks) ++ res.(BBn)::nil)).(block_num) = BBnow.(block_num).
Proof.
  intros.
  unfold res. 
  destruct c.
  - simpl. reflexivity.
  - unfold cmd_BB_gen. simpl. reflexivity.
  - unfold cmd_BB_gen. simpl. reflexivity.
Qed.

Lemma BBgen_head_prop_single_cmd_wo_CIf:
  forall (e: expr)(c1 c2: list cmd)(BBnow : BasicBlock) (BBnum : nat),
  let res := (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum) in
  (hd empty_block (res.(BasicBlocks))).(block_num) = BBnow.(block_num).
Proof.
  intros.
  unfold res. 
  unfold cmd_BB_gen. simpl. reflexivity.

Qed.

(* 第一个Block的num就是BBnow的blocknum *)
Lemma BBgen_head_prop:
  forall (cmds : list cmd)(BBnow : BasicBlock) (BBnum : nat),
  let res := (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum) in
  (hd empty_block (res.(BasicBlocks) ++ res.(BBn)::nil)).(block_num) = BBnow.(block_num).
Proof.
  intros. unfold res. revert BBnow BBnum res.  
  induction cmds; intros.
  - simpl. reflexivity.
  - unfold res in IHcmds. cbn [list_cmd_BB_gen].
    pose proof BBgen_head_prop_single_cmd a BBnow BBnum as H_BBgen_cmd.
    simpl in H_BBgen_cmd.
    pose proof add_BBs_in_generation_reserves_BB cmds ((cmd_BB_gen a nil BBnow BBnum).(BasicBlocks)) (cmd_BB_gen a nil BBnow BBnum).(BBn) (cmd_BB_gen a nil BBnow BBnum).(next_block_num) as BBs_simpl.
    unfold to_result in BBs_simpl. rewrite BBs_simpl.
    clear BBs_simpl.
    remember ((cmd_BB_gen a nil BBnow BBnum)) as cmd_res.
    remember (list_cmd_BB_gen cmd_BB_gen cmds nil cmd_res.(BBn) cmd_res.(next_block_num)) as list_cmd_res.
    specialize (IHcmds cmd_res.(BBn) cmd_res.(next_block_num)). 
    
    (* 对比一下IHcmds和最终的结论，我们发现，实际上利用归纳假设只需要考虑BBnow是否在cmd_res中即可，这个是符合直觉的 *)
    pose proof classic (cmd_res.(BasicBlocks) = nil). destruct H as [A1 | A2].
    + rewrite A1. simpl. subst list_cmd_res. 
      rewrite IHcmds.
      pose proof BBgen_head_prop_single_cmd a BBnow BBnum.
      unfold res in H.
      subst cmd_res. rewrite A1 in H. simpl in H. apply H.
    + rewrite hd_A_and_B_is_hd_A_if_A_not_nil.
      pose proof BBgen_head_prop_single_cmd a BBnow BBnum.
      unfold res in H.
      rewrite hd_A_and_B_is_hd_A_if_A_not_nil in H.
      * subst cmd_res. apply H.
      * subst cmd_res. apply A2.
      * apply A2.
Qed.


(* 第一个Block的num就是BBnow的blocknum *)
Lemma BBgen_head_prop_wo:
  forall (cmds : list cmd)(BBnow : BasicBlock) (BBnum : nat),
  let res := (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum) in
  res.(BasicBlocks) <> nil ->
  (hd empty_block (res.(BasicBlocks))).(block_num) = BBnow.(block_num).
Proof.
  intros.
  pose proof BBgen_head_prop cmds BBnow BBnum. simpl in H0.
  rewrite hd_A_and_B_is_hd_A_if_A_not_nil in H0. apply H0. apply H.
Qed.



(*END: BBgen Head =========================================================================================================================================================================================*)


(*对于CIf而言，其nextblocknum等于else分支得到的nextblocknum*)
Lemma CIf_next_block_num_eq_else_next_block_num:
  forall (e: expr) (c1 c2: list cmd) (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum: nat),
    let BB_now_then := 
      {|
      block_num := S BBnum;
      commands := nil;
      jump_info :=
        {|
          jump_kind := UJump;
          jump_dest_1 := BBnum;
          jump_dest_2 := None;
          jump_condition := None;
        |}
      |} in
    let else_start_num := (list_cmd_BB_gen cmd_BB_gen c1 nil BB_now_then (S(S (S BBnum)))).(next_block_num) in
    let BB_now_else := 
      {|
      block_num := S (S BBnum);
      commands := nil;
      jump_info :=
        {|
          jump_kind := UJump;
          jump_dest_1 := BBnum;
          jump_dest_2 := None;
          jump_condition := None;
        |}
      |} in
    (cmd_BB_gen (CIf e c1 c2 ) BBs BBnow BBnum).(next_block_num) = (list_cmd_BB_gen cmd_BB_gen c2 nil BB_now_else else_start_num).(next_block_num).
Proof.
  intros.
  cbn [cmd_BB_gen]. cbn [next_block_num].
  subst else_start_num. subst BB_now_then. subst BB_now_else. reflexivity.
Qed.

Lemma cmd_BB_delta:
  forall (c: cmd)(BBs BBwo_last: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat),
(cmd_BB_gen c nil BBnow BBnum).(BasicBlocks) = BBwo_last -> (cmd_BB_gen c BBs BBnow BBnum).(BasicBlocks) = BBs ++ BBwo_last.
Proof.
  intros. pose proof Q_add_BBs_in_generation_reserves_BB_sound c BBs BBnow BBnum.
  unfold to_result in H0.
  pose proof eq_BBn BBs BBnow BBnum c. rewrite H1 in H0.
  pose proof cut_eq_part_list_r BasicBlock ((cmd_BB_gen c nil BBnow BBnum).(BBn) :: nil) (cmd_BB_gen c BBs BBnow BBnum).(BasicBlocks) (BBs ++ (cmd_BB_gen c nil BBnow BBnum).(BasicBlocks)).
  rewrite <- app_assoc in H2. pose proof H2 H0. rewrite H3. rewrite H. tauto.
Qed.

Lemma list_cmd_BB_delta:
  forall (cmds: list cmd)(BBs BBwo_last: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat),
(list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(BasicBlocks) = BBwo_last -> (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BasicBlocks) = BBs ++ BBwo_last.
Proof.
  intros. pose proof add_BBs_in_generation_reserves_BB cmds BBs BBnow BBnum.
  unfold to_result in H0.
  pose proof eq_BBn_list BBs nil BBnow BBnum cmds. rewrite H1 in H0.
  pose proof cut_eq_part_list_r BasicBlock ((list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(BBn) :: nil) (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BasicBlocks) (BBs ++ (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow BBnum).(BasicBlocks)).
  rewrite <- app_assoc in H2. pose proof H2 H0. rewrite H3. rewrite H. tauto.
Qed.


Lemma length_eq : forall (A : Type) (xs ys : list A),
  xs = ys -> length xs = length ys.
Proof.
  intros A xs ys H.
  rewrite H.
  reflexivity.
Qed.


Lemma tl_In_sublist_then_in_list_head:
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (x: BasicBlock),
    In x (tl BBs) -> In x (tl (BBs ++ BBnow :: nil)).
Proof.
  intros. induction BBs.
  - unfold In in H. tauto.
  - simpl. unfold tl in H.
    apply In_sublist_then_in_list_head. apply H.
Qed.



Lemma hd_equality:
  forall (x: BasicBlock) (tl: list BasicBlock) (BBs: list BasicBlock),  
    BBs = x :: tl -> x = hd empty_block BBs.
Proof.
  intros. destruct BBs.
  - apply nil_cons in H. tauto.
  - simpl. apply head_eq_prop in H. rewrite H. tauto.
Qed.


(*Start: Main for range =============================================================================================================================================================================================*)

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
  rename H2 into BBnow_lt_startnum.
  unfold to_result in BBs_eq.
  set(then_start_num := S (S (S startnum))). (* S BBnextnum *)
  set(BB_then_now := {|
      block_num := S startnum;
      commands := nil;
      jump_info := {|
        jump_kind := UJump;
        jump_condition := None; 
        jump_dest_1 := startnum; (* BBnextnum*)
        jump_dest_2 := None |} ;
      |}).

  set(then_res := (list_cmd_BB_gen cmd_BB_gen c1 nil BB_then_now then_start_num)).
  set(then_delta := (then_res).(BasicBlocks) ++ (then_res).(BBn)::nil).
  set(then_end_num := (then_res).(next_block_num)).
  
  set(BB_else_now := {|
  block_num := S(S startnum);
  commands := nil;
  jump_info := {|
    jump_kind := UJump;
    jump_condition := None; 
    jump_dest_1 := (startnum); (* BBnextnum*)
    jump_dest_2 := None |} ;
  |}).
  set(else_res := (list_cmd_BB_gen cmd_BB_gen c2 nil BB_else_now then_end_num)).
  set(else_delta := (else_res).(BasicBlocks) ++ (else_res).(BBn)::nil).
  set(else_end_num := (else_res).(next_block_num)).
  set(BB_next := {|
    block_num := (startnum);
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
          jump_dest_1 := S startnum;
          jump_dest_2 := Some (S (S startnum));
          jump_condition := Some e
        |}
      |}
  ).
  
  specialize (c1_prop then_start_num then_end_num BBs BB_then_now then_delta).
  assert (c1_aux1 : (BB_then_now.(jump_info).(jump_kind) = UJump /\ BB_then_now.(jump_info).(jump_dest_2) = None) ). tauto.

  assert (c1_aux2 : then_end_num = (list_cmd_BB_gen cmd_BB_gen c1 BBs BB_then_now then_start_num).(next_block_num)). subst then_end_num. subst then_res. pose proof add_BBs_in_generation_retains_next_block_num c1 BBs BB_then_now then_start_num. apply H.

  assert (c1_aux3 : (to_result (list_cmd_BB_gen cmd_BB_gen c1 BBs BB_then_now then_start_num) = BBs ++ then_delta)). pose proof add_BBs_in_generation_reserves_BB c1 BBs BB_then_now then_start_num. unfold to_result in H. unfold to_result. subst then_delta. subst then_res. apply H. 

  assert (c1_aux4: (BB_then_now.(block_num) < then_start_num)%nat). {
    subst BB_then_now. simpl. lia.
  }

  specialize (c1_prop c1_aux1 c1_aux2 c1_aux3 c1_aux4).
  clear c1_aux1 c1_aux2 c1_aux3 c1_aux4.
  
  specialize (c2_prop then_end_num endnum nil BB_else_now else_delta).
  assert (c2_aux1 : (BB_else_now.(jump_info).(jump_kind) = UJump /\ BB_else_now.(jump_info).(jump_dest_2) = None)). tauto.

  assert (c2_aux2 : endnum = (list_cmd_BB_gen cmd_BB_gen c2 nil BB_else_now then_end_num).(next_block_num)). {
    pose proof CIf_next_block_num_eq_else_next_block_num e c1 c2 BBs BBnow startnum. subst endnum. tauto.
  }

  assert (c2_aux3 : (to_result (list_cmd_BB_gen cmd_BB_gen c2 nil BB_else_now then_end_num) = else_delta)). subst else_delta. subst else_res. unfold to_result. pose proof add_BBs_in_generation_reserves_BB c2 nil BB_else_now then_end_num. unfold to_result in H. apply H.

  assert (c2_aux4: (BB_else_now.(block_num) < then_end_num)%nat). {
    subst BB_else_now. simpl.
    pose proof bbnum_le_next_num nil BB_then_now then_start_num c1.
    assert((BB_then_now.(block_num) < then_start_num)%nat). {
      subst BB_then_now. simpl. lia.
    }
    specialize (H H0). subst then_res. lia.
  } 
  specialize (c2_prop c2_aux1 c2_aux2 c2_aux3 c2_aux4).
  clear c2_aux1 c2_aux3 c2_aux4.

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
         block_num := S startnum;
         commands := nil;
         jump_info :=
           {|
             jump_kind := UJump;
             jump_dest_1 := startnum;
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
         block_num := S (S startnum);
         commands := nil;
         jump_info :=
           {|
             jump_kind := UJump;
             jump_dest_1 := startnum;
             jump_dest_2 := None;
             jump_condition := None
           |}
       |}
       (list_cmd_BB_gen cmd_BB_gen c1 nil
          {|
            block_num := S startnum;
            commands := nil;
            jump_info :=
              {|
                jump_kind := UJump;
                jump_dest_1 := startnum;
                jump_dest_2 := None;
                jump_condition := None
              |}
          |} (S (S (S startnum)))).(next_block_num)) = else_delta).
    {
      assert (then_res_p: (list_cmd_BB_gen cmd_BB_gen c1 nil
      {|
        block_num := S startnum;
        commands := nil;
        jump_info :=
          {|
            jump_kind := UJump;
            jump_dest_1 := startnum;
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
       block_num := S startnum;
       commands := nil;
       jump_info :=
         {|
           jump_kind := UJump;
           jump_dest_1 := startnum;
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
       block_num := S (S startnum);
       commands := nil;
       jump_info :=
         {|
           jump_kind := UJump;
           jump_dest_1 := startnum;
           jump_dest_2 := None;
           jump_condition := None
         |}
     |}
     (list_cmd_BB_gen cmd_BB_gen c1 nil
        {|
          block_num := S startnum;
          commands := nil;
          jump_info :=
            {|
              jump_kind := UJump;
              jump_dest_1 := startnum;
              jump_dest_2 := None;
              jump_condition := None
            |}
        |} (S (S (S startnum)))).(next_block_num)) = else_delta).
  {
    assert (then_res_p: (list_cmd_BB_gen cmd_BB_gen c1 nil
    {|
      block_num := S startnum;
      commands := nil;
      jump_info :=
        {|
          jump_kind := UJump;
          jump_dest_1 := startnum;
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
  BBnum_set (tl BBdelta) ==  BBnum_set then_delta ∪ BBnum_set else_delta ∪ unit_set(startnum)
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
  BBjmp_dest_set BBdelta == unit_set(BBnow.(jump_info).(jump_dest_1)) ∪ BBjmp_dest_set then_delta ∪ BBjmp_dest_set else_delta ∪ unit_set(S startnum) ∪ unit_set(S(S startnum))
  ).
  {
    rewrite eq_delta_prop. split; intros; sets_unfold.
    - destruct H as [x_ [cond1 cond2]].
      simpl in cond1. destruct cond1 as [head | tail].
      * destruct cond2.
        ** left. right. unfold unit_set. rewrite <- head in H. simpl in H. lia.
        ** right. unfold unit_set. rewrite <- head in H. subst BBnow'. cbn [jump_info] in H. simpl in H. 
           pose proof option_eq_some nat (S (S startnum)) (a) as key.
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

  assert (else_prop: (exists n, BBnum_set (tl else_delta) n) -> le then_end_num endnum).
  {
    intros. destruct H as [n H]. unfold all_lt in c2_prop2. unfold all_ge in c2_prop1.
    specialize (c2_prop2 n H). specialize (c2_prop1 n H). lia.
  }
  assert (then_prop: (exists n, BBnum_set (tl then_delta) n) -> lt startnum then_end_num).
  {
    intros. destruct H as [n H]. unfold all_lt in c1_prop2. unfold all_ge in c1_prop1.
    specialize (c1_prop2 n H). specialize (c1_prop1 n H). lia.
  }

(*BBnow < startnum = BBthennum < BBelsenum < BBnextnum < then_end_num <= else_endnum = endnum ============================================================================*)
  assert (le_chain1: lt BBnow.(block_num) startnum). tauto.

  assert (le_chain2: le then_start_num then_end_num). {
    pose proof bbnum_le_next_num nil BB_then_now then_start_num c1.
    assert (pre: (BB_then_now.(block_num) < then_start_num)%nat). {
      unfold then_start_num. subst BB_then_now. cbn [block_num]. lia.
    }
    specialize (H pre). subst then_end_num. subst then_res. simpl. lia.
  }
  

  assert (le_chain3: lt (S (S startnum)) then_end_num). lia.

  assert (le_chain4: le then_end_num endnum).
  {
    pose proof bbnum_le_next_num nil BB_else_now then_end_num c2.
    assert (pre: (BB_else_now.(block_num) < then_end_num)%nat). {
      unfold then_end_num. subst BB_else_now. cbn [block_num]. lia.
    }
    specialize (H pre). 
    assert (tricky_eq: endnum = else_end_num). {
    tauto.
    }
    rewrite tricky_eq. subst else_end_num. subst else_res. simpl. lia.
  }

  assert (le_chain: lt BBnow.(block_num) startnum /\ le then_end_num endnum /\ lt startnum then_end_num /\ lt (S (S startnum)) endnum).
  {
    repeat split.
    - tauto.
    - lia.
    - lia.
    - lia.
  }

  clear le_chain1 le_chain2 le_chain3 le_chain4.


  repeat split.
  (*branch 1: 证明去掉头部的number后， BBdelta的所有num都大于等于startnum*)
  sets_unfold in separate_delta_num. 
  - unfold all_ge. intros. rename H into A. unfold BBnum_set in A. destruct A as [BB A]. destruct A as [A1 A2].
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
      unfold all_ge in c1_prop1. 
      specialize (c1_prop1 n).
      pose proof In_head_or_body BasicBlock x empty_block then_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2.  rewrite head_then in cond2. rewrite <- cond2. subst BB_then_now. cbn [block_num]. lia.
      ** assert(temp: BBnum_set (tl then_delta) n).
          {
            unfold BBnum_set. exists x. split. tauto. tauto.
          }
          specialize (c1_prop1 temp). lia.
          
    + destruct case2 as [x [cond1 cond2]].
      unfold all_ge in c2_prop1. specialize (c2_prop1 n).
      pose proof In_head_or_body BasicBlock x empty_block else_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2. rewrite head_else in cond2. rewrite <- cond2. subst BB_else_now. cbn [block_num]. lia. (*使用 c1_prop2*)
      ** assert(temp: BBnum_set (tl else_delta) n).
          {
            unfold BBnum_set. exists x. split. tauto. tauto.
          }
          specialize (c2_prop1 temp). 
          *** lia. (* c2_prop1和c1_prop2 *)
    + lia.
  (*branch 2: 证明去掉头部的number后， BBdelta的所有num都小于endnum*) 
  - unfold all_lt. intros. sets_unfold in separate_delta_num.
    unfold unit_set in separate_delta_num.
    specialize (separate_delta_num n). destruct separate_delta_num as [separate_delta_num _].
    specialize (separate_delta_num H). clear H.
    destruct separate_delta_num as [[case1 | case2] | case3].
    + destruct case1 as [x [cond1 cond2]].
      unfold all_lt in c1_prop2. specialize (c1_prop2 n).
      (*如果一个元素在一个列表里，它要么是这个列表的第一个，要么就在后续部分里*)
      pose proof In_head_or_body BasicBlock x empty_block then_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2. rewrite head_then in cond2. rewrite <- cond2. subst BB_then_now. cbn [block_num]. lia.
      ** assert(temp: BBnum_set (tl then_delta) n).
          {
            unfold BBnum_set. exists x. split. tauto. tauto.
          }
          specialize (c1_prop2 temp). lia.
    + destruct case2 as [x [cond1 cond2]].
      unfold all_lt in c2_prop2. specialize (c2_prop2 n).
      pose proof In_head_or_body BasicBlock x empty_block else_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2. rewrite head_else in cond2. rewrite <- cond2. subst BB_else_now. cbn [block_num]. lia.
      ** assert(temp: BBnum_set (tl else_delta) n).
          {
            unfold BBnum_set. exists x. split. tauto. tauto.
          }
          specialize (c2_prop2 temp). lia.
    + lia.
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
Qed.

Lemma Q_while_BBgen_range:
forall (e: expr) (c1 c2: list cmd),

    P_BBgen_range cmd_BB_gen c1 ->
    P_BBgen_range cmd_BB_gen c2 ->

    Q_BBgen_range (CWhile c1 e c2).
Proof.
Admitted. (*DONT CARE ABOUT WHILE*)

(*这个肯定成立，没有新的block*)
Lemma Q_asgn_BBgen_range:
forall  (x: var_name) (e: expr),
    Q_BBgen_range (CAsgn x e).
Proof. 
  intros. unfold Q_BBgen_range. intros. simpl in H0.
  unfold to_result in H1. simpl in H1. apply cut_eq_part_list_l in H1. rename H2 into BBnum_lt_startnum.
  repeat split.
  - unfold all_ge. intros. unfold BBnum_set in H2. destruct H2 as [? [? ?]]. 
    rewrite <- H1 in H2. unfold tl in H2. unfold In in H2. tauto.
  - unfold all_lt. intros. unfold BBnum_set in H2. destruct H2 as [? [? ?]]. 
    rewrite <- H1 in H2. unfold tl in H2. unfold In in H2. tauto.
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

Lemma P_BBgen_nil:
    P_BBgen_range cmd_BB_gen nil.
Proof.
  unfold P_BBgen_range. intros. simpl in H0. unfold to_result in H1. simpl in H1. rename H2 into new. 
  pose proof cut_eq_part_list_l BasicBlock BBs (BBnow::nil) BBdelta H1. 
  repeat split.
  - rewrite <- H2. simpl. unfold all_ge. intros. unfold BBnum_set in H3. destruct H3 as [BB [H3 H4]]. simpl in H3. tauto.
  - rewrite <- H2. simpl. unfold all_lt. intros. unfold BBnum_set in H3. destruct H3 as [BB [H3 H4]]. simpl in H3. tauto.
  - rewrite <- H2. simpl. unfold BBjmp_dest_set. sets_unfold. intros. destruct H3 as [BB [H3 H4]]. simpl in H3.
    destruct H3 as [H3 | H3].
    + right.  unfold unit_set. subst BBdelta.
      destruct H4.
      -- rewrite <- H2. rewrite H3 in *. reflexivity.
      -- destruct H as [c1 c2]. rewrite <- H3 in H2. rewrite c2 in H2. discriminate H2.
    + tauto.
Qed.
Lemma P_BBgen_con:
    forall (c: cmd) (cmds: list cmd),
    Q_BBgen_range c ->
    P_BBgen_range cmd_BB_gen cmds ->
    P_BBgen_range cmd_BB_gen (c::cmds).
Proof.
  intros.
  unfold P_BBgen_range in H0.
  unfold Q_BBgen_range in H.
  unfold P_BBgen_range.
  intros.
  rename H4 into lt_prop.
  set (endnum' := (cmd_BB_gen c BBs BBnow startnum).(next_block_num)).
  set (BBwo_last' := (cmd_BB_gen c nil BBnow startnum).(BasicBlocks)).
  set (BBnow' := (cmd_BB_gen c BBs BBnow startnum).(BBn)).
  set (BBdelta' := BBwo_last' ++ BBnow'::nil).
  assert((cmd_BB_gen c BBs BBnow startnum).(BasicBlocks) = BBs ++ BBwo_last').
  {
    pose proof cmd_BB_delta c BBs BBwo_last' BBnow startnum. apply H4. tauto.
  }
    assert(to_result(cmd_BB_gen c BBs BBnow startnum) = BBs ++ BBdelta').
  {
    subst BBdelta'.
    pose proof cmd_BB_delta c BBs BBwo_last' BBnow startnum. 
    unfold to_result. rewrite H5. subst BBnow'. rewrite <- app_assoc. reflexivity. tauto.
  }
  specialize (H startnum endnum' BBs BBnow BBdelta' H1). destruct H. tauto. tauto. tauto.
  set (BBwo_last'' := (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow' endnum').(BasicBlocks)).
  set (BBnow'' := (list_cmd_BB_gen cmd_BB_gen cmds (BBs++BBwo_last') BBnow' endnum').(BBn)).
  set (BBdelta'' := BBwo_last'' ++ BBnow''::nil).
  specialize (H0 endnum' endnum (BBs++BBwo_last') BBnow' BBdelta'').
  assert(jump_kind BBnow'.(jump_info) = UJump /\ jump_dest_2 BBnow'.(jump_info) = None).
  {
    pose proof JmpInfo_inherit BBs BBnow startnum c. subst BBnow'. rewrite H7. tauto.
  }
  assert(endnum = (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBwo_last') BBnow' endnum').(next_block_num)).
  {
    cbn[list_cmd_BB_gen] in H2. subst endnum' BBnow'. rewrite H2. 
    rewrite <- H4. reflexivity.
  }
  assert((list_cmd_BB_gen cmd_BB_gen cmds nil BBnow' endnum').(BasicBlocks) = BBwo_last'').
  {
    tauto.
  }
  assert(to_result (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBwo_last') BBnow' endnum') = (BBs ++ BBwo_last') ++ BBdelta'').
  {
    subst BBdelta''.
    pose proof list_cmd_BB_delta cmds (BBs++BBwo_last') BBwo_last'' BBnow' endnum'.
    unfold to_result.
    specialize (H10 H9).
    rewrite H10.
    subst BBnow''.
    rewrite app_assoc.
    reflexivity.
  }
  assert((BBnow'.(block_num) < endnum')%nat).
  {
    pose proof inherit_lt_num_prop BBs BBnow startnum c lt_prop. 
    subst BBnow'.
    subst endnum'. tauto.
  }
  specialize (H0 H7 H8 H10 H11). 
  assert((list_cmd_BB_gen cmd_BB_gen (c :: cmds) BBs BBnow startnum).(BasicBlocks) =BBs ++ BBwo_last' ++ BBwo_last'').
  {
    cbn[list_cmd_BB_gen]. rewrite H4. subst endnum'. subst BBnow'.
    pose proof list_cmd_BB_delta cmds (BBs++BBwo_last') BBwo_last'' ((cmd_BB_gen c BBs BBnow startnum).(BBn)) ((cmd_BB_gen c BBs BBnow startnum).(next_block_num)) H9.
    rewrite app_assoc. tauto.
  }
    assert((list_cmd_BB_gen cmd_BB_gen (c :: cmds) BBs BBnow startnum).(BBn) = BBnow'').
  {
    cbn[list_cmd_BB_gen]. rewrite H4. subst endnum'. subst BBnow'.
    tauto.
  }
    assert((list_cmd_BB_gen cmd_BB_gen (c :: cmds) BBs BBnow startnum).(next_block_num) = endnum).
  {
    cbn[list_cmd_BB_gen]. rewrite H4. subst endnum'. subst BBnow'.
    rewrite H8. tauto.
  }
  (* properties on delta, wo_last and now*)
    assert(BBdelta = BBwo_last' ++ BBdelta'').
  {
    assert(BBs ++ BBwo_last' ++ BBwo_last'' ++ BBnow''::nil = BBs ++ BBdelta).
    unfold to_result in H3.
    rewrite <- H3. rewrite app_assoc. rewrite app_assoc. rewrite app_assoc in H12.
    rewrite <- H12.
    rewrite <- H13.
    tauto.
    apply app_inv_head in H15.
    subst BBdelta''. rewrite H15. tauto.
  }
  split.
  + rewrite H15.
    destruct H0.
     assert((endnum' >= startnum)%nat).
  {
    subst endnum'.
    pose proof bbnum_le_next_num_single_cmd BBs BBnow startnum c lt_prop. lia.
  }
    destruct c.
   * simpl in BBwo_last'. subst BBwo_last'. simpl.
      unfold all_ge. intros. unfold all_ge in H. specialize (H0 n H18). lia.
   *
    assert(all_ge (BBnum_set (tl(BBwo_last'))) startnum).
  {
    clear H17 H15 H14 H13 H12 H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H16 H0 BBdelta'' BBnow'' BBwo_last'' endnum.
    unfold all_ge. intros. unfold all_ge in H. specialize (H n).
    assert (BBnum_set (tl BBdelta') n). {
      subst BBdelta'. unfold BBnum_set in H0. destruct H0 as [? [? ?]].
      unfold BBnum_set. exists x.
      pose proof tl_In_sublist_then_in_list_head BBwo_last' BBnow' x H0. split.
      apply H2. apply H1.
    }
    apply H. apply H1.
  }
    assert(all_ge (BBnum_set (tl BBdelta'')) startnum).
    {
      unfold all_ge. intros. unfold all_ge in H0. specialize(H0 n H19). lia.
    }
    destruct BBwo_last' eqn:?.
    - simpl. unfold all_ge. unfold all_ge in H19. intros. rename H20 into a1. specialize (H19 n).

      specialize (H19 a1). lia. 
    - simpl. simpl in H18.
      unfold all_ge. intros. rename H20 into key. unfold BBnum_set in key. destruct key as [? [k1 k2]].
      apply in_app_iff in k1. destruct k1.
      -- unfold all_ge in H18. specialize (H18 n). assert( pre: BBnum_set l n ). {
        unfold BBnum_set. exists x. split. tauto. tauto.
        }
        specialize (H18 pre). lia.
      -- subst BBdelta''. destruct BBwo_last''. 
          ++ simpl in H20. destruct H20. 
          rewrite <- H20 in k2.
          rewrite <- k2.
          pose proof if_BBn_num_prop e c1 c2 BBs BBnow startnum. 
          pose proof bbnow_num_le_bbn_num (BBs ++ b :: l) BBnow' endnum' cmds H11.
          tauto.
          tauto.
          ++ 
          assert(b0.(block_num) = BBnow'.(block_num)). 
          {
             pose proof BBgen_head_prop_wo cmds BBnow' endnum'.
             simpl in H21.
             rewrite H9 in H21.
             assert (nil <> b0 :: BBwo_last''). apply nil_cons.
             assert (b0 :: BBwo_last'' <> nil). {
                unfold not. intros. unfold not in H22. apply H22.
                rewrite H23. tauto.
             }
             pose proof H21 H23. unfold hd in H24. unfold BBnow'.
             pose proof if_BBn_num_prop e c1 c2 BBs BBnow.
             specialize (H25 startnum). rewrite H25. apply H24.
          }
          simpl in H0. destruct H20.
          rewrite <- H20 in k2.
          rewrite H21 in k2.
          pose proof if_BBn_num_prop e c1 c2 BBs BBnow startnum.
          subst BBnow'. rewrite <- k2. lia. 
          unfold all_ge in H0. specialize (H0 n). unfold BBnum_set in H0.
          assert((exists BB : BasicBlock, In BB (BBwo_last'' ++ BBnow'' :: nil) /\ BB.(block_num) = n)).
          {
          exists x. tauto. 
          }
          specialize (H0 H22). lia.

  * admit. (* DONT CARE ABOUT WHILE *)
  + split. 
  - rewrite H15. destruct H0. destruct H16.
  assert((endnum' <= endnum)%nat).
  {
    cbn[list_cmd_BB_gen] in H14.
    pose proof bbnum_le_next_num (cmd_BB_gen c BBs BBnow startnum).(BasicBlocks) (cmd_BB_gen c BBs BBnow startnum).(BBn) (cmd_BB_gen c BBs BBnow startnum).(next_block_num) cmds.
    assert ((((cmd_BB_gen c BBs BBnow startnum).(BBn)).(block_num) <
       (cmd_BB_gen c BBs BBnow startnum).(next_block_num))%nat). {
      apply H11.
    }
    pose proof H18 H19 as H18. clear H19.
    lia.
  }
    assert(all_lt (BBnum_set (tl BBwo_last')) endnum).
  {
    clear H15 H14 H13 H12 H11 H10 H9 H8 H7 H5 H4 lt_prop H3 H2 H1 H17 H16 H0.
    destruct H6. subst BBdelta'. destruct BBwo_last'.
    simpl. unfold BBnum_set. simpl. unfold all_lt. intros. destruct H2. tauto. 
    simpl. simpl in H0. unfold all_lt in H0.
    unfold all_lt. intros. specialize (H0 n). 
    assert(BBnum_set (BBwo_last' ++ BBnow' :: nil) n). unfold BBnum_set.
    unfold BBnum_set in H2. destruct H2. destruct H2. exists x.
    split. apply in_app_iff. left. tauto. tauto. specialize(H0 H3). lia.
  }
  assert(all_lt (BBnum_set (BBdelta'')) endnum).
  {
    clear H15 H14 H13 H12 H10 H9 H8 H7 H6 H H5 H4 H3 H2 H1 H0.
  destruct BBdelta'' eqn:?.
 - unfold all_lt. intros. unfold BBnum_set in H. destruct H. simpl in H. tauto. 
 - unfold tl in H16. unfold all_lt. intros. unfold all_lt in H16. specialize (H16 n).
   unfold BBnum_set in H. destruct H as [? [? ?]]. unfold In in H. destruct H as [? | ?].
   + pose proof BBgen_head_prop cmds BBnow' endnum'. simpl in H1.
     assert (b = hd empty_block BBdelta''). {
       pose proof hd_equality b l BBdelta'' Heql. apply H2.
     }
     subst BBdelta''. subst BBwo_last''. subst BBnow''.
     pose proof eq_BBn_list (BBs ++ BBwo_last') nil BBnow' endnum' cmds.
     rewrite H3 in H2. rewrite <- H2 in H1.
     rewrite <- H0. rewrite <- H. rewrite H1.
     lia.
   + unfold BBnum_set in H16. assert (Nat.lt n endnum). {
       apply H16. exists x. split. apply H. apply H0.
     }
     lia.
}
 clear H18 H17 H16 H15 H14 H13 H12 H11 H10 H9 H8 H7 H5 H4 lt_prop H3 H2 H1 H0.
 unfold all_lt. intros. unfold BBnum_set in H0. destruct H0. destruct H0.
 destruct BBwo_last'.
 -- 
 simpl in H0.
 assert(In x BBdelta''). 
 {
 destruct BBdelta''. simpl in H0. tauto. simpl in H0.
 apply in_cons. tauto.
 }
 unfold all_lt in H20. specialize (H20 n).
 assert(BBnum_set BBdelta'' n).
 {
  unfold BBnum_set. exists x. tauto.
 }
 specialize (H20 H3). tauto.
-- simpl in H0. apply in_app_iff in H0. destruct H0.
 simpl in H19. unfold all_lt in H19. specialize (H19 n). unfold BBnum_set in H19.
 assert (exists BB : BasicBlock, In BB BBwo_last' /\ BB.(block_num) = n).
 exists x. tauto. specialize (H19 H2). tauto.
 simpl in H20. unfold all_lt in H20. specialize (H20 n). unfold BBnum_set in H20.
 assert (exists BB : BasicBlock, In BB BBdelta'' /\ BB.(block_num) = n).
 exists x. tauto. specialize (H20 H2). tauto.
     - rewrite H15. 
      assert(BBjmp_dest_set BBwo_last' ⊆ section startnum endnum ∪ unit_set (jump_dest_1 BBnow.(jump_info))).
     {
        destruct H6. sets_unfold. intros. sets_unfold in H16. pose proof H16 a. destruct H18.
        ++
        subst BBdelta'. unfold BBjmp_dest_set. unfold BBjmp_dest_set in H17. destruct H17.
        exists x. destruct H17. split. apply in_app_iff. left. tauto. tauto.
        ++ left. unfold section. unfold section in H18. destruct H18.
        assert((endnum' <= endnum)%nat).
       {
          cbn[list_cmd_BB_gen] in H14.
          pose proof bbnum_le_next_num (cmd_BB_gen c BBs BBnow startnum).(BasicBlocks) (cmd_BB_gen c BBs BBnow startnum).(BBn) (cmd_BB_gen c BBs BBnow startnum).(next_block_num) cmds.
          assert ((((cmd_BB_gen c BBs BBnow startnum).(BBn)).(block_num) <
       (cmd_BB_gen c BBs BBnow startnum).(next_block_num))%nat). {
         apply H11.
          }
        pose proof H20 H21 as H20. clear H21.
        lia.
        }
        split. tauto. lia.
        ++ right. tauto.
     }
      assert(BBjmp_dest_set (BBdelta'') ⊆ section startnum endnum ∪ unit_set (jump_dest_1 BBnow.(jump_info))).
     {
        subst BBdelta. destruct H0. destruct H15. sets_unfold. intros. sets_unfold in H17. specialize (H17 a). destruct H17.
        tauto.
        left.
        assert((endnum'>=startnum)%nat).
       {
          pose proof bbnum_le_next_num_single_cmd BBs BBnow startnum c lt_prop. lia. (*copy the proof in the first +*)
       }
        unfold section. split. unfold section in H17. lia. unfold section in H17. tauto.
        pose proof JmpInfo_inherit BBs BBnow startnum c.
        right. subst BBnow'. rewrite H19 in H17. tauto.
     }
      sets_unfold. intros. sets_unfold in H16. sets_unfold in H17. specialize (H16 a). specialize (H17 a).
      unfold BBjmp_dest_set in H18. destruct H18. destruct H18. apply in_app_iff in H18.
      destruct H18. destruct H16. unfold BBjmp_dest_set. exists x. tauto.
      left. tauto. right. tauto. 
      destruct H17. unfold BBjmp_dest_set. exists x. tauto.
      left. tauto. right. tauto. 
Admitted. (* QED *)


Section BB_gen_range_sound.


Variable BB_gen_range_soundness: forall (c: cmd), Q_BBgen_range c.

Fixpoint BBgen_list_range_soundness (cmds: list cmd): P_BBgen_range cmd_BB_gen cmds :=
  match cmds with
  | nil => P_BBgen_nil 
  | c :: cmds0 => P_BBgen_con c cmds0 (BB_gen_range_soundness c) (BBgen_list_range_soundness cmds0)
  end.

End BB_gen_range_sound.

Fixpoint BB_gen_range_soundness (c: cmd): Q_BBgen_range c :=
  match c with
  | CAsgn x e => Q_asgn_BBgen_range x e
  | CIf e cmds1 cmds2 =>
      Q_if_BBgen_range e cmds1 cmds2
        (BBgen_list_range_soundness BB_gen_range_soundness cmds1)
        (BBgen_list_range_soundness BB_gen_range_soundness cmds2)
  | CWhile cmds1 e cmds2 =>
      Q_while_BBgen_range e cmds1 cmds2
        (BBgen_list_range_soundness BB_gen_range_soundness cmds1)
        (BBgen_list_range_soundness BB_gen_range_soundness cmds2)
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

(* Main range without last ==================== *)

Lemma Q_if_BBgen_range_wo:
forall (e: expr) (c1 c2: list cmd),
    P_BBgen_range_wo cmd_BB_gen c1  ->
    P_BBgen_range_wo cmd_BB_gen c2  ->
    Q_BBgen_range_wo (CIf e c1 c2).
Proof.
  intros.
  rename H into c1_prop.
  rename H0 into c2_prop.
  unfold P_BBgen_range_wo in c1_prop.
  unfold P_BBgen_range_wo in c2_prop.
  unfold Q_BBgen_range_wo.
  intros.
  rename H into BBnow_jump_kind.
  rename H0 into endnum_eq.
  rename H1 into BBs_eq.
  rename H2 into BBnow_lt_startnum.
  unfold to_result in BBs_eq.
  set(then_start_num := S (S (S startnum))). (* S BBnextnum *)
  set(BB_then_now := {|
      block_num := S startnum;
      commands := nil;
      jump_info := {|
        jump_kind := UJump;
        jump_condition := None; 
        jump_dest_1 := startnum; (* BBnextnum*)
        jump_dest_2 := None |} ;
      |}).

  set(then_res := (list_cmd_BB_gen cmd_BB_gen c1 nil BB_then_now then_start_num)).
  set(then_delta := (then_res).(BasicBlocks)).
  set(then_end_num := (then_res).(next_block_num)).
  
  set(BB_else_now := {|
  block_num := S(S startnum);
  commands := nil;
  jump_info := {|
    jump_kind := UJump;
    jump_condition := None; 
    jump_dest_1 := (startnum); (* BBnextnum*)
    jump_dest_2 := None |} ;
  |}).
  set(else_res := (list_cmd_BB_gen cmd_BB_gen c2 nil BB_else_now then_end_num)).
  set(else_delta := (else_res).(BasicBlocks)).
  set(else_end_num := (else_res).(next_block_num)).
  set(BB_next := {|
    block_num := (startnum);
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
          jump_dest_1 := S startnum;
          jump_dest_2 := Some (S (S startnum));
          jump_condition := Some e
        |}
      |}
  ).
  
  specialize (c1_prop then_start_num then_end_num BBs BB_then_now then_delta).
  assert (c1_aux1 : (BB_then_now.(jump_info).(jump_kind) = UJump /\ BB_then_now.(jump_info).(jump_dest_2) = None) ). tauto.

  assert (c1_aux2 : then_end_num = (list_cmd_BB_gen cmd_BB_gen c1 BBs BB_then_now then_start_num).(next_block_num)). subst then_end_num. subst then_res. 
  pose proof add_BBs_in_generation_retains_next_block_num c1 BBs BB_then_now then_start_num. apply H.

  assert (c1_aux3 : ( (list_cmd_BB_gen cmd_BB_gen c1 BBs BB_then_now then_start_num).(BasicBlocks) = BBs ++ then_delta)).
  pose proof add_BBs_in_generation_reserves_BB_wo c1 BBs BB_then_now then_start_num. unfold to_result in H. unfold to_result. subst then_delta. subst then_res. apply H. 

  assert (c1_aux4: (BB_then_now.(block_num) < then_start_num)%nat). {
    subst BB_then_now. simpl. lia.
  }

  specialize (c1_prop c1_aux1 c1_aux2 c1_aux3 c1_aux4).
  clear c1_aux1 c1_aux2 c1_aux3 c1_aux4.
  
  specialize (c2_prop then_end_num endnum nil BB_else_now else_delta).
  assert (c2_aux1 : (BB_else_now.(jump_info).(jump_kind) = UJump /\ BB_else_now.(jump_info).(jump_dest_2) = None)). tauto.

  assert (c2_aux2 : endnum = (list_cmd_BB_gen cmd_BB_gen c2 nil BB_else_now then_end_num).(next_block_num)). {
    pose proof CIf_next_block_num_eq_else_next_block_num e c1 c2 BBs BBnow startnum. subst endnum. tauto.
  }

  assert (c2_aux3 : ((list_cmd_BB_gen cmd_BB_gen c2 nil BB_else_now then_end_num).(BasicBlocks) = else_delta)). subst else_delta. subst else_res. unfold to_result. pose proof add_BBs_in_generation_reserves_BB_wo c2 nil BB_else_now then_end_num. unfold to_result in H. apply H.

  assert (c2_aux4: (BB_else_now.(block_num) < then_end_num)%nat). {
    subst BB_else_now. simpl.
    pose proof bbnum_le_next_num nil BB_then_now then_start_num c1.
    assert((BB_then_now.(block_num) < then_start_num)%nat). {
      subst BB_then_now. simpl. lia.
    }
    specialize (H H0). subst then_res. lia.
  } 
  specialize (c2_prop c2_aux1 c2_aux2 c2_aux3 c2_aux4).
  clear c2_aux1 c2_aux3 c2_aux4.

  destruct c1_prop as [c1_prop1 [c1_prop2 c1_prop3]].
  destruct c2_prop as [c2_prop1 [c2_prop2 c2_prop3]].

  assert (eq_tl_delta_prop: tl BBdelta = then_delta ++ then_res.(BBn)::nil  ++ else_delta ++ else_res.(BBn) :: nil).
  {
    cbn [cmd_BB_gen] in BBs_eq. cbn [BasicBlocks] in BBs_eq. cbn [BBn] in BBs_eq. 
    apply app_inv_head in BBs_eq.
    rewrite <- BBs_eq. simpl. subst BB_next.
    assert (then_eq: to_result
    (list_cmd_BB_gen cmd_BB_gen c1 nil
       {|
         block_num := S startnum;
         commands := nil;
         jump_info :=
           {|
             jump_kind := UJump;
             jump_dest_1 := startnum;
             jump_dest_2 := None;
             jump_condition := None
           |}
       |} (S (S (S startnum)))) = then_delta ++ then_res.(BBn)::nil).
    {
      reflexivity.
    }
    rewrite then_eq. 
    assert (else_eq: to_result
    (list_cmd_BB_gen cmd_BB_gen c2 nil
       {|
         block_num := S (S startnum);
         commands := nil;
         jump_info :=
           {|
             jump_kind := UJump;
             jump_dest_1 := startnum;
             jump_dest_2 := None;
             jump_condition := None
           |}
       |}
       (list_cmd_BB_gen cmd_BB_gen c1 nil
          {|
            block_num := S startnum;
            commands := nil;
            jump_info :=
              {|
                jump_kind := UJump;
                jump_dest_1 := startnum;
                jump_dest_2 := None;
                jump_condition := None
              |}
          |} (S (S (S startnum)))).(next_block_num)) = else_delta ++ else_res.(BBn)::nil).
    {
      assert (then_res_p: (list_cmd_BB_gen cmd_BB_gen c1 nil
      {|
        block_num := S startnum;
        commands := nil;
        jump_info :=
          {|
            jump_kind := UJump;
            jump_dest_1 := startnum;
            jump_dest_2 := None;
            jump_condition := None
          |}
      |} (S (S (S startnum)))) = then_res). reflexivity. rewrite then_res_p.
      reflexivity.
      }
    rewrite else_eq. simpl. rewrite app_assoc_reverse. simpl. reflexivity.  
  }

  assert (eq_delta_prop: BBdelta = BBnow' :: then_delta ++ then_res.(BBn)::nil ++ else_delta ++ else_res.(BBn)::nil).
  {
  cbn [cmd_BB_gen] in BBs_eq. cbn [BasicBlocks] in BBs_eq. cbn [BBn] in BBs_eq. 
  apply app_inv_head in BBs_eq.
  rewrite <- BBs_eq. simpl. subst BB_next. 
  assert (then_eq: to_result
  (list_cmd_BB_gen cmd_BB_gen c1 nil
     {|
       block_num := S startnum;
       commands := nil;
       jump_info :=
         {|
           jump_kind := UJump;
           jump_dest_1 := startnum;
           jump_dest_2 := None;
           jump_condition := None
         |}
     |} (S (S (S startnum)))) = then_delta ++ then_res.(BBn) :: nil).
  {
    reflexivity.
  }
  rewrite then_eq. 
  assert (else_eq: to_result
  (list_cmd_BB_gen cmd_BB_gen c2 nil
     {|
       block_num := S (S startnum);
       commands := nil;
       jump_info :=
         {|
           jump_kind := UJump;
           jump_dest_1 := startnum;
           jump_dest_2 := None;
           jump_condition := None
         |}
     |}
     (list_cmd_BB_gen cmd_BB_gen c1 nil
        {|
          block_num := S startnum;
          commands := nil;
          jump_info :=
            {|
              jump_kind := UJump;
              jump_dest_1 := startnum;
              jump_dest_2 := None;
              jump_condition := None
            |}
        |} (S (S (S startnum)))).(next_block_num)) = else_delta ++ else_res.(BBn) :: nil).
  {
    assert (then_res_p: (list_cmd_BB_gen cmd_BB_gen c1 nil
    {|
      block_num := S startnum;
      commands := nil;
      jump_info :=
        {|
          jump_kind := UJump;
          jump_dest_1 := startnum;
          jump_dest_2 := None;
          jump_condition := None
        |}
    |} (S (S (S startnum)))) = then_res). reflexivity. rewrite then_res_p.
    reflexivity.
    }
  rewrite else_eq. subst BBnow'. simpl. rewrite app_assoc_reverse. simpl. reflexivity.  
  }

  (*拆分BBdelta, 去掉头部的number后， BBdelta里有BBnow的num，还有剩下所有新增的num，其中包括BBthendelta，BBelsedelta*)
  assert (separate_delta_num: 
  BBnum_set (tl BBdelta) ==  BBnum_set (then_delta ++ then_res.(BBn)::nil) ∪ BBnum_set (else_delta ++ else_res.(BBn)::nil)
  ). {
    rewrite eq_tl_delta_prop.
    repeat split; sets_unfold; intros.
    - destruct H as [x_ [cond1 cond2]].
      (* pose proof (In_a_or_b BasicBlock x_ (then_delta ++ else_delta) (BB_next :: nil)). *)
      pose proof (In_a_or_b BasicBlock x_ (then_delta ++then_res.(BBn)::nil)  (else_delta ++ else_res.(BBn)::nil)).
      rewrite app_assoc_reverse in H. simpl in H. specialize (H cond1).
      rename H into H0.
      destruct H0 as [c1__ | c2__].
      * left. unfold BBnum_set. exists x_. split. tauto. tauto.
      * right. unfold BBnum_set. exists x_. split. tauto. tauto. 
    - destruct H as [case1 | case2].
      * unfold BBnum_set in case1. destruct case1 as [x_ [cond1 cond2]].
        unfold BBnum_set. exists x_. split. 
        ** pose proof In_sublist_then_in_list_head BasicBlock x_ (then_delta ++ then_res.(BBn) :: nil) (else_delta ++ else_res.(BBn) :: nil) cond1. rewrite app_assoc_reverse in H. simpl in H. tauto.
        ** tauto.
      * unfold BBnum_set in case2. destruct case2 as [x_ [cond1 cond2]].
        unfold BBnum_set. exists x_. split. 
        ** pose proof In_sublist_then_in_list_last BasicBlock x_ (else_delta ++ else_res.(BBn) :: nil) (then_delta ++ then_res.(BBn) :: nil) cond1. simpl in H. rewrite app_assoc_reverse in H. tauto.
        ** tauto.
  }

  (*拆分BBdelta的jump dest. jumpdest里包含BBthennum和BBelsenum*)
  assert (separate_delta_jump_dest:
  BBjmp_dest_set BBdelta == BBjmp_dest_set (then_delta ++ then_res.(BBn)::nil) ∪ BBjmp_dest_set (else_delta ++ else_res.(BBn)::nil) ∪ unit_set(S startnum) ∪ unit_set(S(S startnum))
  ).
  {
    rewrite eq_delta_prop. split; intros; sets_unfold.
    - destruct H as [x_ [cond1 cond2]].
      simpl in cond1. destruct cond1 as [head | tail].
      * destruct cond2.
        ** left. right. unfold unit_set. rewrite <- head in H. simpl in H. lia.
        ** right. unfold unit_set. rewrite <- head in H. subst BBnow'. cbn [jump_info] in H. simpl in H. 
           pose proof option_eq_some nat (S (S startnum)) (a) as key.
           destruct key as [_ key]. pose proof (key H) as key. lia.
      * pose proof In_a_or_b BasicBlock x_ (then_delta ++ then_res.(BBn)::nil) (else_delta ++ else_res.(BBn)::nil). rewrite app_assoc_reverse in H. simpl in H. specialize (H tail).
        destruct H as [c1_ | c2_].
        ** left. left. left . unfold BBjmp_dest_set. exists x_. split. tauto. tauto.
        ** left. left. right. unfold BBjmp_dest_set. exists x_. split. tauto. tauto.
    - destruct H as [[[case2 | case3] | case4] | case5].
      * unfold BBjmp_dest_set in case2. destruct case2 as [x_ [cond1 cond2]].
        unfold BBjmp_dest_set. exists x_. split. 
        ** pose proof In_sublist_then_in_list_head BasicBlock x_ (then_delta ++ then_res.(BBn) :: nil) (else_delta ++ else_res.(BBn) :: nil) cond1.
           pose proof In_add_one_list BasicBlock x_ BBnow' (then_delta ++ then_res.(BBn)::nil ++ else_delta ++ else_res.(BBn)::nil). rewrite app_assoc_reverse in H. simpl in H. specialize (H0 H). tauto.
        ** tauto.
      * unfold BBjmp_dest_set in case3. destruct case3 as [x_ [cond1 cond2]].
        unfold BBjmp_dest_set. exists x_. split. 
        ** pose proof In_sublist_then_in_list_last BasicBlock x_ (else_delta ++ else_res.(BBn) :: nil) (then_delta ++ then_res.(BBn) :: nil) cond1.
           pose proof In_add_one_list BasicBlock x_ BBnow' (then_delta ++ then_res.(BBn)::nil ++ else_delta ++ else_res.(BBn)::nil). rewrite app_assoc_reverse in H. simpl in H. specialize (H0 H). tauto.
        ** tauto.
      * unfold BBjmp_dest_set. exists BBnow'. split.
        ** simpl. tauto.
        ** unfold unit_set in case4. subst BBnow'. cbn [jump_info]. left. cbn [jump_dest_1]. lia.
      * unfold BBjmp_dest_set. exists BBnow'. split.
        ** simpl. tauto.
        ** unfold unit_set in case5. subst BBnow'. cbn [jump_info]. right. cbn [jump_dest_2]. rewrite case5. reflexivity. 
  }

  assert (head_then: ((then_delta <> nil -> (hd empty_block (then_delta)).(block_num) = BB_then_now.(block_num)))).
  { 
    intros. 
    pose proof BBgen_head_prop_wo c1 BB_then_now then_start_num. rewrite <- H0. reflexivity.
    subst then_delta. subst then_res. simpl. tauto.
  }


  assert (head_else: ((else_delta <> nil -> (hd empty_block (else_delta)).(block_num) = BB_else_now.(block_num)))).
  { 
    intros. 
    pose proof BBgen_head_prop_wo c2 BB_else_now then_end_num. rewrite <- H0. reflexivity.
    subst else_delta. subst else_res. simpl. tauto.
  }

  assert (else_prop: (exists n, BBnum_set (tl else_delta) n) -> lt then_end_num endnum).
  {
    intros. destruct H as [n H]. unfold all_lt in c2_prop2. unfold all_gt in c2_prop1.
    specialize (c2_prop2 n H). specialize (c2_prop1 n H). lia.
  }
  assert (then_prop: (exists n, BBnum_set (tl then_delta) n) -> lt startnum then_end_num).
  {
    intros. destruct H as [n H]. unfold all_lt in c1_prop2. unfold all_gt in c1_prop1.
    specialize (c1_prop2 n H). specialize (c1_prop1 n H). lia.
  }

(*BBnow < startnum = BBthennum < BBelsenum < BBnextnum < then_end_num <= else_endnum = endnum ============================================================================*)
  assert (le_chain1: lt BBnow.(block_num) startnum). tauto.

  assert (le_chain2: le then_start_num then_end_num). {
    pose proof bbnum_le_next_num nil BB_then_now then_start_num c1.
    assert (pre: (BB_then_now.(block_num) < then_start_num)%nat). {
      unfold then_start_num. subst BB_then_now. cbn [block_num]. lia.
    }
    specialize (H pre). subst then_end_num. subst then_res. simpl. lia.
  }
  

  assert (le_chain3: lt (S (S startnum)) then_end_num). lia.

  assert (le_chain4: le then_end_num endnum).
  {
    pose proof bbnum_le_next_num nil BB_else_now then_end_num c2.
    assert (pre: (BB_else_now.(block_num) < then_end_num)%nat). {
      unfold then_end_num. subst BB_else_now. cbn [block_num]. lia.
    }
    specialize (H pre). 
    assert (tricky_eq: endnum = else_end_num). {
    tauto.
    }
    rewrite tricky_eq. subst else_end_num. subst else_res. simpl. lia.
  }

  assert (le_chain: lt BBnow.(block_num) startnum /\ le then_end_num endnum /\ lt startnum then_end_num /\ lt (S (S startnum)) endnum).
  {
    repeat split.
    - tauto.
    - lia.
    - lia.
    - lia.
  }

  clear le_chain1 le_chain2 le_chain3 le_chain4.


  repeat split.
  (*branch 1: 证明去掉头部的number后， BBdelta的所有num都大于startnum*)
  sets_unfold in separate_delta_num. 
  - unfold all_gt. intros. rename H into A. unfold BBnum_set in A. destruct A as [BB A]. destruct A as [A1 A2].
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
    destruct separate_delta_num as [case1 | case2]. 
    + destruct case1 as [x [cond1 cond2]].
      unfold all_gt in c1_prop1. 
      specialize (c1_prop1 n).
      pose proof In_pre_or_tail BasicBlock x then_res.(BBn) then_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2. rewrite <- cond2. 
        pose proof bbnow_num_le_bbn_num nil BB_then_now then_start_num c1.
        assert((BB_then_now.(block_num) < then_start_num)%nat). {
          subst then_start_num. 
          subst BB_then_now. cbn [block_num]. lia.
        }
        specialize (H H0). subst then_res. simpl in H. lia.
      ** pose proof In_head_or_body BasicBlock x empty_block then_delta tail.
        destruct H as [head | body].
        rewrite <- head in head_then.
        destruct then_delta.
        --- simpl in tail. tauto.
        ---
        assert(t: b :: then_delta <> nil). {
          pose proof (nil_cons).
          specialize (H BasicBlock b BBdelta). intros contra.
          rewrite contra in tail. tauto.  
        }
        specialize (head_then t). 
        rewrite head_then in cond2.  subst BB_then_now. simpl in cond2. lia.
        ---
          assert(temp: BBnum_set (tl then_delta) n).
          {
            unfold BBnum_set. exists x. split. tauto. tauto.
          }
          specialize (c1_prop1 temp). lia.
          
    + destruct case2 as [x [cond1 cond2]].
      unfold all_gt in c2_prop1. 
      specialize (c2_prop1 n).
      pose proof In_pre_or_tail BasicBlock x else_res.(BBn) else_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2. rewrite <- cond2. 
      pose proof bbnow_num_le_bbn_num nil BB_else_now then_end_num c2.
      assert((BB_then_now.(block_num) < then_start_num)%nat). {
      subst then_start_num. 
      subst BB_then_now. cbn [block_num]. lia.
      }
      assert((BB_else_now.(block_num) < then_end_num)%nat). {
        subst then_end_num. 
        subst BB_else_now. cbn [block_num]. 
        pose proof bbnum_le_next_num nil BB_then_now then_start_num c1 H0.
        subst then_res. lia.
      }
      specialize (H H1). subst else_res. simpl in H. lia.
      **  pose proof In_head_or_body BasicBlock x empty_block else_delta tail.
          destruct H as [head | body].
          rewrite <- head in head_else.
          destruct else_delta.
          --- simpl in tail. tauto.
          ---
          assert(t: b :: else_delta <> nil). {
            pose proof (nil_cons).
            specialize (H BasicBlock b BBdelta). intros contra.
            rewrite contra in tail. tauto.  
          }
          specialize (head_else t). 
          rewrite head_else in cond2.  subst BB_then_now. simpl in cond2. lia.
          ---
            assert(temp: BBnum_set (tl else_delta) n).
            {
              unfold BBnum_set. exists x. split. tauto. tauto.
            }
            specialize (c2_prop1 temp). lia.

  (*branch 2: 证明去掉头部的number后， BBdelta的所有num都小于endnum*) 
  - unfold all_lt. intros. sets_unfold in separate_delta_num.
    unfold unit_set in separate_delta_num.
    specialize (separate_delta_num n). destruct separate_delta_num as [separate_delta_num _].
    specialize (separate_delta_num H). clear H.
    destruct separate_delta_num as [case1 | case2].
    + destruct case1 as [x [cond1 cond2]].
      unfold all_lt in c1_prop2. specialize (c1_prop2 n).
      (*如果一个元素在一个列表里，它要么是这个列表的第一个，要么就在后续部分里*)
      pose proof In_pre_or_tail BasicBlock x then_res.(BBn) then_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2. rewrite <- cond2.
          assert((BB_then_now.(block_num) < then_start_num)%nat). {
          subst then_start_num. 
          subst BB_then_now. cbn [block_num]. lia.
          }
          
         assert(lt (then_res.(BBn)).(block_num) then_end_num). 
         {
            pose proof inherit_lt_num_prop_list nil BB_then_now then_start_num c1.

            specialize (H0 H). subst then_res. subst then_end_num. simpl in H. lia.
         }

         pose proof bbnum_le_next_num nil BB_else_now then_end_num c2.
          assert((BB_else_now.(block_num) < then_end_num)%nat). {
          subst then_end_num. 
          subst BB_else_now. cbn [block_num]. 
          pose proof bbnum_le_next_num nil BB_then_now then_start_num c1 H.
          subst then_res. lia.
        }

        specialize (H1 H2). subst else_res. simpl in H. lia.

      ** pose proof In_head_or_body BasicBlock x empty_block then_delta tail.
      destruct H as [head | body].
      rewrite <- head in head_then.
      destruct then_delta.
      --- simpl in tail. tauto.
      ---
      assert(t: b :: then_delta <> nil). {
        pose proof (nil_cons).
        specialize (H BasicBlock b BBdelta). intros contra.
        rewrite contra in tail. tauto.  
      }
      specialize (head_then t). 
      rewrite head_then in cond2.  subst BB_then_now. simpl in cond2. lia.
      ---
        assert(temp: BBnum_set (tl then_delta) n).
        {
          unfold BBnum_set. exists x. split. tauto. tauto.
        }
        specialize (c1_prop2 temp). lia.
    + destruct case2 as [x [cond1 cond2]].
      unfold all_lt in c2_prop2. specialize (c2_prop2 n).
      pose proof In_pre_or_tail BasicBlock x else_res.(BBn) else_delta cond1.
      destruct H as [head | tail].
      ** rewrite head in cond2. rewrite <- cond2.
         pose proof inherit_lt_num_prop_list nil BB_else_now then_end_num c2.
         
         assert((BB_else_now.(block_num) < then_end_num)%nat). {
          assert(lt BB_else_now.(block_num) then_start_num).
          subst BB_else_now. simpl. lia.
          assert(le then_start_num then_end_num).
          pose proof bbnum_le_next_num nil BB_then_now then_start_num c1.
          assert((BB_then_now.(block_num) < then_start_num)%nat). {
            subst BB_then_now. cbn [block_num]. lia.
          }
          specialize (H1 H2). subst then_end_num. subst then_res. simpl in H0. lia.
          lia.
        }

        specialize (H H0). subst else_res. simpl in H. lia.
      ** pose proof In_head_or_body BasicBlock x empty_block else_delta tail.
        destruct H as [head | body].
        rewrite <- head in head_else.
        destruct else_delta.
        --- simpl in tail. tauto.
        ---
        assert(t: b :: else_delta <> nil). {
          pose proof (nil_cons).
          specialize (H BasicBlock b BBdelta). intros contra.
          rewrite contra in tail. tauto.  
        }
        specialize (head_else t). 
        rewrite head_else in cond2.  subst BB_else_now. simpl in cond2. lia.
        ---
          assert(temp: BBnum_set (tl else_delta) n).
          {
            unfold BBnum_set. exists x. split. tauto. tauto.
          }
          specialize (c2_prop2 temp). lia.

  (*branch 3: 证明BBdelta的所有jump dest都在[startnum, endnum]*)
  - clear c1_prop1 c1_prop2 c2_prop1 c2_prop2.
    rename H into A. unfold BBjmp_dest_set in A. destruct A as [BB A]. destruct A as [A1 A2]. 
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
    destruct separate_delta_jump_dest as [[[case2 | case3] | case4] | case5].
    +   (*用c1_prop3*)
      destruct case2 as [x [cond1 cond2]]. 
      unfold BBjmp_dest_set in c1_prop3. specialize (c1_prop3 a). sets_unfold in c1_prop3.
      pose proof In_pre_or_tail BasicBlock x then_res.(BBn) then_delta cond1.
      destruct H as [head | tail].
      * rewrite head in cond2. pose proof JmpInfo_inherit_for_list nil BB_then_now then_start_num c1. 
        subst then_res. rewrite H in cond2. subst BB_then_now. simpl in cond2.
        destruct cond2. lia. discriminate H0.
      * 
      assert (temp: (exists BB : BasicBlock, In BB then_delta /\ (jump_dest_1 BB.(jump_info) = a \/ jump_dest_2 BB.(jump_info) = Some a))).
      {
        exists x. split. 
        tauto. tauto. 
      }
      specialize (c1_prop3 temp).  unfold section in c1_prop3.  lia.
    + (*用c2_prop3*)
      destruct case3 as [x [cond1 cond2]].
      unfold BBjmp_dest_set in c2_prop3. specialize (c2_prop3 a). sets_unfold in c2_prop3.
      pose proof In_pre_or_tail BasicBlock x else_res.(BBn) else_delta cond1. destruct H as [head | tail].
      * rewrite head in cond2. pose proof JmpInfo_inherit_for_list nil BB_else_now then_end_num c2. 
      subst else_res. rewrite H in cond2. subst BB_else_now. simpl in cond2.
      destruct cond2. lia. discriminate H0.
      *
      assert (temp: (exists BB : BasicBlock, In BB else_delta /\ (jump_dest_1 BB.(jump_info) = a \/ jump_dest_2 BB.(jump_info) = Some a))).
      {
        exists x. split. tauto. tauto.
      }
      specialize (c2_prop3 temp).  unfold section in c2_prop3.  lia.
    + lia.
    + lia.
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
  destruct separate_delta_jump_dest as [[[case2 | case3] | case4] | case5].
  +   (*用c1_prop3*)
    destruct case2 as [x [cond1 cond2]]. 
    unfold BBjmp_dest_set in c1_prop3. specialize (c1_prop3 a). sets_unfold in c1_prop3.
    pose proof In_pre_or_tail BasicBlock x then_res.(BBn) then_delta cond1. destruct H as [head | tail].
    * rewrite head in cond2. pose proof JmpInfo_inherit_for_list nil BB_then_now then_start_num c1. 
      subst then_res. rewrite H in cond2. subst BB_then_now. simpl in cond2.
      destruct cond2. lia. discriminate H0.
    *
    assert (temp: (exists BB : BasicBlock, In BB then_delta /\ (jump_dest_1 BB.(jump_info) = a \/ jump_dest_2 BB.(jump_info) = Some a))).
    {
      exists x. split. tauto. tauto. 
    }
    specialize (c1_prop3 temp).  unfold section in c1_prop3.  lia.
  + (*用c2_prop3*)
    destruct case3 as [x [cond1 cond2]].
    unfold BBjmp_dest_set in c2_prop3. specialize (c2_prop3 a). sets_unfold in c2_prop3.
    pose proof In_pre_or_tail BasicBlock x else_res.(BBn) else_delta cond1. destruct H as [head | tail].

    * rewrite head in cond2. pose proof JmpInfo_inherit_for_list nil BB_else_now then_end_num c2. 
      subst else_res. rewrite H in cond2. subst BB_else_now. simpl in cond2.
      destruct cond2. lia. discriminate H0.
    *
    assert (temp: (exists BB : BasicBlock, In BB else_delta /\ (jump_dest_1 BB.(jump_info) = a \/ jump_dest_2 BB.(jump_info) = Some a))).
    {
      exists x. split. tauto. tauto. 
    }
    specialize (c2_prop3 temp). unfold section in c2_prop3.  lia.
  + lia.
  + lia.
Qed.

Lemma Q_while_BBgen_range_wo:
forall (e: expr) (c1 c2: list cmd),

    P_BBgen_range_wo cmd_BB_gen c1 ->
    P_BBgen_range_wo cmd_BB_gen c2 ->

    Q_BBgen_range_wo (CWhile c1 e c2).
Proof.
Admitted. (*DONT CARE ABOUT WHILE*)

(*这个肯定成立，没有新的block*)
Lemma Q_asgn_BBgen_range_wo:
forall  (x: var_name) (e: expr),
    Q_BBgen_range_wo (CAsgn x e).
Proof. 
  intros. unfold Q_BBgen_range_wo. intros. simpl in H0.
  unfold to_result in H1. simpl in H1. 
  assert (BBdelta = nil). {
    assert (BBs ++ nil = BBs ++ BBdelta). {
      rewrite app_nil_r. apply H1.
    }
    apply cut_eq_part_list_l in H3. rewrite H3. tauto.
  }
  rewrite H3. simpl. repeat split.
  - unfold all_gt. intros. unfold BBnum_set in H4. destruct H4 as [? [? ?]].
    unfold In in H4. tauto.
  - unfold all_lt. intros. unfold BBnum_set in H4. destruct H4 as [? [? ?]].
    unfold In in H4. tauto.
  - unfold BBjmp_dest_set in H4. destruct H4 as [? [? ?]]. unfold In in H4. tauto.
  - unfold BBjmp_dest_set in H4. destruct H4 as [? [? ?]]. unfold In in H4. tauto.
Qed.

Lemma P_BBgen_nil_wo:
    P_BBgen_range_wo cmd_BB_gen nil.
Proof.
  unfold P_BBgen_range_wo. intros. simpl in H0. unfold to_result in H1. simpl in H1. rename H2 into new. 
  assert (BBdelta = nil). {
    assert (BBs ++ nil = BBs ++ BBdelta). {
      rewrite app_nil_r. apply H1.
    }
    apply cut_eq_part_list_l in H2. rewrite H2. tauto.
  }
  rewrite H2. simpl. repeat split.
  - unfold all_ge. intros. unfold BBnum_set in H3. destruct H3 as [? [? ?]].
    unfold In in H4. tauto.
  - unfold all_lt. intros. unfold BBnum_set in H3. destruct H3 as [? [? ?]].
    unfold In in H4. tauto.
  - unfold BBjmp_dest_set in H3. destruct H3 as [? [? ?]]. unfold In in H4. tauto.
  - unfold BBjmp_dest_set in H3. destruct H3 as [? [? ?]]. unfold In in H4. tauto.
Qed.


Lemma P_BBgen_con_wo:
    forall (c: cmd) (cmds: list cmd),
    Q_BBgen_range_wo c ->
    P_BBgen_range_wo cmd_BB_gen cmds ->
    P_BBgen_range_wo cmd_BB_gen (c::cmds).
Proof.
  intros.
  unfold P_BBgen_range_wo in H0.
  unfold Q_BBgen_range_wo in H.
  unfold P_BBgen_range_wo.
  intros.
  rename H4 into lt_prop.
  set (endnum' := (cmd_BB_gen c BBs BBnow startnum).(next_block_num)).
  set (BBwo_last' := (cmd_BB_gen c nil BBnow startnum).(BasicBlocks)).
  set (BBnow' := (cmd_BB_gen c BBs BBnow startnum).(BBn)).
  set (BBdelta' := BBwo_last' ++ BBnow'::nil).
  assert((cmd_BB_gen c BBs BBnow startnum).(BasicBlocks) = BBs ++ BBwo_last').
  {
    pose proof cmd_BB_delta c BBs BBwo_last' BBnow startnum. apply H4. tauto.
  }
    assert(to_result(cmd_BB_gen c BBs BBnow startnum) = BBs ++ BBdelta').
  {
    subst BBdelta'.
    pose proof cmd_BB_delta c BBs BBwo_last' BBnow startnum. 
    unfold to_result. rewrite H5. subst BBnow'. rewrite <- app_assoc. reflexivity. tauto.
  }
  specialize (H startnum endnum' BBs BBnow BBwo_last' H1). destruct H. tauto. tauto. tauto.
  set (BBwo_last'' := (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow' endnum').(BasicBlocks)).
  set (BBnow'' := (list_cmd_BB_gen cmd_BB_gen cmds (BBs++BBwo_last') BBnow' endnum').(BBn)).
  set (BBdelta'' := BBwo_last'' ++ BBnow''::nil).
  specialize (H0 endnum' endnum (BBs++BBwo_last') BBnow' BBwo_last'').
  assert(jump_kind BBnow'.(jump_info) = UJump /\ jump_dest_2 BBnow'.(jump_info) = None).
  {
    pose proof JmpInfo_inherit BBs BBnow startnum c. subst BBnow'. rewrite H7. tauto.
  }
  assert(endnum = (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBwo_last') BBnow' endnum').(next_block_num)).
  {
    cbn[list_cmd_BB_gen] in H2. subst endnum' BBnow'. rewrite H2. 
    rewrite <- H4. reflexivity.
  }
  assert((list_cmd_BB_gen cmd_BB_gen cmds nil BBnow' endnum').(BasicBlocks) = BBwo_last'').
  {
    tauto.
  }
  assert(to_result (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBwo_last') BBnow' endnum') = (BBs ++ BBwo_last') ++ BBdelta'').
  {
    subst BBdelta''.
    pose proof list_cmd_BB_delta cmds (BBs++BBwo_last') BBwo_last'' BBnow' endnum'.
    unfold to_result.
    specialize (H10 H9).
    rewrite H10.
    subst BBnow''.
    rewrite app_assoc.
    reflexivity.
  }

  assert((list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBwo_last') BBnow' endnum').(BasicBlocks) = (BBs ++ BBwo_last') ++ BBwo_last'').
  {
    unfold to_result in H10. subst BBdelta''. subst BBnow''. 
    pose proof cut_eq_part_list_r BasicBlock as key.
    specialize (key ((list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBwo_last') BBnow' endnum').(BBn) :: nil)).
    specialize (key (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBwo_last') BBnow' endnum').(BasicBlocks)).
    specialize (key ((BBs ++ BBwo_last') ++ BBwo_last'')).
    rewrite app_assoc_reverse in key. specialize (key H10).
    tauto.
  }
  clear H10. rename H11 into H10.

  assert((BBnow'.(block_num) < endnum')%nat).
  {
    pose proof inherit_lt_num_prop BBs BBnow startnum c lt_prop. 
    subst BBnow'.
    subst endnum'. tauto.
  }
  specialize (H0 H7 H8 H10 H11). 
  assert((list_cmd_BB_gen cmd_BB_gen (c :: cmds) BBs BBnow startnum).(BasicBlocks) = BBs ++ BBwo_last' ++ BBwo_last'').
{
   cbn[list_cmd_BB_gen]. rewrite H4. subst endnum'. subst BBnow'.
   pose proof list_cmd_BB_delta cmds (BBs++BBwo_last') BBwo_last'' ((cmd_BB_gen c BBs BBnow startnum).(BBn)) ((cmd_BB_gen c BBs BBnow startnum).(next_block_num)) H9.
   rewrite app_assoc. tauto.
}
  assert((list_cmd_BB_gen cmd_BB_gen (c :: cmds) BBs BBnow startnum).(BBn) = BBnow'').
{
  cbn[list_cmd_BB_gen]. rewrite H4. subst endnum'. subst BBnow'.
  tauto.
}
  assert((list_cmd_BB_gen cmd_BB_gen (c :: cmds) BBs BBnow startnum).(next_block_num) = endnum).
{
  cbn[list_cmd_BB_gen]. rewrite H4. subst endnum'. subst BBnow'.
  rewrite H8. tauto.
}
(* properties on delta, wo_last and now*)
  assert(BBdelta = BBwo_last' ++ BBwo_last'').
{
  assert(BBs ++ BBwo_last' ++ BBwo_last'' = BBs ++ BBdelta).
  rewrite <- H3. rewrite app_assoc.  rewrite app_assoc in H12.
  rewrite <- H12. reflexivity.
  apply app_inv_head in H15.
  subst BBdelta''. rewrite H15. tauto.
}
split.
  + rewrite H15.
    destruct H0.
     assert((endnum' >= startnum)%nat).
  {
    pose proof bbnum_le_next_num_single_cmd BBs BBnow startnum c lt_prop. lia.
  }

  assert(all_gt (BBnum_set (tl(BBwo_last'))) startnum).
  {
    clear H17 H15 H14 H13 H12 H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H1 H16 H0 BBdelta'' BBnow'' BBwo_last'' endnum.
    tauto.
  }
    assert(all_ge (BBnum_set (tl(BBwo_last''))) startnum).
  {
    destruct BBwo_last''.
    - simpl. unfold all_ge. intros. unfold BBnum_set in H19. destruct H19 as [bb [cond1 cond2]].
      simpl in cond1. tauto.
    - simpl. simpl in H0. unfold all_ge in H0. 
      unfold all_ge. intros. specialize (H0 n H19). lia.
  }
  destruct BBwo_last'.
  - simpl. destruct BBwo_last''. 
    * simpl. tauto.
    * simpl. subst BBdelta''. unfold all_gt in H19. unfold all_ge. intros. specialize (H19 n).
      simpl in H19.
      specialize (H19 H20). tauto.
  - simpl. simpl in H18. subst BBdelta''.
    unfold all_ge in H19. unfold all_ge. intros. unfold BBnum_set in H20. destruct H20 as [bb [cond1 cond2]].
    pose proof in_app_iff as key. specialize (key BasicBlock BBwo_last' BBwo_last'' bb).
    assert( In bb BBwo_last' \/ In bb BBwo_last''). apply key. tauto.
    destruct H20.
    * unfold all_gt in H18. specialize (H18 n). 
      assert(BBnum_set BBwo_last' n ).
      {
        unfold BBnum_set. exists bb. split. tauto. tauto.
      }
      specialize (H18 H21). lia.
    * unfold all_gt in H19. specialize (H19 n).
      assert(BBnum_set (BBwo_last'') n ).
      {
        unfold BBnum_set. exists bb. split. tauto.
        tauto.
      }
      destruct BBwo_last''.
      -- unfold BBnum_set in H21. destruct H21 as [bb' [cond1' cond2']]. simpl in cond1'. tauto.
      -- simpl in H19. 
         unfold BBnum_set in H21. destruct H21 as [bb' [cond1' cond2']]. simpl in cond1'. destruct cond1' as [case1 | case2].
         ** pose proof BBgen_head_prop_wo cmds BBnow' endnum' as k. simpl in k. 
            assert(tmp: (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow' endnum').(BasicBlocks) <> nil).
            {
              rewrite H9. pose proof nil_cons as k1.
              specialize (k1 BasicBlock b0 BBwo_last''). intros contra. rewrite contra in k1. tauto. 
            }
            specialize (k tmp). rewrite H9 in k. simpl in k. rewrite case1 in k. rewrite cond2' in k. rewrite k.
            destruct c.  
            --- simpl in H4. pose proof H4. assert (BBs ++ nil = BBs ++ b :: BBwo_last'). {
                  rewrite app_nil_r. apply H21.
                }
                pose proof cut_eq_part_list_l BasicBlock BBs nil (b :: BBwo_last') H22.
                pose proof nil_cons. specialize (H24  BasicBlock b BBwo_last').
                contradiction.
            --- pose proof if_BBn_num_prop e c1 c2 BBs BBnow startnum. subst BBnow'. simpl. lia. 
            --- admit. (*DONT CARE ABOUT WHILE*)


         ** assert (tmp: BBnum_set BBwo_last'' n ). {
            unfold BBnum_set. exists bb'. split. tauto. tauto.
          }
          specialize (H19 tmp). tauto.
  + split. 
     - rewrite H15.
     destruct H0.
     assert((endnum' <= endnum)%nat).
      {
        pose proof bbnum_le_next_num as key.
        specialize (key (BBs ++ BBwo_last') BBnow' endnum' cmds H11). 
        subst endnum. lia.
      }

      assert(all_lt (BBnum_set (tl(BBwo_last'))) endnum').
      {
        destruct H6. tauto.
      }
        assert(all_lt (BBnum_set (tl(BBwo_last''))) endnum).
      {
        destruct H16. tauto.
      }
      destruct BBwo_last'.
      -- simpl. tauto.
      -- simpl. simpl in H18. unfold all_lt. intros. rename H20 into key. unfold BBnum_set in key. destruct key as [key_bb [cond1 cond2]].
         apply in_app_iff in cond1. destruct cond1.
         ** unfold all_lt in H18. specialize (H18 n). 
            assert(BBnum_set BBwo_last' n ).
            {
              unfold BBnum_set. exists key_bb. split. tauto. tauto.
            }
            specialize (H18 H21). lia.
          ** unfold all_lt in H19. specialize (H19 n).
            destruct BBwo_last''.
            --- simpl in H20. tauto.
            --- simpl in H19. simpl in H20. 
                destruct H20 as [case1 | case2].
                *** pose proof BBgen_head_prop_wo cmds BBnow' endnum' as key. simpl in key.
                    assert(tmp: (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow' endnum').(BasicBlocks) <> nil).
                    {
                      rewrite H9. pose proof nil_cons as k1.
                      specialize (k1 BasicBlock b0 BBwo_last''). intros contra. rewrite contra in k1. tauto. 
                    }
                    specialize (key tmp). rewrite H9 in key. simpl in key. rewrite case1 in key. rewrite cond2 in key. rewrite key. lia.

                *** unfold all_lt in H18. specialize (H18 n).
                    assert(BBnum_set (BBwo_last'') n ).
                    {
                      unfold BBnum_set. exists key_bb. split. tauto.
                      tauto.
                    }
                    specialize (H19 H20). lia.
      - rewrite H15. 
        assert(lt_num: (endnum' <= endnum)%nat).
        {
          pose proof bbnum_le_next_num as key.
          specialize (key (BBs ++ BBwo_last') BBnow' endnum' cmds H11). 
          subst endnum. lia.
        }

        assert (lt_num1: (startnum <= endnum')%nat). 
        {
          pose proof bbnum_le_next_num_single_cmd BBs BBnow startnum c lt_prop. lia.
        }
  

        sets_unfold. intros. 
        destruct H0 as [p1 [p2 p3]].
        destruct H6 as [q1 q2].
        sets_unfold in q2. 
        sets_unfold in p3.
        unfold BBjmp_dest_set in H16. 
        destruct H16 as [BB [cond1 cond2]].
        -- apply in_app_iff in cond1. destruct cond1 as [cond1 | cond1].
           ** specialize (q2 a). assert (BBjmp_dest_set BBwo_last' a). {
              unfold BBjmp_dest_set. exists BB. split. tauto. tauto.
            }

            specialize (q2 H0). unfold section in q2. unfold section. destruct q2. split. lia. lia. 
           ** specialize (p3 a). assert (BBjmp_dest_set BBwo_last'' a). {
              unfold BBjmp_dest_set. exists BB. split. tauto. tauto.
            }

            specialize (p3 H0). unfold section in p3. unfold section. destruct p3. split. lia. lia. 
Admitted. (* QED *)



Section BB_gen_range_wo_sound.


Variable BB_gen_range_wo_soundness: forall (c: cmd), Q_BBgen_range_wo c.

Fixpoint BBgen_list_range_wo_soundness (cmds: list cmd): P_BBgen_range_wo cmd_BB_gen cmds :=
  match cmds with
  | nil => P_BBgen_nil_wo 
  | c :: cmds0 => P_BBgen_con_wo c cmds0 (BB_gen_range_wo_soundness c) (BBgen_list_range_wo_soundness cmds0)
  end.

End BB_gen_range_wo_sound.

Fixpoint BB_gen_range_wo_soundness (c: cmd): Q_BBgen_range_wo c :=
  match c with
  | CAsgn x e => Q_asgn_BBgen_range_wo x e
  | CIf e cmds1 cmds2 =>
      Q_if_BBgen_range_wo e cmds1 cmds2
        (BBgen_list_range_wo_soundness BB_gen_range_wo_soundness cmds1)
        (BBgen_list_range_wo_soundness BB_gen_range_wo_soundness cmds2)
  | CWhile cmds1 e cmds2 =>
      Q_while_BBgen_range_wo e cmds1 cmds2
        (BBgen_list_range_wo_soundness BB_gen_range_wo_soundness cmds1)
        (BBgen_list_range_wo_soundness BB_gen_range_wo_soundness cmds2)
  end.

Lemma BBgen_range_wo_single_soundness_correct:
    forall (c: cmd),
    Q_BBgen_range_wo c.
Proof.
    apply BB_gen_range_wo_soundness.
Qed.

Lemma BBgen_range_wo_list_soundness_correct:
    forall (cmds: list cmd),
    P_BBgen_range_wo cmd_BB_gen cmds.
Proof.
    apply BBgen_list_range_wo_soundness.
    pose proof BBgen_range_wo_single_soundness_correct.
    apply H.
Qed.

(* end ================================================================================= *)



(* BBgen If 的一些性质 ================================================================================= *)


(*! IMPORTANT 对于if而言，新产生的BBs中的第一个，就是BBthen，那么自然有其blocknum的性质*)
Lemma if_head_prop:
  forall (e: expr) (c1 c2: list cmd)(BBswo_ BBs: list BasicBlock)(BBnow BBnow'_: BasicBlock)(BBnum: nat),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) = BBs ++ BBnow'_ :: BBswo_
  ->
  (hd empty_block (BBswo_)).(block_num) = S BBnum.
Proof.
  intros.
  cbn [cmd_BB_gen] in H. simpl in H.
  remember ({|
  block_num := BBnow.(block_num);
  commands := BBnow.(cmd);
  jump_info :=
    {|
      jump_kind := CJump;
      jump_dest_1 := S BBnum;
      jump_dest_2 := Some (S(S BBnum));
      jump_condition := Some e
    |}
|}
:: to_result
     (list_cmd_BB_gen cmd_BB_gen c1 nil
        {|
          block_num := S BBnum;
          commands := nil;
          jump_info :=
            {|
              jump_kind := UJump;
              jump_dest_1 := BBnum;
              jump_dest_2 := None;
              jump_condition := None
            |}
        |} (S (S (S BBnum)))) ++
   to_result
     (list_cmd_BB_gen cmd_BB_gen c2 nil
        {|
          block_num := S (S BBnum);
          commands := nil;
          jump_info :=
            {|
              jump_kind := UJump;
              jump_dest_1 := BBnum;
              jump_dest_2 := None;
              jump_condition := None
            |}
        |}
        (list_cmd_BB_gen cmd_BB_gen c1 nil
           {|
             block_num := S BBnum;
             commands := nil;
             jump_info :=
               {|
                 jump_kind := UJump;
                 jump_dest_1 := BBnum;
                 jump_dest_2 := None;
                 jump_condition := None
               |}
           |} (S (S (S BBnum)))).(next_block_num))) as BBswo_2.
  pose proof cut_eq_part_list_l BasicBlock BBs BBswo_2 (BBnow'_ :: BBswo_) H.
  rewrite HeqBBswo_2 in H0. inversion H0. rewrite H3. clear H2.
  rename H3 into key. unfold to_result in key. 
  remember (((list_cmd_BB_gen cmd_BB_gen c1 nil
  {|
    block_num := S BBnum;
    commands := nil;
    jump_info :=
      {|
        jump_kind := UJump;
        jump_dest_1 := BBnum;
        jump_dest_2 := None;
        jump_condition := None
      |}
  |} (S (S (S BBnum)))).(BasicBlocks))) as e0.

  remember ((list_cmd_BB_gen cmd_BB_gen c1 nil
  {|
    block_num := S BBnum;
    commands := nil;
    jump_info :=
      {|
        jump_kind := UJump;
        jump_dest_1 := BBnum;
        jump_dest_2 := None;
        jump_condition := None
      |}
  |} (S (S (S BBnum)))).(BBn) :: nil) as e1.

  remember ((list_cmd_BB_gen cmd_BB_gen c2 nil
  {|
    block_num := S(S BBnum);
    commands := nil;
    jump_info :=
      {|
        jump_kind := UJump;
        jump_dest_1 := BBnum;
        jump_dest_2 := None;
        jump_condition := None
      |}
  |}
  (list_cmd_BB_gen cmd_BB_gen c1 nil
     {|
       block_num := S BBnum;
       commands := nil;
       jump_info :=
         {|
           jump_kind := UJump;
           jump_dest_1 := BBnum;
           jump_dest_2 := None;
           jump_condition := None
         |}
     |} (S (S (S BBnum)))).(next_block_num)).(BasicBlocks) ++
(list_cmd_BB_gen cmd_BB_gen c2 nil
  {|
    block_num := S(S BBnum);
    commands := nil;
    jump_info :=
      {|
        jump_kind := UJump;
        jump_dest_1 := BBnum;
        jump_dest_2 := None;
        jump_condition := None
      |}
  |}
  (list_cmd_BB_gen cmd_BB_gen c1 nil
     {|
       block_num := S BBnum;
       commands := nil;
       jump_info :=
         {|
           jump_kind := UJump;
           jump_dest_1 := BBnum;
           jump_dest_2 := None;
           jump_condition := None
         |}
     |} (S (S (S BBnum)))).(next_block_num)).(BBn) :: nil) as e2.
    
    pose proof hd_A_and_B_is_hd_A_if_A_not_nil (e0 ++ e1) e2 as hd_position.
    assert (e0_not_nil: (e0 ++ e1) <> nil).
    {
      pose proof classic (e0 = nil) as He0_nil. destruct He0_nil as [He0_nil | He0_nnil].
      - rewrite He0_nil. rewrite app_nil_l. rewrite Heqe1. unfold not. intros.
        inversion H1.
      - unfold not. intros. destruct e0. tauto. discriminate H1.   
    }
    pose proof hd_position e0_not_nil as hd_position.
    subst BBswo_. rewrite hd_position.
    remember ({|
      block_num := S BBnum;
      commands := nil;
      jump_info := {|
                   jump_kind := UJump;
                   jump_dest_1 := BBnum;
                   jump_dest_2 := None;
                   jump_condition := None |} |}) as BBnow_then.
    assert (e0 ++ e1 = to_result(list_cmd_BB_gen cmd_BB_gen c1 nil BBnow_then
            (S (S (S BBnum))))). {
      unfold to_result. subst e0. subst e1. tauto.
    }
    pose proof BBgen_head_prop c1 BBnow_then (S ( S (S BBnum))).
    simpl in H2. subst e0. subst e1. rewrite H2. subst BBnow_then. simpl. tauto.
Qed. 



Lemma BBn_determined_by_cmds_BBn_single_cmd (BBnow: BasicBlock) (c: cmd) (BBs: list BasicBlock) (BBnum: nat):
  forall (BBs': list BasicBlock),
  (cmd_BB_gen c BBs BBnow BBnum).(BBn) = (cmd_BB_gen c BBs' BBnow BBnum).(BBn).
Proof.
  intros. destruct c.
  - simpl. tauto.
  - cbn[cmd_BB_gen]. simpl. tauto.
  - cbn[cmd_BB_gen]. simpl. tauto.
Qed.


Lemma BBnum_determined_by_cmds_single_cmd (BBnow: BasicBlock) (c: cmd) (BBs: list BasicBlock) (BBnum: nat):
  forall (BBs': list BasicBlock),
  (cmd_BB_gen c BBs BBnow BBnum).(next_block_num) = (cmd_BB_gen c BBs' BBnow BBnum).(next_block_num).
Proof.
  intros. destruct c.
    - simpl. tauto.
    - cbn[cmd_BB_gen]. simpl. tauto.
    - cbn[cmd_BB_gen]. simpl. tauto.
Qed.

Lemma BBn_determined_by_cmds_BBn (BBnow: BasicBlock) (cmds: list cmd) (BBs: list BasicBlock) (BBnum: nat):
  forall (BBs': list BasicBlock),
    (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BBn) = (list_cmd_BB_gen cmd_BB_gen cmds BBs' BBnow BBnum).(BBn).
Proof.
  intros. revert BBs BBs' BBnow BBnum. induction cmds; intros.
  - cbn[list_cmd_BB_gen]. simpl. tauto.
  - cbn[list_cmd_BB_gen]. 
    pose proof BBn_determined_by_cmds_BBn_single_cmd BBnow a BBs BBnum BBs'.
    rewrite H. 
    specialize (IHcmds (cmd_BB_gen a BBs BBnow BBnum).(BasicBlocks) (cmd_BB_gen a BBs' BBnow BBnum).(BasicBlocks) (cmd_BB_gen a BBs' BBnow BBnum).(BBn) (cmd_BB_gen a BBs BBnow BBnum).(next_block_num)). rewrite IHcmds.
    pose proof BBnum_determined_by_cmds_single_cmd BBnow a BBs BBnum BBs'.
    rewrite H0. tauto.
Qed.
    


Lemma if_separate_for_pcons1:
  forall (e: expr) (c1 c2 cmds: list cmd) (BBs BBswo_ : list BasicBlock)(BBnow BBnow'_ BBnow_mid : BasicBlock)(BBnum BBnum'_: nat),
  BBnow_mid = (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) ->
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) = BBs ++ BBnow'_ :: BBswo_  ->
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num) = BBnum'_ ->
  (list_cmd_BB_gen cmd_BB_gen (CIf e c1 c2 :: cmds) BBs BBnow BBnum).(BasicBlocks) 
  = 
  (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_).(BasicBlocks).
Proof.
  intros.
  pose proof add_BBs_in_generation_reserves_BB cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_.
  unfold to_result in H2.
  pose proof BBn_determined_by_cmds_BBn BBnow_mid cmds (BBs ++ BBnow'_ :: BBswo_) BBnum'_ nil. 
  rewrite H3 in H2.
  pose proof cut_eq_part_list_r BasicBlock ((list_cmd_BB_gen cmd_BB_gen cmds nil BBnow_mid BBnum'_).(BBn) :: nil) (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_).(BasicBlocks) ((BBs ++ BBnow'_ :: BBswo_) ++
  (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow_mid BBnum'_).(BasicBlocks)).
  rewrite <- app_assoc in H4. pose proof H4 H2 as H4. clear H2. clear H3. rewrite H4.

  pose proof add_BBs_in_generation_reserves_BB (CIf e c1 c2 :: cmds) BBs BBnow BBnum.
  unfold to_result in H2.
  pose proof BBn_determined_by_cmds_BBn BBnow (CIf e c1 c2 :: cmds) BBs BBnum nil.
  rewrite H3 in H2.
  pose proof cut_eq_part_list_r BasicBlock ((list_cmd_BB_gen cmd_BB_gen (CIf e c1 c2 :: cmds) nil BBnow BBnum).(BBn) :: nil) (list_cmd_BB_gen cmd_BB_gen (CIf e c1 c2 :: cmds) BBs BBnow BBnum).(BasicBlocks) (BBs ++
  (list_cmd_BB_gen cmd_BB_gen (CIf e c1 c2 :: cmds) nil BBnow BBnum).(BasicBlocks)).
  rewrite <- app_assoc in H5. pose proof H5 H2 as H5. clear H2 H3. rewrite H5.

  rewrite <- app_assoc.
  assert ((list_cmd_BB_gen cmd_BB_gen (CIf e c1 c2 :: cmds) nil BBnow BBnum).(BasicBlocks) = (BBnow'_ :: BBswo_) ++ (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow_mid BBnum'_).(BasicBlocks)). {
    cbn[list_cmd_BB_gen]. 
    pose proof BBn_determined_by_cmds_BBn_single_cmd BBnow (CIf e c1 c2) BBs BBnum nil. 
    rewrite H2 in H. rewrite <- H. 
    pose proof BBnum_determined_by_cmds_single_cmd BBnow (CIf e c1 c2) BBs BBnum nil.
    rewrite H3 in H1. rewrite H1.
    pose proof add_BBs_in_generation_reserves_BB cmds (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BasicBlocks) BBnow_mid BBnum'_.
    unfold to_result in H6.
    pose proof BBn_determined_by_cmds_BBn BBnow_mid cmds (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BasicBlocks) BBnum'_ nil. rewrite H7 in H6.
    pose proof cut_eq_part_list_r BasicBlock ((list_cmd_BB_gen cmd_BB_gen cmds nil BBnow_mid BBnum'_).(BBn) :: nil) (list_cmd_BB_gen cmd_BB_gen cmds (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BasicBlocks) BBnow_mid BBnum'_).(BasicBlocks) ((cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BasicBlocks) ++
    (list_cmd_BB_gen cmd_BB_gen cmds nil BBnow_mid BBnum'_).(BasicBlocks)).
    rewrite <- app_assoc in H8.
    pose proof H8 H6 as H8. clear H6 H7. rewrite H8.

    pose proof Q_add_BBs_in_generation_reserves_BB_sound (CIf e c1 c2) BBs BBnow BBnum.
    unfold to_result in H6.
    pose proof BBn_determined_by_cmds_BBn_single_cmd BBnow (CIf e c1 c2) BBs BBnum nil.
    rewrite H7 in H6.
    pose proof cut_eq_part_list_r BasicBlock ((cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BBn) :: nil) (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) (BBs ++
    (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BasicBlocks)).
    rewrite <- app_assoc in H9.
    pose proof H9 H6. clear H6 H7 H9. rewrite H10 in H0.
    apply cut_eq_part_list_l in H0. rewrite H0. tauto.

  }

  rewrite H2. tauto.
Qed.



Lemma if_separate_for_pcons2:
  forall (e: expr) (c1 c2 cmds: list cmd) (BBs BBswo_ : list BasicBlock)(BBnow BBnow'_ BBnow_mid : BasicBlock)(BBnum BBnum'_: nat),
  BBnow_mid = (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) ->
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) = BBs ++ BBnow'_ :: BBswo_ ->
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num) = BBnum'_ ->
  (list_cmd_BB_gen cmd_BB_gen (CIf e c1 c2 :: cmds) BBs BBnow BBnum).(BBn) :: nil 
  = 
  (list_cmd_BB_gen cmd_BB_gen cmds (BBs ++ BBnow'_ :: BBswo_) BBnow_mid BBnum'_).(BBn) :: nil.
Proof.
  intros.
  pose proof BBn_determined_by_cmds_BBn BBnow (CIf e c1 c2 :: cmds) BBs BBnum nil. rewrite H2.
  pose proof BBn_determined_by_cmds_BBn BBnow_mid cmds (BBs ++ BBnow'_ :: BBswo_) BBnum'_ nil. 
  rewrite H3.
  cbn[list_cmd_BB_gen]. f_equal.
  pose proof BBn_determined_by_cmds_BBn_single_cmd BBnow (CIf e c1 c2) BBs BBnum nil. rewrite <- H4.
  rewrite <- H.
  pose proof BBn_determined_by_cmds_BBn BBnow_mid cmds (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BasicBlocks) (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(next_block_num) nil. rewrite H5.
  rewrite <- H1.
  pose proof BBnum_determined_by_cmds_single_cmd BBnow (CIf e c1 c2) BBs BBnum nil. rewrite H6.
  tauto.
Qed.



(* ================================================================================= *)


Definition endinfo_property (BBnow: BasicBlock) := 
  gt BBnow.(block_num) (jump_dest_1 BBnow.(jump_info)).
  
(*如果BBnow的endinfo满足特殊符号性质，那么对于任何新生成的的一串BB（BBs)，对于CIf指令而言，它只能在BBs的最后一个Block里，也就是(res.(BBn)的jmpdest里*)
Lemma unique_endinfo_if:
  forall (BBs BBswo_ BBs'_: list BasicBlock)  (e: expr) (c1 c2: list cmd) (BBnow BBnow'_: BasicBlock) (BBnum: nat),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) = BBs ++ BBnow'_ :: BBswo_ ->
  BBs'_ =  BBswo_ ++ (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil ->
  endinfo_property BBnow ->
  jump_kind BBnow.(jump_info) = UJump /\ jump_dest_2 BBnow.(jump_info) = None ->
  (BBnow.(block_num) < BBnum)%nat ->
  ~ (BBnow.(jump_info).(jump_dest_1) ∈ BBjmp_dest_set (BBnow'_ :: nil ++ BBswo_)).
Proof.
  intros. rename H2 into Hn1. rename H3 into Hn2.
  unfold endinfo_property in H1. unfold not. sets_unfold. intros.
  pose proof inherit_not_jmp_to_self_soundness_correct (CIf e c1 c2).
  unfold Q_inherit_not_jmp_to_self in H3.
  specialize (H3 nil BBnow BBnum). pose proof H3 H1 as H3.
  pose proof Q_add_BBs_in_generation_reserves_BB_sound (CIf e c1 c2) BBs BBnow BBnum.
  unfold to_result in H4.
  pose proof BBn_determined_by_cmds_BBn_single_cmd BBnow (CIf e c1 c2) BBs BBnum nil.
  rewrite H5 in H4. 
  pose proof cut_eq_part_list_r BasicBlock ((cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BBn) :: nil) (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) (BBs ++
  (cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BasicBlocks)).
  rewrite <- app_assoc in H6. pose proof H6 H4 as H6. 
  rewrite H6 in H. apply cut_eq_part_list_l in H.
  rewrite H5 in H0. clear H4 H5 H6.

  (* H1中说明了BBnow.(block_num)都大于BBnow.(jump_info).(jump_dest_1)
  * H2中则又说BBnow.(jump_info)在BBnow'_::nil+BBswo_的jmp_dest_set中
  * 但事实上，任何以一个BBnow'_::nil+BBswo_中的Block的num都大于等于BBnow.(block_num)
  * 所以会导出矛盾
  *)

  pose proof BBgen_range_wo_single_soundness_correct (CIf e c1 c2).
  unfold Q_BBgen_range_wo in H4.
  specialize (H4 BBnum (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num) nil BBnow (BBnow'_ :: nil ++ BBswo_)).
  assert (all_gt (BBnum_set (tl (BBnow'_ :: nil ++ BBswo_))) BBnum /\
    all_lt (BBnum_set (tl (BBnow'_ :: nil ++ BBswo_)))
    (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num) /\
    BBjmp_dest_set (BBnow'_ :: nil ++ BBswo_)
     ⊆ section BBnum (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num)). {
      apply H4. apply Hn1. tauto.
      unfold to_result. rewrite H. simpl. reflexivity. apply Hn2.
    }
  clear H4. destruct H5 as [? [? ?]].
  sets_unfold in H6. rename H3 into p1. rename H4 into p2. rename H5 into p3.
  specialize (H6 (jump_dest_1 BBnow.(jump_info))).
  assert (BBjmp_dest_set (BBnow'_ :: nil ++ BBswo_) (jump_dest_1 BBnow.(jump_info))). {
    unfold BBjmp_dest_set. unfold BBjmp_dest_set in H2.
    destruct H2 as [? [? ?]]. exists x. 
    pose proof In_sublist_then_in_list_head BasicBlock x (BBnow'_ :: nil ++ BBswo_) ((cmd_BB_gen (CIf e c1 c2) nil BBnow BBnum).(BBn) :: nil) H2. split.
    apply H2. apply H3.
  }
  pose proof H6 H3 as H6.  rename H6 into H4.
  unfold section in H4. unfold Nat.le in H4. unfold Nat.lt in H4.
  assert ((jump_dest_1 BBnow.(jump_info) < BBnum)%nat). lia.
  assert ((jump_dest_1 BBnow.(jump_info) >= BBnum)%nat). lia.
  lia.
Qed.


(*对于CIf，其BBnow的num肯定和新生成的BBs(去掉最后BBn)的num不交*)
Lemma disjoint_num_prop_wo_last_if:
  forall (BBs BBswo_: list BasicBlock) (BBnow BBnow'_: BasicBlock) (BBnum: nat) (e: expr) (c1 c2: list cmd),
  jump_kind BBnow.(jump_info) = UJump /\ jump_dest_2 BBnow.(jump_info) = None ->
  (BBnow.(block_num) < BBnum)%nat ->
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) =
     BBs ++ BBnow'_ :: BBswo_ -> ~ BBnow.(block_num) ∈ BBnum_set BBswo_.
Proof.
  intros. 
  unfold not. intros. 
  pose proof BBgen_range_single_soundness_correct (CIf e c1 c2) as Q_prop.
  unfold Q_BBgen_range in Q_prop.
  specialize (Q_prop BBnum (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num) BBs BBnow (BBnow'_::nil ++ BBswo_ ++ (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn)::nil)).
  specialize (Q_prop H). 
  assert(t1: (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num) =
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num)). tauto.
  specialize (Q_prop t1).
  assert(t2: to_result (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum) =
  BBs ++ BBnow'_::nil ++ BBswo_ ++ (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil). {
  unfold to_result. rewrite H1. 
  assert((BBs ++ BBnow'_ :: BBswo_)  = BBs ++ BBnow'_ :: nil ++ BBswo_  ).
  {
    simpl. reflexivity.
  }
  rewrite H3. rewrite app_assoc. rewrite <- app_assoc. reflexivity.
  }

  specialize (Q_prop t2 H0). destruct Q_prop as [Q_prop1 [Q_prop2 Q_prop3]].
  simpl in Q_prop1. unfold all_ge in Q_prop1.
  sets_unfold in H2. unfold BBnum_set in H2. destruct H2 as [BB H2]. destruct H2 as [H2 H3].
  specialize (Q_prop1 (BB.(block_num))).
  assert(BBnum_set (BBswo_ ++ {| block_num := BBnum; commands := nil; jump_info := BBnow.(jump_info) |} :: nil)
  BB.(block_num)).
  {
    unfold BBnum_set. exists BB. split. 
    pose proof In_tail_inclusive BBswo_ BB {| block_num := BBnum; commands := nil; jump_info := BBnow.(jump_info) |} H2.
    tauto. tauto.
  }

  specialize (Q_prop1 H4). lia.

Qed.


(*对于CIf，其去掉最后一个BBn的新生成的BBs, 即BBswo_，其所有的num不等于BBnum*)
Lemma neq_ssnum:
  forall (BBs BBswo_: list BasicBlock) (BB BBnow BBnow'_: BasicBlock) (BBnum: nat) (e: expr) (c1 c2: list cmd),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) =
     BBs ++ BBnow'_ :: BBswo_ -> 
     In BB BBswo_ -> 
     jump_kind BBnow.(jump_info) = UJump /\ jump_dest_2 BBnow.(jump_info) = None ->
     (BBnow.(block_num) < BBnum)%nat ->
     (BB.(block_num) <> BBnum).
Proof.
  intros.
  rename H1 into jmp_prop. rename H2 into num_prop.

  pose proof BBgen_range_wo_single_soundness_correct (CIf e c1 c2).
  unfold Q_BBgen_range_wo in H1.
  specialize (H1 BBnum (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num) BBs BBnow (BBnow'_::nil ++ BBswo_)).

  assert(all_gt (BBnum_set (tl (BBnow'_ :: nil ++ BBswo_))) BBnum /\
  all_lt (BBnum_set (tl (BBnow'_ :: nil ++ BBswo_))) (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num) /\
  BBjmp_dest_set (BBnow'_ :: nil ++ BBswo_) ⊆ section BBnum (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(next_block_num)).
  {
    apply H1. apply jmp_prop. reflexivity. tauto. lia.
  }

  destruct H2 as [? [? ?]].

  simpl in H2. unfold all_gt in H2. specialize H2 with (BB.(block_num)).
  assert(BBnum_set BBswo_ BB.(block_num)).
  {
    unfold BBnum_set. exists BB. split. tauto. tauto.
  }

  specialize (H2 H5). lia.
Qed.