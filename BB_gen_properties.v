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

(*BUG emm这里定义的时候其实应该加一个括号才对，但是emm，不改似乎不会影响证明*)
Definition all_ge (natset: nat -> Prop)(num: nat): Prop :=
    (forall n, natset n -> Nat.le num n).
  
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


(* TODO 证明======================================================================================================================================== *)


Definition Q_inherit_not_jmp_to_self (c: cmd): Prop :=
  forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
    (BBnow.(block_num) <> jump_dest_1 BBnow.(jump_info)) ->
    (cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num) <> jump_dest_1 (cmd_BB_gen c BBs BBnow BBnum).(BBn).(jump_info).

Definition P_inherit_not_jmp_to_self(cmds: list cmd): Prop :=
  forall (BBs: list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
  (BBnow.(block_num) <> jump_dest_1 BBnow.(jump_info)) ->
  (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BBn).(block_num) <> jump_dest_1 (list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BBn).(jump_info).

Lemma Q_inherit_not_jmp_to_self_asgn: 
  forall  (x: var_name) (e: expr),
  Q_inherit_not_jmp_to_self (CAsgn x e).
Proof. 

Admitted. (*yz*)

Lemma Q_inherit_not_jmp_to_self_if:
  forall  (e: expr) (c1: list cmd) (c2: list cmd),
  P_inherit_not_jmp_to_self (c1) -> P_inherit_not_jmp_to_self (c2) ->
  Q_inherit_not_jmp_to_self (CIf e c1 c2).
Proof.
Admitted. (*bh*)

Lemma Q_inherit_not_jmp_to_self_while:
  forall  (e: expr) (c1: list cmd) (c2: list cmd),
  P_inherit_not_jmp_to_self (c1) -> P_inherit_not_jmp_to_self (c2) ->
  Q_inherit_not_jmp_to_self (CWhile c1 e c2).
Proof.
Admitted.  (*we DONT CARE while*)

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
Admitted.  (*yz*)

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
    (BBnow.(block_num) <> jump_dest_1 BBnow.(jump_info)) ->
    (cmd_BB_gen c BBs BBnow BBnum).(BBn).(block_num) <> jump_dest_1 (cmd_BB_gen c BBs BBnow BBnum).(BBn).(jump_info).
Proof.
  pose proof inherit_not_jmp_to_self_soundness_correct.
  intros.
  unfold Q_inherit_not_jmp_to_self in H.
  specialize (H c BBs BBnow BBnum H0). tauto.
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

(*TODO ! 这里num之间的关系要整理一下，说不定有些定理是没有必要的*)
(*如果传入的BBnow的num小于BBnum（似乎不需要用到），那么BBnum的num小于等于next_block_num ====================================================================================================== *)
(*要写成互递归了，因为要拿到c1中间的结果进行比较*)

(*如果BBnow的num小于分配的num，那么总有最后所在的BB的num小于下一个分配的num*)

Definition Q_inherit_lt_num_prop_mutual (c: cmd): Prop :=
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat),
    (lt BBnow.(block_num) BBnum) -> le BBnum (cmd_BB_gen c BBs BBnow BBnum).(next_block_num).

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
              block_num := S BBnum;
              commands := nil;
              jump_info := {|
                          jump_kind := UJump;
                          jump_dest_1 := S (S BBnum);
                          jump_dest_2 := None;
                          jump_condition := None |} |}) as BBnow_else.
  remember ({|
              block_num := BBnum;
              commands := nil;
              jump_info := {|
                            jump_kind := UJump;
                            jump_dest_1 := S (S BBnum);
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

  assert ((BBnum' <= (list_cmd_BB_gen cmd_BB_gen c2 nil BBnow_else BBnum').(next_block_num))%nat). {
    apply H0. subst BBnow_else. simpl. clear H0. admit.
  }
  lia.
Admitted.


Lemma Q_inherit_lt_num_prop_mutual_while:
  forall (e: expr) (c1: list cmd) (c2: list cmd),
    P_inherit_lt_num_prop_mutual c1 -> P_inherit_lt_num_prop_mutual c2 -> Q_inherit_lt_num_prop_mutual (CWhile c1 e c2).
Proof.
Admitted. (*DONT CARE for WHILE*)

Lemma P_inherit_lt_num_prop_mutual_nil:
  P_inherit_lt_num_prop_mutual nil.
Proof.
  Admitted. (*yz*)

Lemma P_inherit_lt_num_prop_mutual_cons:
  forall (c: cmd) (cmds: list cmd),
    Q_inherit_lt_num_prop_mutual c ->
    P_inherit_lt_num_prop_mutual cmds ->
    P_inherit_lt_num_prop_mutual (c :: cmds).
Proof.
  Admitted. (*bh*)

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
Admitted.

Lemma bbnum_le_next_num_single_cmd:
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: cmd),
    (lt BBnow.(block_num) BBnum) -> le BBnum (cmd_BB_gen c BBs BBnow BBnum).(next_block_num).
Proof.
  intros. destruct c.
  - simpl. lia.
  - cbn [cmd_BB_gen]. simpl. admit.
  - admit.
Admitted.

Lemma bbnum_le_next_num:
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: list cmd),
    (lt BBnow.(block_num) BBnum) -> le BBnum (list_cmd_BB_gen cmd_BB_gen c BBs BBnow BBnum).(next_block_num).
Proof.
  intros. induction c.
  - simpl. lia.
  - cbn [list_cmd_BB_gen].
    unfold list_cmd_BB_gen.
    destruct a.
    + simpl. admit.
Admitted. (*TODO @LYZ*)


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


(*END:  ====================================================================================================== *)


(*如果生成的res.(BasicBlocks) ++ res.(BBn) :: nil中仅有一个元素，那么BBnum等于next_block_num ===================================================================================================*)

Lemma bbnum_eq_next_num_single_cmd:
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: cmd),
    let res := (cmd_BB_gen c BBs BBnow BBnum) in
    (lt BBnow.(block_num) BBnum) -> (tl (res.(BasicBlocks) ++ res.(BBn) :: nil)) = nil -> BBnum = res.(next_block_num).
Proof.
  intros. destruct c.
  - simpl. lia.
  - cbn [cmd_BB_gen]. simpl. admit.
  - admit.
Admitted. (*TODO yz *)

Lemma bbnum_eq_next_num:
  forall (BBs : list BasicBlock) (BBnow : BasicBlock) (BBnum : nat) (c: list cmd),
    let res := (list_cmd_BB_gen cmd_BB_gen c BBs BBnow BBnum) in
    (lt BBnow.(block_num) BBnum) -> (tl (res.(BasicBlocks) ++ res.(BBn) :: nil)) = nil -> BBnum = res.(next_block_num).
Proof.
  intros. induction c.
  - cbn [list_cmd_BB_gen].
    simpl. lia.
  -
    unfold list_cmd_BB_gen.
    destruct a.
    + simpl. admit.
Admitted. (*TODO yz *)

(* END ===================================================================================================*)


(*START：列表集合的一些性质 ==================================================================================================================================================================================================================== *)

Lemma head_eq_prop:
  forall (A: Type) (l1 l2: list A) (a b: A),
  a::l1 = b::l2 -> a = b.
Proof.
  intros. inversion H. reflexivity.
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
                jump_dest_1 := BBnum;
                jump_dest_2 := Some (S BBnum);
                jump_condition := Some e |} |}) as BBnow_.
  remember ({|
            block_num := BBnum;
            commands := nil;
            jump_info := {|
                         jump_kind := UJump;
                         jump_dest_1 := S (S BBnum);
                         jump_dest_2 := None;
                         jump_condition := None |} |}) as BBnow_then.
  remember ({|
            block_num := S BBnum;
            commands := nil;
            jump_info := {|
                         jump_kind := UJump;
                         jump_dest_1 := S (S BBnum);
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



(*TODO IMPORTANT：第一个Block的num就是BBnow的blocknum *)
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

(*END: BBgen Head =========================================================================================================================================================================================*)


(*对于CIf而言，其nextblocknum等于else分支得到的nextblocknum*)
Lemma CIf_next_block_num_eq_else_next_block_num:
  forall (e: expr) (c1 c2: list cmd) (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum: nat),
    let BB_now_then := 
      {|
      block_num := BBnum;
      commands := nil;
      jump_info :=
        {|
          jump_kind := UJump;
          jump_dest_1 := S (S BBnum);
          jump_dest_2 := None;
          jump_condition := None;
        |}
      |} in
    let else_start_num := (list_cmd_BB_gen cmd_BB_gen c1 nil BB_now_then (S(S (S BBnum)))).(next_block_num) in
    let BB_now_else := 
      {|
      block_num := S BBnum;
      commands := nil;
      jump_info :=
        {|
          jump_kind := UJump;
          jump_dest_1 := S (S BBnum);
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


(*Start: Main =============================================================================================================================================================================================*)

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

  assert (c1_aux2 : then_end_num = (list_cmd_BB_gen cmd_BB_gen c1 BBs BB_then_now then_start_num).(next_block_num)). subst then_end_num. subst then_res. pose proof add_BBs_in_generation_retains_next_block_num c1 BBs BB_then_now then_start_num. apply H.

  assert (c1_aux3 : (to_result (list_cmd_BB_gen cmd_BB_gen c1 BBs BB_then_now then_start_num) = BBs ++ then_delta)). pose proof add_BBs_in_generation_reserves_BB c1 BBs BB_then_now then_start_num. unfold to_result in H. unfold to_result. subst then_delta. subst then_res. apply H. 

  specialize (c1_prop c1_aux1 c1_aux2 c1_aux3).
  clear c1_aux1 c1_aux2 c1_aux3.
  
  specialize (c2_prop then_end_num endnum nil BB_else_now else_delta).
  assert (c2_aux1 : (BB_else_now.(jump_info).(jump_kind) = UJump /\ BB_else_now.(jump_info).(jump_dest_2) = None)). tauto.

  assert (c2_aux2 : endnum = (list_cmd_BB_gen cmd_BB_gen c2 nil BB_else_now then_end_num).(next_block_num)). {
    pose proof CIf_next_block_num_eq_else_next_block_num e c1 c2 BBs BBnow startnum. subst endnum. tauto.
  }

  assert (c2_aux3 : (to_result (list_cmd_BB_gen cmd_BB_gen c2 nil BB_else_now then_end_num) = else_delta)). subst else_delta. subst else_res. unfold to_result. pose proof add_BBs_in_generation_reserves_BB c2 nil BB_else_now then_end_num. unfold to_result in H. apply H.
  specialize (c2_prop c2_aux1 c2_aux2 c2_aux3).
  clear c2_aux1 c2_aux3.

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
Admitted. (*DONT CARE, 老师说while分支都不管*)

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
  unfold P_BBgen_range. intros. simpl in H0. unfold to_result in H1. simpl in H1. 
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
  unfold P_BBgen_range.
  intros.
  
Admitted. (* yz *)

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



(* BBgen If 的一些性质 ================================================================================= *)


(*! IMPORTANT 对于if而言，新产生的BBs中的第一个，就是BBthen，那么自然有其blocknum的性质*)
Lemma if_head_prop:
  forall (e: expr) (c1 c2: list cmd)(BBswo_ BBs: list BasicBlock)(BBnow BBnow'_: BasicBlock)(BBnum: nat),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) = BBs ++ BBnow'_ :: BBswo_
  ->
  (hd empty_block (BBswo_)).(block_num) = BBnum.
Proof.
  intros.
  cbn [cmd_BB_gen] in H. simpl in H.
  remember ({|
  block_num := BBnow.(block_num);
  commands := BBnow.(cmd);
  jump_info :=
    {|
      jump_kind := CJump;
      jump_dest_1 := BBnum;
      jump_dest_2 := Some (S BBnum);
      jump_condition := Some e
    |}
|}
:: to_result
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
        |} (S (S (S BBnum)))) ++
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
           |} (S (S (S BBnum)))).(next_block_num))) as BBswo_2.
  pose proof cut_eq_part_list_l BasicBlock BBs BBswo_2 (BBnow'_ :: BBswo_) H.
  rewrite HeqBBswo_2 in H0. inversion H0. rewrite H3. clear H2.
  rename H3 into key. unfold to_result in key. 
  remember (((list_cmd_BB_gen cmd_BB_gen c1 nil
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
  |} (S (S (S BBnum)))).(BasicBlocks))) as e0.

  remember ((list_cmd_BB_gen cmd_BB_gen c1 nil
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
  |} (S (S (S BBnum)))).(BBn) :: nil) as e1.

  remember ((list_cmd_BB_gen cmd_BB_gen c2 nil
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
     |} (S (S (S BBnum)))).(next_block_num)).(BasicBlocks) ++
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
     |} (S (S (S BBnum)))).(next_block_num)).(BBn) :: nil) as e2.
    
    pose proof hd_A_and_B_is_hd_A_if_A_not_nil (e0 ++ e1) e2 as hd_position.
    assert (e0_not_nil: (e0 ++ e1) <> nil).
    {
      (*对c1是否为空进行分类讨论, 但是可能有点麻烦*)
      pose proof classic (e0 = nil) as He0_nil. destruct He0_nil as [He0_nil | He0_nnil].
      - rewrite He0_nil. rewrite app_nil_l. rewrite Heqe1. unfold not. intros.
        inversion H1.
      - unfold not. intros.
        
    }
    pose proof hd_position e0_not_nil as hd_position.
Admitted.


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
Admitted. (*TODO bh*)

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
Admitted. (*TODO bh*)


(*如果cmd是CIf，那么新生成的BBs的最后一个Block，也就是BBnext，它的cmd为空*)
Lemma if_cmdgen_prop1:
  forall (e: expr) (c1 c2: list cmd) (BBs: list BasicBlock)(BBnow: BasicBlock)(BBnum : nat),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn).(cmd) = nil.
Proof.
  intros.
  cbn [cmd_BB_gen]. simpl. reflexivity.
Qed.

(*如果cmd是CIf，那么新生成的BBs的最后一个就是BBnext，它的num就是S S BBnum*)
Lemma if_BBn_num_prop:
  forall (e: expr) (c1 c2: list cmd) (BBs: list BasicBlock)(BBnow: BasicBlock)(BBnum: nat),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn).(block_num) = S (S BBnum).
Proof. 
  intros.
  cbn [cmd_BB_gen]. simpl. reflexivity.
Qed.



(* ================================================================================= *)


(* Jmp Info的继承性质  ============================================================================================================ *)

(*Jmp Info是会被继承下去的！TODO Maybe EASY, 递归就好*)
Lemma JmpInfo_inherit_for_list:
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum: nat) (cmds: list cmd),
  ((list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum).(BBn)).(jump_info) = BBnow.(jump_info).
Proof.
  (*bh*)
Admitted.


Lemma JmpInfo_inherit:
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum: nat) (c: cmd),
  ((cmd_BB_gen c BBs BBnow BBnum).(BBn)).(jump_info) = BBnow.(jump_info).
Proof.
  destruct c. 
  + reflexivity.
  + cbn [cmd_BB_gen]. simpl. reflexivity.
  + cbn [cmd_BB_gen]. simpl. reflexivity.
Qed.

(* ============================================================================================================ *)

(*特殊符号性质：BBnow的传入的endinfo其实不能算在BBnumset里, 这个定义的目的是让这个num仅仅只能通过“传递”拿到，而不可能和其他任何num重叠。*)
(*当然，我们已经意识到，这个条件其实太强了；但是也很好地帮我们解决了一些逻辑上显然的情况*)
Definition not_eq_to_any_BBnum (end_info: nat) := 
  forall (n: nat), end_info <> n.


(*如果BBnow的endinfo满足特殊符号性质，那么对于任何新生成的的一串BB（BBs)，它只能在BBs的最后一个Block里，也就是(res.(BBn)的jmpdest里*)
Lemma unique_endinfo_if:
  forall (BBs BBswo_ BBs'_: list BasicBlock)  (e: expr) (c1 c2: list cmd) (BBnow BBnow'_: BasicBlock) (BBnum: nat),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) = BBs ++ BBnow'_ :: BBswo_ ->
  BBs'_ =  BBswo_ ++ (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BBn) :: nil ->
  not_eq_to_any_BBnum (BBnow.(jump_info).(jump_dest_1)) ->
  ~ (BBnow.(jump_info).(jump_dest_1) ∈ BBjmp_dest_set (BBnow'_ :: nil ++ BBswo_)).
Proof.
  intros.
  unfold not_eq_to_any_BBnum in H1.
(*TODO bh*)
Admitted.


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
  assert(BBnum_set (BBswo_ ++ {| block_num := S (S BBnum); commands := nil; jump_info := BBnow.(jump_info) |} :: nil)
  BB.(block_num)).
  {
    unfold BBnum_set. exists BB. split. 
    pose proof In_tail_inclusive BBswo_ BB {| block_num := S (S BBnum); commands := nil; jump_info := BBnow.(jump_info) |} H2.
    tauto. tauto.
  }

  specialize (Q_prop1 H4). lia.

Qed.


(*对于CIf，其去掉最后一个BBn的新生成的BBs, 即BBswo_，其所有的num不等于SS BBnum*)
Lemma neq_ssnum:
  forall (BBs BBswo_: list BasicBlock) (BB BBnow BBnow'_: BasicBlock) (BBnum: nat) (e: expr) (c1 c2: list cmd),
  (cmd_BB_gen (CIf e c1 c2) BBs BBnow BBnum).(BasicBlocks) =
     BBs ++ BBnow'_ :: BBswo_ -> 
     In BB BBswo_ -> (BB.(block_num) <> (S (S BBnum))).
Proof.
Admitted. (*TODO yz*)