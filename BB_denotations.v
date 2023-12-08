Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. 
Import SetsNotation.
Require Import compcert.lib.Integers.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.
Require Import Main.grammer.
Require Import Main.cmd_denotations.
Require Import Main.BB_generation.
Require Import Coq.Lists.List.
Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.

Record BB_state: Type := {
  BB_num: nat;
  st: state
}.

Module BDenote.
Record BDenote: Type := {
  Bnrm: BB_state -> BB_state -> Prop;
  Berr: BB_state -> Prop;
  Binf: BB_state -> Prop
}.
End BDenote.

Import BDenote.

Definition empty_sem : BDenote := {|
  Bnrm := ∅;
  Berr := ∅;
  Binf := ∅
|}.

Definition get_state (bs: BB_state): state := bs.(st).



Definition test_true_jmp (D: EDenote):
  state -> Prop :=
    (fun s => exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false_jmp (D: EDenote):
  state -> Prop :=
    (fun s => D.(nrm) s (Int64.repr 0)).

Definition ujmp_sem (jum_dist: nat): BDenote :=
  {|
    Bnrm := fun (bs1: BB_state) (bs2 :BB_state) =>
      bs1.(st) = bs2.(st) /\ bs2.(BB_num) = jum_dist;
    Berr := ∅;
    Binf := ∅;
  |}.

Definition cjmp_sem (jmp_dist1: nat) (jmp_dist2: nat) (D: EDenote) : BDenote :=
  {|
    Bnrm := fun bs1 bs2 => ((bs1.(st) = bs2.(st)) /\ 
            ((bs2.(BB_num) = jmp_dist1) /\ (test_true_jmp D bs1.(st)) \/ ((bs2.(BB_num) = jmp_dist2) /\ (test_false_jmp D bs1.(st)))));
    Berr := ∅; (* Ignore err cases now *)
    Binf := ∅;
  |}.


Definition jmp_sem (jmp_dist1: nat) (jmp_dist2: option nat)(D: option EDenote) :BDenote :=
  match D with 
  | None => ujmp_sem jmp_dist1 (* No expr *)
  | Some D => match jmp_dist2 with
              | None => ujmp_sem jmp_dist1
              | Some jmp_dist2 => cjmp_sem jmp_dist1 jmp_dist2 D
              end
  end.

Definition BAsgn_sem (x: var_name) (e:EDenote) : BDenote := {|
  Bnrm := fun (bs1:BB_state) (bs2:BB_state) => 
     exists i,
     (e.(nrm) bs1.(st) i) /\  (bs2.(st) x = Vint i) /\ (forall y, x <> y -> bs1.(st) y = bs2.(st) y);
  Berr := fun(bs1:BB_state) => bs1.(st) ∈ e.(err);
  Binf := ∅;
|}.


Definition BJump_sem (jmp_dist1: nat) (jmp_dist2: option nat) (D: option EDenote) : BDenote := {|
  Bnrm := fun bs1 bs2 => 
    exists i,
      bs1.(st) = i.(st) /\ (jmp_sem jmp_dist1 jmp_dist2 D).(Bnrm) i bs2;
  Berr := ∅;
  Binf := ∅;
|}.

(** Now we are certain that BB only contains BAsgn and BJump cmds *)
(* The sementics for a list of BAsgn *)
Print BB_cmd.


Definition BAsgn_denote (BAsgn_cmd: BB_cmd) : BDenote :=   
  let x := BAsgn_cmd.(X) in 
  let e := BAsgn_cmd.(E) in
 {|
  Bnrm :=  fun (bs1: BB_state) (bs2: BB_state) => (BAsgn_sem x (eval_expr e)).(Bnrm) bs1 bs2 /\ (bs1.(BB_num) = bs2.(BB_num)); 
  Berr := (BAsgn_sem x (eval_expr e)).(Berr);
  Binf := ∅;
|}.



Fixpoint BAsgn_list_sem (BAsgn_list: list BB_cmd) : BDenote := 
match BAsgn_list with 
 | BAsgn_cmd :: tl =>
   {|   
      Bnrm := (BAsgn_denote BAsgn_cmd).(Bnrm) ∘ (BAsgn_list_sem tl).(Bnrm);
      Berr := (BAsgn_denote BAsgn_cmd).(Berr) ∪ (BAsgn_denote BAsgn_cmd).(Bnrm) ∘ (BAsgn_list_sem tl).(Berr);
      Binf := ∅;
  |}
  | _ =>
  {|
      Bnrm := Rels.id;
      Berr := ∅;
      Binf := ∅;
  |}
end.

Definition eval_cond_expr (e: option expr): option EDenote :=
  match e with
  | Some (EBinop op e1 e2) =>
      Some (binop_sem op (element_sem (e1)) (element_sem (e2)))
  | Some (EUnop op e1) =>
      Some (unop_sem op (element_sem (e1)))
  | None => None
  end.


(* Combine list of BAsgn and the final BJump *)
Definition BB_sem (BB: BasicBlock): BDenote := {| 
  Bnrm := 
    let jmp_dist1 := BB.(jump_info).(jump_dist_1) in
    let jmp_dist2 := BB.(jump_info).(jump_dist_2) in
    let jmp_cond := BB.(jump_info).(jump_condition) in
    (BAsgn_list_sem BB.(cmd)).(Bnrm) ∘ (BJump_sem jmp_dist1 jmp_dist2 (eval_cond_expr jmp_cond)).(Bnrm); 
  Berr := ∅;
  Binf := ∅;
|}.


(* Combine the single_step_stem to form the denotation for BB_list_sem.
   Not certain about its correctness  *)
Fixpoint BB_list_sem (BBs: list BasicBlock): BDenote := {|
  Bnrm := 
    match BBs with 
    | BB :: tl => (BB_sem BB).(Bnrm) ∘ (BB_list_sem tl).(Bnrm)
    | _ => Rels.id
    end;
  Berr := ∅;
  Binf := ∅;
|}.


(* Construct the denotation for the original cmds, should be in cmd_denotations.v 
* For debugging convenience, I have put it here
*)

(* The definition follows similar approach as BB_gen for mutually recursive cases *)
Section cmd_list_sem.

Variable cmd_sem : cmd -> CDenote.

Fixpoint cmd_list_sem (cmd_list: list cmd): CDenote := {|
  nrm := 
    match cmd_list with
    | cmd :: tl => (cmd_sem cmd).(nrm) ∘ (cmd_list_sem tl).(nrm)
    | _ => Rels.id
    end;
  err := ∅;
  inf := ∅;
|}.

End cmd_list_sem.

(* I have used while_sem from cmd_denotations.v, don't know if it is correct *)
Fixpoint cmd_sem (cmd: cmd): CDenote := {|
  nrm := 
    match cmd with 
    | CAsgn x e => (asgn_sem x (eval_expr e)).(nrm)
    | CIf e c1 c2 => (if_sem (eval_expr e) (cmd_list_sem cmd_sem c1) (cmd_list_sem cmd_sem c2)).(nrm)
    | CWhile pre e body => (while_sem (eval_expr e) (cmd_list_sem cmd_sem body) (cmd_list_sem cmd_sem pre)).(nrm)
    end;
  err := ∅;
  inf := ∅;
|}.

Definition state_to_BBstate (s: state): BB_state :=
  {| BB_num := 0; st := s |}.

(* The following are the equivalence between BB_state and state *)


(* The following are preparations for the final theorem *)


Record BCequiv (B: BDenote) (C: CDenote) (startBB endBB: nat): Prop := {
  nrm_cequiv: (fun s1 s2 => exists bs1 bs2, B.(Bnrm) bs1 bs2 /\ bs1.(st) = s1 /\ bs2.(st) = s2 /\ bs1.(BB_num) = startBB /\ bs2.(BB_num) = endBB) == C.(nrm);
  err_cequiv: (fun s => exists bs, B.(Berr) bs /\ bs.(st) = s) == C.(err); 
  inf_cequiv: (fun s => exists bs, B.(Binf) bs /\ bs.(st) = s) == C.(inf);
}.

(* 
Notation "c1 '~=~' c2" := (cequiv c1 c2)
  (at level 69, only printing, no associativity). *)


Definition construct_BB_state (s: state) (BB_num: nat): BB_state := 
  {| BB_num := BB_num; st := s |}.


(* TODO The ultimate goal of the task, incomplete *)
(* Given a list of cmds, we could derive many cmd sem, multiply them together to get (s1, s2) *)
(* Given a list of cmds, by using BB_gen cmds, we could generate a list of BBs, BB1, BB2, .. BBn, we have to prove: *)
(* (s1, s2) \in (BB1.st, BB2.st) *)


(* Theorem BB_gen_sound (cmds: list cmd):
  forall s1 s2, 
    let BBs_sem := BB_list_sem (BB_gen cmds) in

    let BB_st := {| BB_num := 0; st := s1 |} in

    (BB_st ∘ BBs_sem.(Bnrm)).(st) = s2 ∘ (cmd_list_sem cmd_sem cmds).(nrm). *)

Check Rels_concat_id_l.

Check Rels_concat_id_r.


(* Theorem BB_gen_sound : 
  forall (cmds: list cmd),
    let BBs_sem := BB_list_sem (BB_gen cmds) in
    let cmds_sem := (cmd_list_sem cmd_sem cmds) in
    BCequiv BBs_sem cmds_sem 10 (9 + length(BB_gen cmds)).
Proof.
  intros.
  induction cmds;split;sets_unfold; intros; split; intros.
  * destruct H as [bs1 [bs2 [Hnrm [? [? []]]]]].
    - unfold cmds_sem; unfold cmd_list_sem; simpl.
      unfold BB_gen in H2;simpl in H2.
      unfold BBs_sem in Hnrm; unfold BB_gen in Hnrm.
      simpl in Hnrm.
      Sets_unfold in Hnrm.
      destruct Hnrm as (? & (? & ? & ?) & ? ).
      destruct H4 as [? [? []]].
      assert (bs1 = bs2). {
        destruct bs1,bs2.
        simpl in H, H0, H1, H2.
        rewrite H1, H2; simpl.
        rewrite H6 in H4.
        rewrite <- H3 in H4. rewrite H5 in H4. simpl in H4.
        rewrite H4.
        reflexivity.
      }
      subst.
      sets_unfold.
      reflexivity.
  * admit.
  * admit.
  * admit.
Admitted.  
(* Print cmd. *)

Print BB_state. *)



Ltac my_destruct H :=
  match type of H with 
  | exists _, _ => destruct H as [? H]; my_destruct H 
  | _ /\ _ => let H1:= fresh "H" in 
              destruct H as [H H1];my_destruct H; my_destruct H1
  | _ => idtac 
  end.



Definition start_with_Asgn (cmds: list cmd) : Prop :=
  match cmds with
  | CAsgn _ _ :: _ => True
  | _ => False
  end.

Lemma BAsgn_sound:
  forall (x: var_name) (e: expr) (BBs: list BasicBlock) (BB_now: BasicBlock) (BB_num: nat),
  let BB_last := (cmd_BB_gen (CAsgn x e) BBs BB_now BB_num).(BBn) in
  let BAsgn_cmd := {| X := x; E:= e |} in
  let BB_Asgn := {|
    block_num := BB_last.(block_num);
    commands := BAsgn_cmd :: nil;
    jump_info := BB_last.(jump_info);
  |} in

  BCequiv (BB_list_sem (BB_Asgn :: nil)) (cmd_sem (CAsgn x e)) BB_num BB_last.(block_num).
Proof.
  Admitted.

Lemma BIf_BWhile_sound:
  forall (c: cmd) (BBs: list BasicBlock) (BB_now: BasicBlock) (BB_num: nat),
  let BBs_new := (cmd_BB_gen c BBs BB_now BB_num).(BasicBlocks) in
  let BB_last := (cmd_BB_gen c BBs BB_now BB_num).(BBn) in
  let BB_result := BBs_new ++ (BB_last :: nil) in

  BCequiv (BB_list_sem BB_result) (cmd_sem c) BB_num BB_last.(block_num).

Proof.
Admitted.


Definition is_CAsgn (cmd: cmd) : bool :=
  match cmd with
  | CAsgn _ _ => true
  | _ => false
  end.

(* Lemma BB_cmd_sound :
  forall (c: cmd) (BBs: list BasicBlock) (BB_now: BasicBlock) (BB_num: nat),
  is_CAsgn c = false -> BIf_BWhile_sound c BBs BB_now BB_num.
Proof.
  Admitted.  *)

Lemma BB_list_cmd_sound:
  forall (cmds: list cmd) (BBs: list BasicBlock) (BB_now: BasicBlock) (BB_num: nat),
    let BBs_new := (list_cmd_BB_gen cmd_BB_gen cmds BBs BB_now BB_num).(BasicBlocks) in
    let BB_last := (list_cmd_BB_gen cmd_BB_gen cmds BBs BB_now BB_num).(BBn) in
    let BB_result := BBs_new ++ (BB_last :: nil) in
    BCequiv (BB_list_sem BB_result) (cmd_list_sem cmd_sem cmds) BB_num BB_last.(block_num).
Proof.
  intros.
  induction cmds.
  - admit.
  - admit.
Admitted.


(*Parameters:
  cmds: list cmd, 
  BBs: list of Basic Blocks which have been already generated
  BBnow: the current BB
  BBs': the BBs that will be generated by the current BB
  BBcmds': list BB_cmd, new BB_cmds to be coped in Asgn case
  这个写法还有问题,没有考虑到对Asgn的处理,Asgn的情况；按照asgn的处理,其实BBs'应该是一个空的list)我们还在当前的BB里,这个BB之后可能还会被用到）,这种情况下,sem (BBs') = sem(cmd) 是不对的
  我感觉还是需要一个单步语义等价,类似那种cmd_gen和list_cmd_gen的关系, 不能直接用BCequiv, 否则我感觉对于以asgn指令起始cmds的情况,这个BCequiv是不成立的, 那就不能继续推下去才对。
  tricky的点在于,这种情况下我的BB还留在原地不动,cmd其实已经往前走了一个了,再用(BB_list_sem BBs') (cmd_list_sem cmd_sem cmds) 就有些不对劲。鹏翔你起来的的时候再看看吧,我实在没想出来怎么写了,熬夜真没脑子。
  多写命题来分类。
  *)
Lemma inductive_equiv :
forall (cmds: list cmd) (BBs BBs': list BasicBlock)(BBcmds': list BB_cmd)(BBnow BBnew: BasicBlock) (BBnum BBNextnum: nat) ,
  start_with_Asgn (cmds) -> list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum = {| BasicBlocks := BBs ++ BBs'; BBn:= BBnew ; next_block_num := BBNextnum |} 
  -> BCequiv (BB_list_sem BBs') (cmd_list_sem cmd_sem cmds) BBnum BBNextnum 
  \/ 
  ~start_with_Asgn (cmds) -> (**not start with asgn*)
  list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum = {| BasicBlocks := BBs ++ BBs'; BBn:= BBnew ; next_block_num := BBNextnum |} ->
  BCequiv (BB_list_sem BBs') (cmd_list_sem cmd_sem cmds) BBnum BBNextnum.
Proof.
  intros.
  induction cmds.
  - admit.
  - destruct IHcmds as [? ?].
  Admitted.

Fixpoint get_head_asgn (cmds: list cmd) : list cmd :=
  match cmds with
  | CAsgn x e :: tl => CAsgn x e :: (get_head_asgn tl)
  | _ => nil
  end.

Fixpoint get_tail_others (cmds: list cmd) : list cmd :=
  match cmds with
  | CAsgn x e :: tl => get_tail_others tl
  | CIf e c1 c2 :: tl => CIf e c1 c2 :: tl
  | CWhile pre e body :: tl => CWhile pre e body :: tl
  | nil => nil
  end.

(* 判断 cmds 是不是一串 CAsgn*)
Fixpoint is_seq_cmds (cmds : list cmd) : bool :=
  match cmds with
  | nil => true
  | CAsgn x e :: tl => is_seq_cmds tl
  | CIf e c1 c2 :: tl => false
  | CWhile pre e body :: tl => false

  end.

(* Prove that the CAsgn commands in the front has the same sementics as corresponding list cmds *)
(* 考虑 if和while刚开始，进入那个BB_next里，或者是cmds的刚开始 *)
Lemma head_CAsgn_sound:
  forall (cmds: list cmd) (BBs BBs': list BasicBlock)(BBcmds': list BB_cmd)(BBnow BBnew: BasicBlock) (BBnum BBNextnum: nat) ,
    is_seq_cmds(cmds) = true -> list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum = {| BasicBlocks := BBs ++ BBs'; BBn:= BBnew ; next_block_num := BBNextnum |} 
    -> BCequiv (BB_list_sem (BBnew :: nil)) (cmd_list_sem cmd_sem cmds) BBnum BBNextnum.
Proof.
Admitted.

Lemma CIf_Cwhile_sound:
  forall (cmds: list cmd) (BBs BBs': list BasicBlock)(BBcmds': list BB_cmd)(BBnow BBnew: BasicBlock) (BBnum BBNextnum: nat) ,
  is_seq_cmds(cmds) = false -> list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum = {| BasicBlocks := BBs ++ BBs'; BBn:= BBnew ; next_block_num := BBNextnum |} 
  -> BCequiv (BB_list_sem BBs') (cmd_list_sem cmd_sem cmds) BBnum BBNextnum.
Proof.
Admitted.

(* Lemma all_sound:
  forall (cmds: list cmd) (BBs BBs': list BasicBlock)(BBcmds': list BB_cmd)(BBnow BBnew: BasicBlock) (BBnum BBNextnum: nat),
  let

 *)

 (* ! Return a list to avoid option *)
Definition CAsgn_BAsgn (c: cmd): list BB_cmd := 
  match c with 
  | CAsgn x e =>  {| X := x ; E := e|} :: nil
  | _ => nil
  end.


(* Consider: we already use cmds to generate BBs, then we add a new cmd*)
Lemma single_cmd_BB_sound:
  forall (cmds: list cmd) (c: cmd) (BBs: list BasicBlock) (BB_now: BasicBlock) (BB_num: nat),

  (* Suppose the cmds semantics and c semantics are equivalent *)
  let BBs' := (list_cmd_BB_gen cmd_BB_gen cmds BBs BB_now BB_num).(BasicBlocks) in

  (* This is BB_now in our previous discussion *)
  let BB_now' := (list_cmd_BB_gen cmd_BB_gen cmds BBs BB_now BB_num).(BBn) in

  let BB_mid_num := (list_cmd_BB_gen cmd_BB_gen cmds BBs BB_now BB_num).(next_block_num) in

  (* Used for CAsgn case *)
  let BB_now'' := {|
      block_num := BB_now'.(block_num); 
      commands := BB_now'.(commands) ++ (CAsgn_BAsgn c); 
      jump_info := BB_now'.(jump_info);
    |} in

  (* ! Used for while case, check the input *)
  let BBs'' := (cmd_BB_gen c BBs' BB_now' BB_num).(BasicBlocks) in

  let BB_final_num := (cmd_BB_gen c BBs' BB_now' BB_num).(next_block_num) in 

  (* Two conditions, CAsgn/CIf-CWhile *)
  (* list sem same, single cmd sem same -> list::cmd sem same *)
  (* BB_mid_num is the final block num *)
  ((is_CAsgn c) = true 
  -> BCequiv (BB_list_sem (BBs' ++ (BB_now' :: nil))) (cmd_list_sem cmd_sem cmds) BB_num BB_mid_num 
  -> BCequiv (BB_sem BB_now'') (cmd_sem c) BB_mid_num BB_mid_num 
  -> BCequiv (BB_list_sem (BBs' ++ (BB_now'' :: nil))) (cmd_list_sem cmd_sem (cmds ++ (c :: nil))) BB_num BB_mid_num) /\
  
  ((is_CAsgn c) = false
  -> BCequiv (BB_list_sem (BBs' ++ (BB_now' :: nil))) (cmd_list_sem cmd_sem cmds) BB_num BB_mid_num
  -> BCequiv (BB_list_sem BBs'') (cmd_sem c) BB_mid_num BB_final_num 
  (* Here we use BB_now rather than BB_now', the notations follow the blackboard, so BB_now is actually BB_now'  *)
  -> BCequiv (BB_list_sem (BBs ++ (BB_now' :: BBs'))) (cmd_list_sem cmd_sem (cmds ++ (c :: nil))) BB_num BB_final_num).
Proof.
  intros.
  split.
  + intros.
   


Theorem BB_sound:
  forall (cmds: list cmd) (BBs BBs': list BasicBlock) (BBcmds': list BB_cmd) (BBnow: BasicBlock) (BBnum BBNextnum: nat) ,
    let BBnow' := {| block_num := BBnow.(block_num); commands := BBnow.(commands) ++ BBcmds'; jump_info := BBnow.(jump_info); |} in

    list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum = {| BasicBlocks := BBs ++ (BBnow' :: nil) ++ BBs'; BBn:= EmptyBlock ; next_block_num := BBNextnum |} 

    -> BCequiv (BB_list_sem (BBs ++ (BBnow' :: nil) ++ BBs')) (cmd_list_sem cmd_sem cmds) BBnum BBNextnum.
Proof.
  intros.
  induction cmds.
  - admit.
  - split.
    + admit.
Admitted.  