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
      bs1.(st) = bs2.(st) /\ (jmp_sem jmp_dist1 jmp_dist2 D).(Bnrm) bs1 bs2;
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
Definition BB_jmp_sem (BB: BasicBlock): BDenote := {| 
  Bnrm := 
    let jmp_dist1 := BB.(jump_info).(jump_dist_1) in
    let jmp_dist2 := BB.(jump_info).(jump_dist_2) in
    let jmp_cond := BB.(jump_info).(jump_condition) in
    (BJump_sem jmp_dist1 jmp_dist2 (eval_cond_expr jmp_cond)).(Bnrm); 
  Berr := ∅;
  Binf := ∅;
|}.

Definition BB_cmds_sem (BB: BasicBlock): BDenote := {| 
  Bnrm := 
    (BAsgn_list_sem BB.(cmd)).(Bnrm);
  Berr := ∅;
  Binf := ∅;
|}.

(* Combine the single_step_stem to form the denotation for BB_list_sem.
   Not certain about its correctness  *)
Fixpoint BB_list_sem (BBs: list BasicBlock): BDenote := {|
  Bnrm := 
    match BBs with 
    | BB :: tl => match tl with
                  | nil => (BB_cmds_sem BB).(Bnrm)
                  | _ => (BB_cmds_sem BB).(Bnrm) ∘ (BB_jmp_sem BB).(Bnrm) ∘ (BB_list_sem tl).(Bnrm)
                  end
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


(* The following are preparations for the final theorem *)


Record BCequiv (B: BDenote) (C: CDenote) (startBB endBB: nat): Prop := {
  nrm_cequiv: (fun s1 s2 => exists bs1 bs2, B.(Bnrm) bs1 bs2 /\ bs1.(st) = s1 /\ bs2.(st) = s2 /\ bs1.(BB_num) = startBB /\ bs2.(BB_num) = endBB) == C.(nrm);
  err_cequiv: (fun s => exists bs, B.(Berr) bs /\ bs.(st) = s) == C.(err); 
  inf_cequiv: (fun s => exists bs, B.(Binf) bs /\ bs.(st) = s) == C.(inf);
}.

Ltac my_destruct H :=
  match type of H with 
  | exists _, _ => destruct H as [? H]; my_destruct H 
  | _ /\ _ => let H1:= fresh "H" in 
              destruct H as [H H1];my_destruct H; my_destruct H1
  | _ => idtac 
  end.

Definition Q(c: cmd): Prop :=
  (* Q(Asgn)里面不能出现cmds, 或者说Q(c)里面你就要讲BBs等等变化前后有什么区别, 别去搞cmds，你们搞得那个反而把问题搞复杂了
    嗯，当然你要证明的是语义的变化，所以你要说多出来的commands的语义，和那个c的语义一样 -- by cqx *)
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum :nat), 
    let res := cmd_BB_gen c BBs BBnow BBnum in
    (*CAsgn*)
    (exists BBnow' BBcmd,
      res.(BBn) = BBnow' /\
      BBnow'.(commands) = BBnow.(commands) ++ (BBcmd :: nil) /\
      BCequiv (BAsgn_list_sem (BBcmd :: nil)) (cmd_sem c) BBnow'.(block_num) BBnow'.(block_num)) (*还在当下的BBnow里，BBnum则是下一个BB的编号，不能用*)
    \/
    (*CIf / CWhile*)
    (exists BBs' BBnum', 
      res.(BasicBlocks) ++ (res.(BBn)::nil) =  BBs ++ (BBnow :: nil) ++ BBs' /\
      res.(BBn).(block_num) = BBnum' /\
      BCequiv (BB_list_sem BBs') (cmd_sem c) BBnum BBnum').


(* c: the cmd we are currently facing
  BBs: list of Basic Blocks which have been already generated
  BB_now: the Basic Block we are currently at
  BB_num: we should start assigning new basic blocks with BB_num 
  
  Record basic_block_gen_results : Type := {
  BasicBlocks: list BasicBlock; (* already finished blocks*)
  BBn: BasicBlock; (* current_block_num should be the block num of BB_now, I think *)
  next_block_num: nat (* I think next block should start with the number*)
}.*)

Definition P(cmds: list cmd)(cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results): Prop :=
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum :nat),  exists BBs' BBnow' (BBcmds: list BB_cmd),
    let res := list_cmd_BB_gen cmd_BB_gen cmds BBs BBnow BBnum in
    let BBres := res.(BasicBlocks) ++ (res.(BBn) :: nil) in (* 这里已经加入了生成完后，最后停留在的那个BB了，从而BBs'里有这个BB*)

      (*用BBnow_delta，一方面处理增加的BBcmds的语义，另一方面考虑了jumpinfo*)
      let BBnow_delta := {|
        block_num := BBnow'.(block_num);
        commands :=  BBcmds;
        jump_info := BBnow'.(jump_info);
      |}
      in 
    (* 连接当前基本块中因为Asgn添加的语义和新生成的基本块的语义*)
    let ConcateBDenote := 
    {| Bnrm := (BB_list_sem (BBnow_delta :: nil ++ BBs')).(Bnrm);
       Berr:= (BB_list_sem (BBnow_delta :: nil ++ BBs')).(Berr);
       Binf:= ∅;
      |}
    in



    (* 根据BBs' 的情况分配JumpInfo*)
    match BBs' with
    | nil => BBnow'.(jump_info) = BBnow.(jump_info)
    | next_BB :: _  => let BlockInfo' := {|
                      jump_kind := UJump;
                      jump_dist_1 := next_BB.(block_num);
                      jump_dist_2 := None;
                      jump_condition := None
                    |} in
                    BBnow'.(jump_info) = BlockInfo'
    end /\

    BBnow'.(commands) = BBnow.(commands) ++ BBcmds /\ BBnow'.(block_num) = BBnow.(block_num) /\

    BBres = BBs ++ (BBnow' :: nil) ++ BBs' /\ BCequiv (ConcateBDenote) (cmd_list_sem cmd_sem cmds) BBnow'.(block_num) res.(BBn).(block_num) (*总是从当前所在的BB开始*)

    /\ res.(BBn).(jump_info) = BBnow.(jump_info).

Lemma Q_asgn:
  forall (x: var_name) (e: expr),
  Q (CAsgn x e).
Proof.
  intros. unfold Q. left.
  exists {|
    block_num := BBnow.(block_num);
    commands := BBnow.(cmd) ++ {| X:= x; E:= e|} :: nil;
    jump_info := BBnow.(jump_info);
  |}.
  exists {| X := x; E := e|}.
  split.
  + reflexivity.
  + split. tauto. split.
    - unfold BAsgn_list_sem. simpl.
      sets_unfold. intros.
      split; intros.
      * destruct H as [? [? [? [? [? [? ?]]]]]].
        destruct H as [? ?].
        destruct H as [? ?].
        destruct H as [[? ?] ?].
        exists x3.
        rewrite H0 in H.
        rewrite <- H4 in H1.
        rewrite H1 in H.
        split. apply H. split. apply H.
        destruct H as [? [? ?]].
        intros.
        specialize (H7 Y). apply H7 in H8.
        rewrite H8. 
        tauto.
      * destruct H as [? [? [? ?]]].
        exists {| st := a; BB_num := BBnow.(block_num) |}.
        exists {| st := a0; BB_num := BBnow.(block_num) |}.
        split.
        ++ simpl.
           exists {| st := a0; BB_num := BBnow.(block_num) |}.
           split. split.
           exists x0. simpl.
           split. apply H. 
           split. apply H0.
           intros. specialize (H1 y). apply H1 in H2. rewrite H2. tauto.
           simpl. tauto.
           simpl. tauto.
        ++ simpl. tauto.
    - admit.
    - admit. 
Admitted.


Lemma Q_if:
  forall (e: expr) (c1 c2: list cmd),
  P c1 (cmd_BB_gen) -> P c2 (cmd_BB_gen) -> Q (CIf e c1 c2).
Proof.
  intros.
  unfold Q. intros. right.
  (* first get the result of the block from c1 for preparing c2 *)
  admit.
 
Admitted. 

Lemma Q_while:
  forall (pre: list cmd) (e: expr) (body: list cmd),
  P pre (cmd_BB_gen) -> P body (cmd_BB_gen) -> Q (CWhile pre e body).
Proof.
Admitted.


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


Lemma P_nil_aux1:
  forall (BBnow : BasicBlock) (a0 : state),
  Bnrm
    (jmp_sem (jump_dist_1 BBnow.(jump_info))
      (jump_dist_2 BBnow.(jump_info))
      (eval_cond_expr (jump_condition BBnow.(jump_info))))
    {| BB_num := BBnow.(block_num); st := a0 |}
    {| BB_num := BBnow.(block_num); st := a0 |}.
Proof.
  intros.
  unfold jmp_sem.
  destruct jump_condition.
  + admit.
  + simpl. 
    split. tauto.
    admit.    
Admitted.


Lemma P_nil:
  P nil (cmd_BB_gen).
Proof.
  unfold P. 
  simpl.
  intros.
  exists nil. exists BBnow. exists nil.
  split. tauto.
  split. rewrite append_nil_r. reflexivity.
  split. reflexivity.
  split. reflexivity.
  split. split.
  - split.
    ++ intros. 
      destruct H as [? [? [? [? [? [? ?]]]]]].
      simpl in H.
      simpl. sets_unfold.
      sets_unfold in H. rewrite H in H0. rewrite H0 in H1. apply H1.
    ++ intros.
      exists {| st := a; BB_num := BBnow.(block_num) |}.
      exists {| st := a0; BB_num := BBnow.(block_num) |}.
      simpl in H. sets_unfold in H.
      simpl. sets_unfold.
      repeat split.
      rewrite H. reflexivity.
  - admit.
  - admit. 
Admitted.



Lemma PAsgn_sound:
  forall (x: var_name) (e: expr) (cmds: list cmd),
  Q (CAsgn x e) -> P cmds cmd_BB_gen -> P ((CAsgn x e) :: cmds) (cmd_BB_gen).
Proof.
  intros.
  unfold Q in H. 
  unfold P. 
  intros. 
  specialize (H BBs BBnow BBnum). 
  destruct H.
  unfold cmd_BB_gen in H. 
  simpl in H.
  * destruct H as [BBnow' [BBcmd []]]. 
    unfold P in H0.    
    specialize (H0 BBs BBnow' BBnum).
    destruct H0 as [BBs' [BBnow'' [BBcmds []]]]. 
    my_destruct H2.
    exists BBs'. (*这里我们考虑到，a为Asgn，P(a::cmds)，归纳假设中的BBS'正好是我们要的delta量*)
    exists BBnow''. (*这里我们考虑到，a为Asgn，证明P(a::cmds)，里面的BBnow'应是把(a::cmds)开头所有的asgns都放进去的那个BB，所以应该用归纳假设中的BBnow', 也即BBnow''*) 
    exists (BBcmd :: BBcmds). (*这里我们考虑到，a为Asgn，证明P(a::cmds)，里面的BBcmds应该是把(a::cmds)开头所有的asgns都放进去的那个BB的cmds，所以应该用归纳假设中的BBcmds并上由单条指令产生的BBcmd, 也即(BBcmd :: BBcmds)*)
    repeat split; simpl.
    ++ destruct BBs'.
      +++  rewrite H0. 
           rewrite <- H. 
           simpl. 
           reflexivity.
      +++  rewrite H0. reflexivity.
    ++ rewrite H2.
       destruct H1. 
       simpl in H1. 
       rewrite H1. 
       simpl. 
       apply app_assoc_reverse.
    ++ rewrite H3. rewrite <- H. reflexivity.
    ++ rewrite H. rewrite H4. reflexivity.
    ++ sets_unfold.
       intros.
       my_destruct H7. 
       destruct BBs' in H7.
       +++ my_destruct H7.
           exists a.
           split.
           - exists x3. repeat split.
             rewrite H8 in H7.
             destruct H1. 
             rewrite <- H in H1. 
             simpl in H1. 
             apply app_inj_tail in H1. 
             destruct H1. 
             rewrite <- H14 in H7. 
             simpl in H7. 
             apply H7.
             rewrite H8 in H7. 
             destruct H1. 
             rewrite <- H in H1. 
             simpl in H1. 
             apply app_inj_tail in H1. 
             destruct H1. 
             (* rewrite <- H15 in H7. simpl in H7. apply H7. *)
             admit.
             admit.
           - admit.
       +++ admit.
    ++ admit.
    ++ admit. (*err*)
    ++ admit. (*inf*)
    ++ admit.
    ++ admit.
    ++ admit.
  * admit.
Admitted.

(* forall Q(C) => forall cmds, P cmds *)
Lemma P_sound:
  (forall (c: cmd), 
    Q c) -> forall (cmds : list cmd), P (cmds) (cmd_BB_gen).
Proof.
  intros.
  induction cmds.
  + apply P_nil.
  + destruct a.
    - specialize (H (CAsgn x e)).
      pose proof PAsgn_sound x e cmds.
      apply H0 in IHcmds.
      apply IHcmds. apply H.
    - specialize (H (CIf e c1 c2)).
      admit.
    - specialize (H (CWhile pre e body)).
      admit.
Admitted.

(* Lemma Q_sound:
  forall (c: cmd), Q c.
Proof.
  destruct c.
  + apply Q_asgn.
  + apply Q_if.
  + apply Q_while. *)

    
Search (_ ++ _::nil = _ ++ _ :: nil ).

Theorem BB_sound:
  forall (cmds: list cmd),
  P cmds cmd_BB_gen.
Proof.
  intros.
  induction cmds.
  - apply P_nil.
  - pose proof P_sound.
    destruct a.
    * pose proof Q_asgn x e.
      admit.
    * destruct cmds.
Admitted.