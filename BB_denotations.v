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


(* Handle Jmp Sem ====================================================================================================================== *)


Definition test_true_jmp (D: EDenote):
  state -> Prop :=
    (fun s => exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false_jmp (D: EDenote):
  state -> Prop :=
    (fun s => D.(nrm) s (Int64.repr 0)).

Definition ujmp_sem (jum_dist: nat): BDenote :=
  {|
    Bnrm := fun (bs1: BB_state) (bs2 :BB_state) =>
      bs1.(st) = bs2.(st) /\ bs2.(BB_num) = jum_dist /\ bs1.(BB_num) <> bs2.(BB_num); (*用于证明不相交*)
    Berr := ∅;
    Binf := ∅;
  |}.

Definition cjmp_sem (jmp_dist1: nat) (jmp_dist2: nat) (D: EDenote) : BDenote :=
  {|
    Bnrm := fun bs1 bs2 => ((bs1.(st) = bs2.(st)) /\ 
            ((bs2.(BB_num) = jmp_dist1) /\ (test_true_jmp D bs1.(st)) \/ ((bs2.(BB_num) = jmp_dist2) 
            /\ (test_false_jmp D bs1.(st))))) /\ bs1.(BB_num) <> bs2.(BB_num); (*用于证明不相交*)
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


Definition BJump_sem (jmp_dist1: nat) (jmp_dist2: option nat) (D: option EDenote) : BDenote := {|
  Bnrm := fun bs1 bs2 => 
      bs1.(st) = bs2.(st) /\ (jmp_sem jmp_dist1 jmp_dist2 D).(Bnrm) bs1 bs2;
  Berr := ∅;
  Binf := ∅;
|}.

(* =================================================================================================================================================================================    *)



Definition BAsgn_sem (x: var_name) (e:EDenote) : BDenote := {|
  Bnrm := fun (bs1:BB_state) (bs2:BB_state) => 
     exists i,
     (e.(nrm) bs1.(st) i) /\  (bs2.(st) x = Vint i) /\ (forall y, x <> y -> bs1.(st) y = bs2.(st) y);
  Berr := fun(bs1:BB_state) => bs1.(st) ∈ e.(err);
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

Definition BB_single_step_sem (BB: BasicBlock): BDenote := {|
  Bnrm := (BB_cmds_sem BB).(Bnrm) ∘ (BB_jmp_sem BB).(Bnrm);
  Berr := ∅;
  Binf := ∅;
|}.

Definition BB_sem (BB: BasicBlock): BDenote := {|
  Bnrm := (BB_cmds_sem BB).(Bnrm) ∘ (BB_jmp_sem BB).(Bnrm) ;
  Berr :=  ∅;
  Binf :=  ∅;
|}.

Fixpoint BB_sem_list(BBs: list BasicBlock): BDenote :=  {|
  Bnrm := 
    match BBs with 
    | BB :: tl =>(BB_sem_list tl).(Bnrm) ∪ (BB_sem BB).(Bnrm)
    | _ => ∅
    end;
  Berr := ∅;
  Binf := ∅;
|}.

Fixpoint Iter_nrm_BBs_n (BD: BDenote) (n: nat):  BB_state -> BB_state  -> Prop :=
  match n with
  | O => BD.(Bnrm)
  | S n0 => BD.(Bnrm) ∪ (BD.(Bnrm) ∘ (Iter_nrm_BBs_n BD n0))
  end.

(* Combine the single_step_stem to form the denotation for BB_list_sem.
   Not certain about its correctness  *)
Definition BB_list_sem (BBs: list BasicBlock): BDenote := {|
  Bnrm := ⋃ (Iter_nrm_BBs_n (BB_sem_list BBs)); 
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
    (exists BBnow' BBs' BBnum', 
      res.(BasicBlocks) ++ (res.(BBn)::nil) =  BBs ++ (BBnow' :: nil) ++ BBs' /\
      res.(BBn).(block_num) = BBnum' /\
      BCequiv (BB_list_sem BBs') (cmd_sem c) BBnum BBnum'). (* 这里的BBnum'是最后停留在BB的编号，要和cmd_BB_gen中的BBnum做区分！ *)


(* c: the cmd we are currently facing
  BBs: list of Basic Blocks which have been already generated
  BBnow: the Basic Block we are currently at
  BB_num: we should start assigning new basic blocks with BB_num 
  
  Record basic_block_gen_results : Type := {
  BasicBlocks: list BasicBlock; (* already finished blocks*)
  BBn: BasicBlock; (* current_block_num should be the block num of BBnow, I think *)
  next_block_num: nat (* I think next block should start with the number*)
}.*)

Definition P(cmds: list cmd)(cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results): Prop :=
  forall (BBs: list BasicBlock) (BBnow: BasicBlock) (BBnum :nat),  exists BBs' BBnow' (BBcmds: list BB_cmd) BBnum',
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
    | next_BB :: _  => 
        (match cmds with
        | nil =>  BBnow'.(jump_info) = BBnow.(jump_info)
        | c :: tl =>
          (match c with
            | CAsgn x e => (let BlockInfo' := {|
                                              jump_kind := UJump;
                                              jump_dist_1 := next_BB.(block_num);
                                              jump_dist_2 := None;
                                              jump_condition := None
                                            |} in
                                            BBnow'.(jump_info) = BlockInfo')
            | CIf e c1 c2 => (let BB_then_num := BBnum in
                   let BB_else_num := S(BB_then_num) in  (* 用哪个比较好？next_BB.(block_num)还是 BBnum？*)
                   let BlockInfo' := {|
                                        jump_kind := CJump;
                                        jump_dist_1 := next_BB.(block_num);
                                        jump_dist_2 := Some (S(next_BB.(block_num)));
                                        jump_condition := Some e
                                      |} in
                                      BBnow'.(jump_info) = BlockInfo')
            | CWhile pre e body => (let BB_then_num := BBnum in
                   let BB_else_num := S(BB_then_num) in  (* 用哪个比较好？next_BB.(block_num)还是 BBnum？*)
                   let BlockInfo' := {|
                                        jump_kind := UJump;
                                        jump_dist_1 := next_BB.(block_num);
                                        jump_dist_2 := None;
                                        jump_condition := None
                                      |} in
                                      BBnow'.(jump_info) = BlockInfo') 
          end)
        end)
    end /\

    (*要拿到用于分配的下一个BBnum的信息*)

    BBnum' = res.(next_block_num) /\

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
                      jump_dist_1 := BB_next_num; 
                      jump_dist_2 := None; 
                      jump_condition := None
                      |};
                   |}).
  set(BBnow' := {|block_num := BBnow.(block_num);
                   commands := BBnow.(commands);
                   jump_info := {|
                      jump_kind := CJump;
                      jump_dist_1 := BB_then_num; 
                      jump_dist_2 := Some BB_else_num; 
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
  destruct H as [BBs_then [BB_now_then [ BB_cmds_then [BB_num2 [?]]]]].
  (* Get correct BBnow for P c2 *)
  set (BB_else := {|
    block_num := BB_else_num;
    commands := nil;
    jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_next_num; 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |}).
  (*此时已经生成的 BBs_ := BBs ++ BBnow::nil ++ BB_now_then ++ BBs_then, 注意这里的BB_now_then和BB_then不同！它里面的commands可能由于CAsgn有填充*)
  (*此时的BBnow则应该用BB_else了*)

  unfold P in H0. 
  specialize (H0 (BBs ++ BBnow'::nil ++ BB_now_then::nil ++ BBs_then) BB_else BB_num2).

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
  set(BBs'_ := BB_now_then::nil ++ BBs_then ++ BB_now_else::nil ++ BBs_else ++ BB_next::nil). (*这里BBs_else已经包括了else分支最后一个BB，然后就是无条件跳转到BBnext了，还要接上一个BBnext，*)
  
  exists BBnow'. exists BBs'_. exists BB_next_num.
  (*========================================== *)
  (* MAIN ========================================== *)
  split.
  - cbn [cmd_BB_gen]. simpl. 
    subst BB_then_num. subst BB_next_num. subst BB_else_num.
    my_destruct H1. my_destruct H2.
    replace (S (S (S BBnum))) with (BB_num1).
    replace ({|
    block_num := BBnum;
    commands := nil;
    jump_info :=
      {|
        jump_kind := UJump;
        jump_dist_1 := S (S BBnum);
        jump_dist_2 := None;
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
                 jump_dist_1 := BBnum;
                 jump_dist_2 := Some (S BBnum);
                 jump_condition := Some e
                |}
              |} with BBnow'.
    replace {|
              block_num := S BBnum;
              commands := nil;
              jump_info :=
                {|
                  jump_kind := UJump;
                  jump_dist_1 := S (S BBnum);
                  jump_dist_2 := None;
                  jump_condition := None
                |}
            |} with BB_else.
      + subst BBs'_ . simpl. unfold to_result. simpl. rewrite H5. simpl. rewrite <- H1. simpl in H10. 
        assert (BBs ++ BBnow' :: BB_now_then :: BBs_then = (BBs ++ BBnow' :: nil) ++ BB_now_then :: BBs_then).
        {
          rewrite <- app_assoc. simpl. reflexivity.
        }
        rewrite <- H13. rewrite H10. rewrite <- app_assoc. simpl. rewrite <- app_assoc. simpl. reflexivity. 
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
  - split.
    * cbn [cmd_BB_gen]. simpl. reflexivity.
    * my_destruct H2. my_destruct H1.
      simpl in H11. simpl in H6.
      assert (BB_now_else.(block_num) = BB_else_num).
      {
        rewrite H4. reflexivity.
      }
      rewrite H13 in H6.
      split; sets_unfold.
      ++ intros. destruct H6. destruct H11. clear err_cequiv0 inf_cequiv0 err_cequiv1 inf_cequiv1.
          specialize (nrm_cequiv1 a a0). destruct nrm_cequiv1.
          specialize (nrm_cequiv0 a a0). destruct nrm_cequiv0.
         repeat split.
         +++ intros.
                simpl. unfold BB_list_sem in H16.
              (*OK 到这一步就已经是分两部分走了, 开始看上面的命题，在jmp还是不jmp之间找共通，bs1，bs2的a和a0*)
              (*如果test true*)

Admitted. 

Search (S _ = _ ).

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


Lemma P_nil: forall cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results,
  P nil (cmd_BB_gen).
Proof.
  unfold P. 
  simpl.
  intros.
  exists nil. exists BBnow. exists nil. exists BBnum.
  split. tauto.
  split. reflexivity.
  split. admit.
  split. reflexivity.
  split. split. split.
  - intros. simpl.
    split.
    + sets_unfold. intros.
      split. 
      ++ intros.
         my_destruct H. simpl in H. my_destruct H.
         simpl.
         induction x1.
         -- simpl in H. destruct H. tauto. 
            my_destruct H.
            rewrite <- H0. rewrite <- H1.
            rewrite <- H4. rewrite H. tauto.
         -- unfold Iter_nrm_BBs_n in H. simpl in H.
            sets_unfold in H.
            destruct H as [[? | ?]| ?].
            * tauto.
            * my_destruct H.
              rewrite <- H0. rewrite <- H1.
              rewrite <- H4. rewrite H. tauto.
            * my_destruct H. destruct H as [? | ?]. tauto.
              my_destruct H.
              assert (x2 = x). {
                (* 只需要证明x2, x3 block_num相同；需要从已知条件中推一下 *)
                repeat rewrite <- H5.
                admit.
              }
              rewrite H7 in H4.
              apply IHx1 in H4.
              apply H4.
    + admit.
    + admit. 
  - reflexivity.
Admitted.


Lemma P_cons:
  forall (c: cmd) (cmds: list cmd) (cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results),
  Q c -> P cmds cmd_BB_gen -> P (c :: cmds) (cmd_BB_gen).
Proof.
  intros.
  destruct c.
  - admit.
  - admit.
  - admit.
Admitted. 


Section BB_sound.

Variable cmd_BB_gen: cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results.
Variable cmd_BB_gen_sound: forall (c: cmd), Q c.

Fixpoint cmd_list_BB_gen_sound (cmds: list cmd): P cmds cmd_BB_gen :=
  match cmds with
  | nil => P_nil cmd_BB_gen
  | c :: cmds0 => P_cons c cmds0 cmd_BB_gen (cmd_BB_gen_sound c) (cmd_list_BB_gen_sound cmds0)
  end.

End BB_sound.

Fixpoint cmd_BB_gen_sound (c: cmd): Q c :=
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