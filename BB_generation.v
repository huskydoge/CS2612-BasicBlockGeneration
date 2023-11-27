Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Main.grammer.
Require Import Coq.Program.Wf.
Require Export String.
Require Export ZArith.
Require Export Znumtheory.
Require Export List.
Require Export Bool.
Require Export Lia.


(* Block Number 0 ~ 10 are reserved*)

Definition BB0 : nat := 0.

(* Create a global variable recording the current block number *)
Definition global_block_num : nat := 10.
  
Inductive JumpKind : Type :=
| UJump  (* Represents an unconditional jump *)
| CJump.   (* Represents a conditional jump *)


(* Definition of BlockInfo *)
Record BlockInfo : Type := {
  jump_kind : JumpKind; (* Represents the type of jump instruction *)
  jump_dist_1 : nat; (* Represents the target block's identifier or label *)
  jump_dist_2 : option nat; (* Represents the target block's identifier or label, used for CJump *)
  jump_condition : option expr (* Represents the condition for conditional jumps, if any *)
}.


(* Definition of BasicBlock *)
Record BasicBlock : Type := {
  block_num : nat; (* Represents the block's identifier *)
  commands : list cmd; (* Represents a command *)
  jump_info : BlockInfo (* Defines the jump information *)
}.


Notation "s '.(block_num)'" := (block_num s) (at level 1).
Notation "s '.(cmd)'" := (commands s) (at level 1).
Notation "s '.(jump_info)'" := (jump_info s) (at level 1).


(* Definition
    - cmds is the list of remaining commands that need to be processed.
    - BB_now is the currently constructed basic block, which starts with an empty list of commands 
      and has a jump information specified by end_info.
*)

Record basic_block_gen_results : Type := {
  BasicBlocks: list BasicBlock;
  current_block_num: nat
}.

Notation "s '.(BasicBlocks)'" := (BasicBlocks s) (at level 1).
Notation "s '.(current_block_num)'" := (current_block_num s) (at level 1).

  Fixpoint last (l:list BasicBlock) (d:BasicBlock) : BasicBlock :=
    match l with
      | [] => d
      | [a] => a
      | a :: l => last l d
    end.


(* 空基本块，用于寻找BB list中最后一个元素时候的默认值处理*)
Definition EmptyBlock : BasicBlock := {|
  block_num := 10;
  commands := [];
  jump_info := {|
    jump_kind := UJump;
    jump_dist_1 := 10;
    jump_dist_2 := None;
    jump_condition := None
  |}
|}.


Section basic_block_gen.

Variable cmd_BB_gen : cmd -> BasicBlock -> basic_block_gen_results.


Fixpoint list_cmd_BB_gen (cmds: list cmd) (BB_now: BasicBlock): basic_block_gen_results :=
  match cmds with
  | [] => {| BasicBlocks := [BB_now]; current_block_num := BB_now.(block_num) |}
  | cmd :: tl => 
    match cmd with
    | CAsgn _ _ => 
      let cmd_BB_result := cmd_BB_gen cmd BB_now in
      let tl_BB_result := list_cmd_BB_gen tl (last cmd_BB_result.(BasicBlocks) EmptyBlock) in
      {| BasicBlocks := tl_BB_result.(BasicBlocks);
         current_block_num := tl_BB_result.(current_block_num) |}
    | _ => 
      let cmd_BB_result := cmd_BB_gen cmd BB_now in
      let tl_BB_result := list_cmd_BB_gen tl (last cmd_BB_result.(BasicBlocks) EmptyBlock) in
      {| BasicBlocks := cmd_BB_result.(BasicBlocks) ++ tl_BB_result.(BasicBlocks);
         current_block_num := tl_BB_result.(current_block_num) |}
    end
  end.



  
End basic_block_gen.


Fixpoint cmd_BB_gen (c: cmd) (BB_now: BasicBlock) : basic_block_gen_results :=
  match c with
  | CAsgn x e => 
    (* update BB_now*)
    let BB_now' := {|
      block_num := BB_now.(block_num);
      commands := BB_now.(commands) ++ [CAsgn x e];
      jump_info := BB_now.(jump_info)
    |} in
    {| 
      BasicBlocks := [BB_now'];
      current_block_num := BB_now'.(block_num)
    |}

  | CIf e c1 c2 =>
    let BB_next := {|
    block_num := 10;
    commands := []; (* 创建一个空的命令列表 *)
    (* 占位, 无实际作用*)
    jump_info := {|
      jump_kind := UJump;
      jump_dist_1 := 10;
      jump_dist_2 := None;
      jump_condition := None
      |}
    |} in

    (* Then Branch*)
    let BB_then := {|
    block_num := S (BB_now.(block_num)); (* a + 2 *)
    commands := c1;
    jump_info := {|
      jump_kind := UJump;
      jump_dist_1 := BB_next.(block_num); 
      jump_dist_2 := None; 
      jump_condition := None
      |}
    |} in
    let BB_then_generated_results := list_cmd_BB_gen cmd_BB_gen c1 BB_then in

    (* Else Branch*)
    let BB_else := {|
      block_num := S (BB_then_generated_results.(current_block_num)); (* current block num +1 *)
      commands := c2;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_next.(block_num); 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in

    let BB_else_generated_results := list_cmd_BB_gen cmd_BB_gen c2 BB_else in

    let BB_now' := {|
    block_num := BB_now.(block_num);
    commands := BB_now.(commands);
    jump_info := {|
      jump_kind := CJump;
      jump_dist_1 := BB_then.(block_num);
      jump_dist_2 := Some (BB_else.(block_num));
      jump_condition := Some (e);
      |}
    |} in

    (* We should now correct the jump info of BB_then and BB_else*)
    let BB_then' := {|
      block_num := BB_then.(block_num);
      commands := c1;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := S (BB_else_generated_results.(current_block_num)); 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in

    let BB_then_generated_results' := list_cmd_BB_gen cmd_BB_gen c1 BB_then' in

    let BB_else' := {|
      block_num := BB_else.(block_num);
      commands := c2;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := S (BB_else_generated_results.(current_block_num)); 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in

    let BB_else_generated_results' := list_cmd_BB_gen cmd_BB_gen c2 BB_else' in

    {| BasicBlocks := [BB_now'] ++ BB_then_generated_results'.(BasicBlocks) ++ BB_else_generated_results'.(BasicBlocks);
       current_block_num := BB_else_generated_results'.(current_block_num) |}
    
  | CWhile pre e body => 
    let BB_next := {|
      block_num := 10; 
      commands := []; (* 创建一个空的命令列表 *)
      (* 占位, 目前暂不知道BBnext的blocknum，因而pre其实也不知道跳转到哪里。我们需要先知道PRE和BODY产生了多少BB *)
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := 10;
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    (* 占位，因为pre中要知道自己需要产生多少个BB，来指定自己跳转的位置 (到Body) *)
    let BB_pre := {|
        block_num := S (BB_now.(block_num)); 
        commands := pre;
        jump_info := {|
          jump_kind := CJump;
          jump_dist_1 := 10;
          jump_dist_2 := Some BB_next.(block_num); (* jump out of the loop *)
          jump_condition := Some e
        |}
    |} in

    let BB_pre_generated_results := list_cmd_BB_gen cmd_BB_gen pre BB_pre in

    let BB_pre' := {|
      block_num := S (BB_next.(block_num)); 
      commands := pre;
      jump_info := {|
        jump_kind := CJump;
        jump_dist_1 := S(BB_pre_generated_results.(current_block_num)); (* jump to the body *)
        jump_dist_2 := Some BB_next.(block_num); (* jump out of the loop *)
        jump_condition := Some e
      |}
    |} in

    let BB_body := {|
      block_num := S (BB_pre_generated_results.(current_block_num));
      commands := body;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_pre'.(block_num); 
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_body_generated_results := list_cmd_BB_gen cmd_BB_gen body BB_body in

    let BB_now' := {|
      block_num := BB_now.(block_num); 
      commands := BB_now.(commands);
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_pre'.(block_num); (* update jump info*)
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let out_loop := Some (S(BB_body_generated_results.(current_block_num))) in
    (* 更正pre 跳转的位置*)
    let BB_pre_ := {|
      block_num := S (BB_next.(block_num)); 
      commands := pre;
      jump_info := {|
        jump_kind := CJump;
        jump_dist_1 := BB_body.(block_num); (* jump to the body *)
        jump_dist_2 := out_loop ; (* jump out of the loop *)
        jump_condition := Some e
      |}
    |} in

    let BB_pre_generated_results_ := list_cmd_BB_gen cmd_BB_gen pre BB_pre_ in
      
    {| BasicBlocks := [BB_now'] ++ BB_pre_generated_results_.(BasicBlocks) ++ BB_body_generated_results.(BasicBlocks);
        current_block_num := BB_body_generated_results.(current_block_num) |}
  end.


Check cmd_BB_gen.