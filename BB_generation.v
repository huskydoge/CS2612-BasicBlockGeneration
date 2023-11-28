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
  BasicBlocks: list BasicBlock; (* already finished blocks*)
  BBn: BasicBlock; (* current_block_num should be the block num of BB_now, I think *)
  current_block_num: nat
}.

Notation "s '.(BasicBlocks)'" := (BasicBlocks s) (at level 1).
Notation "s '.(current_block_num)'" := (current_block_num s) (at level 1).
Notation "s '.(BBn)'"  := (BBn s)(at level 1).

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

(*考虑将已经生成的所有basicblock作为输入*)
Section basic_block_gen.

Variable cmd_BB_gen : cmd -> list BasicBlock -> BasicBlock -> nat -> basic_block_gen_results.


Fixpoint list_cmd_BB_gen (cmds: list cmd) (BBs: list BasicBlock)(BB_now: BasicBlock)(BB_num: nat): basic_block_gen_results :=
  match cmds with
  | [] => {| BasicBlocks := BBs; BBn := BB_now; current_block_num := BB_num;  |}
  | cmd :: tl => 
    let cmd_BB_result := cmd_BB_gen (cmd) (BBs) (BB_now) (BB_num) in  (* 先对列表第一个cmd进行处理，返回results *)
    let tl_BB_result := list_cmd_BB_gen (tl) (cmd_BB_result.(BasicBlocks))(cmd_BB_result.(BBn)) (cmd_BB_result.(current_block_num)) in  (* 对剩下的cmd进行处理，返回results *)
    {| 
      BasicBlocks := tl_BB_result.(BasicBlocks);
      BBn := tl_BB_result.(BBn);
      current_block_num := tl_BB_result.(current_block_num) |}
  end.


  
End basic_block_gen.



(* Section cmd_list_BB_num.

Variable cmd_BB_num : cmd -> nat -> nat.

(* Fixpoint cmd_list_BB_num (cl : list cmd) : nat :=
  match cl with
  | [] => 0
  | cmd :: tl => cmd_BB_num cmd + cmd_list_BB_num tl
  end.

End cmd_list_BB_num.

Fixpoint cmd_BB_num (c : cmd) : nat :=
  match c with
  | CAsgn _ _ => 0
  | CIf _ c1 c2 => 2 + cmd_list_BB_num cmd_BB_num c1 + cmd_list_BB_num cmd_BB_num c2
  | CWhile pre _ body => 2 + cmd_list_BB_num cmd_BB_num pre + cmd_list_BB_num cmd_BB_num body
  end. *) *)


Fixpoint cmd_BB_gen (c: cmd) (BBs: list BasicBlock)(BB_now: BasicBlock) (BB_num: nat) : basic_block_gen_results :=
  match c with
  | CAsgn x e => 
    (* update BB_now*)
    let BB_now' := {|
      block_num := BB_num;
      commands := BB_now.(commands) ++ [CAsgn x e];
      jump_info := BB_now.(jump_info)
    |} in
    {| 
      BasicBlocks := BBs;
      BBn := BB_now';
      current_block_num := BB_now'.(block_num)
    |}

  | CIf e c1 c2 =>
    (* Then Branch*)
    let BB_then_num := (S BB_num) in 
    let BB_then_last_num := (list_cmd_BB_gen cmd_BB_gen c1 [] EmptyBlock BB_then_num).(current_block_num) in
    (* Else Branch*)
    let BB_else_num := (S BB_then_last_num) in 
    let BB_else_last_num := (list_cmd_BB_gen cmd_BB_gen c2 [] EmptyBlock BB_else_num).(current_block_num) in
    let BB_next_num := S(BB_else_last_num) in

    let BB_next := {|
      block_num := BB_next_num;
      commands := []; (* 创建一个空的命令列表 *)
      jump_info := BB_now.(jump_info)
      |} in

    let BB_now' := {|
      block_num := BB_num;
      commands := BB_now.(commands);
      jump_info := {|
        jump_kind := CJump;
        jump_dist_1 := BB_then_num;
        jump_dist_2 := Some (BB_else_num);
        jump_condition := Some (e);
        |}
      |} in

    let BB_then' := {|
      block_num := BB_then_num;
      commands := c1;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_next_num; 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in

    let BB_then_generated_results' := list_cmd_BB_gen cmd_BB_gen c1 [] BB_then' BB_then_num in

    let BB_else' := {|
      block_num := BB_else_num;
      commands := c2;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_next_num; 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in

    let BB_else_generated_results' := list_cmd_BB_gen cmd_BB_gen c2 [] BB_else' BB_else_num in
    {| BasicBlocks := BBs++[BB_now'] ++ BB_then_generated_results'.(BasicBlocks) ++ [BB_then_generated_results'.(BBn)] ++ BB_else_generated_results'.(BasicBlocks) ++ [BB_else_generated_results'.(BBn)]; BBn := BB_next;
       current_block_num := BB_next.(block_num) |}
    
  | CWhile pre e body => 

    let BB_pre_num := (S BB_num) in 
    let BB_pre_last_num := (list_cmd_BB_gen cmd_BB_gen pre [] EmptyBlock BB_pre_num).(current_block_num) in
    let BB_body_num := (S BB_pre_last_num) in 
    let BB_body_last_num := (list_cmd_BB_gen cmd_BB_gen body [] EmptyBlock BB_body_num).(current_block_num) in
    let BB_next_num := (S BB_body_last_num) in

    let BB_now' := {|
      block_num := BB_num; 
      commands := BB_now.(commands);
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_pre_num; (* update jump info*)
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_pre := {|
    block_num := BB_pre_num; 
    commands := [];
    jump_info := {|
      jump_kind := CJump;
      jump_dist_1 := BB_body_num; (* jump to the body *)
      jump_dist_2 := Some BB_next_num; (* jump out of the loop *)
      jump_condition := Some e
      |}
    |} in
    
    let BB_pre_generated_results := list_cmd_BB_gen cmd_BB_gen pre [] BB_pre BB_pre_num in

    let BB_body := {|
      block_num := BB_body_num;
      commands := [];
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_pre_num; 
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_body_generated_results := list_cmd_BB_gen cmd_BB_gen body [] BB_body BB_body_num in

    let BB_next := {|
      block_num := BB_next_num;
      commands := [];
      jump_info := BB_now.(jump_info)
    |} in
      
    {| BasicBlocks := BBs ++ [BB_now'] ++ BB_pre_generated_results.(BasicBlocks) ++ [BB_pre_generated_results.(BBn)] ++ BB_body_generated_results.(BasicBlocks) ++ [BB_body_generated_results.(BBn)];
        BBn := BB_next;
        current_block_num := BB_next.(block_num) |}
  end.


Check cmd_BB_gen.

(*名字瞎起的，可以改一下*)
(*When finishing all block generations,
the record still remains a BBs and aBBn, which is indeed completed.
This function merge the result to a whole list of basicblock*)
Definition to_result (r: basic_block_gen_results) :
list BasicBlock := r.(BasicBlocks) ++ [r.(BBn)].

(* main function, which generates BBs for the whole cmds. Take zero as start for now*)
Definition BB_gen (cmds: list cmd):
list BasicBlock := to_result (list_cmd_BB_gen cmd_BB_gen cmds [] EmptyBlock 0).




