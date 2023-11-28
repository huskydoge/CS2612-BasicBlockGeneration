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

Variable cmd_BB_gen : cmd -> list BasicBlock -> BasicBlock -> basic_block_gen_results.


Fixpoint list_cmd_BB_gen (cmds: list cmd) (BBs: list BasicBlock)(BB_now: BasicBlock): basic_block_gen_results :=
  match cmds with
  | [] => {| BasicBlocks := BBs; BBn := BB_now; current_block_num := BB_now.(block_num);  |}
  | cmd :: tl => 
    let cmd_BB_result := cmd_BB_gen (cmd) (BBs)(BB_now) in  (* 先对列表第一个cmd进行处理，返回results *)
    let tl_BB_result := list_cmd_BB_gen (tl) (cmd_BB_result.(BasicBlocks))(cmd_BB_result.(BBn)) in  (* 对剩下的cmd进行处理，返回results *)
    {| 
      BasicBlocks := tl_BB_result.(BasicBlocks);
      BBn := tl_BB_result.(BBn);
      current_block_num := tl_BB_result.(current_block_num) |}
  end.


  
End basic_block_gen.



Section cmd_list_BB_num.

Variable cmd_BB_num : cmd -> nat -> nat.

Fixpoint cmd_list_BB_num (cl : list cmd) (num: nat) : nat :=
  match cl with
  | [] => 0
  | cmd :: tl => cmd_BB_num cmd num + cmd_list_BB_num tl num
  end.

End cmd_list_BB_num.

Fixpoint cmd_BB_num (c : cmd) (num: nat) : nat :=
  match c with
  | CAsgn _ _ => 0
  | CIf _ c1 c2 => 2 + cmd_list_BB_num cmd_BB_num c1 num + cmd_list_BB_num cmd_BB_num c2 num
  | CWhile pre _ body => 2 + cmd_list_BB_num cmd_BB_num pre num + cmd_list_BB_num cmd_BB_num body num
  end.


Fixpoint cmd_BB_gen (c: cmd) (BBs: list BasicBlock)(BB_now: BasicBlock) : basic_block_gen_results :=
  match c with
  | CAsgn x e => 
    (* update BB_now*)
    let BB_now' := {|
      block_num := BB_now.(block_num);
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
    let BB_then := {|
    block_num := S (BB_now.(block_num)); (* a + 2 *)
    commands := [];
    jump_info := {|
      jump_kind := UJump;
      jump_dist_1 := 10; 
      jump_dist_2 := None; 
      jump_condition := None
      |}
    |} in
    let BB_then_generated_results := list_cmd_BB_gen cmd_BB_gen c1 [] BB_then in
 
    (* Else Branch*)
    let BB_else := {|
      block_num := S (BB_then_generated_results.(current_block_num)); (* current block num +1 *)
      commands := [];
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := 10; 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in

    let BB_else_generated_results := list_cmd_BB_gen cmd_BB_gen c2 [] BB_else in

    let BB_next := {|
    block_num := S(BB_else_generated_results.(current_block_num));
    commands := []; (* 创建一个空的命令列表 *)
    (* 占位, 无实际作用*)
    jump_info := BB_now.(jump_info)

    |} in
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
        jump_dist_1 := BB_next.(block_num); 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in

    let BB_then_generated_results' := list_cmd_BB_gen cmd_BB_gen c1 [] BB_then' in

    let BB_else' := {|
      block_num := BB_else.(block_num);
      commands := c2;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_next.(block_num); 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in

    let BB_else_generated_results' := list_cmd_BB_gen cmd_BB_gen c2 [] BB_else' in

    {| BasicBlocks := BBs++[BB_now'] ++ BB_then_generated_results'.(BasicBlocks) ++ [BB_then_generated_results'.(BBn)] ++ BB_else_generated_results'.(BasicBlocks) ++ [BB_else_generated_results'.(BBn)]; BBn := BB_next;
       current_block_num := BB_next.(block_num) |}
    
  | CWhile pre e body => 

    (* 占位，因为pre中要知道自己需要产生多少个BB，来指定自己跳转的位置 (到Body) *)
    let BB_pre := {|
        block_num := S (BB_now.(block_num)); 
        commands := [];
        jump_info := {|
          jump_kind := CJump;
          jump_dist_1 := 10;
          jump_dist_2 := None; (* jump out of the loop *)
          jump_condition := None
        |}
    |} in

    let BB_pre_generated_results := list_cmd_BB_gen cmd_BB_gen pre [] BB_pre in

    let BB_now' := {|
      block_num := BB_now.(block_num); 
      commands := BB_now.(commands);
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_pre.(block_num); (* update jump info*)
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_body := {|
      block_num := S (BB_pre_generated_results.(current_block_num));
      commands := [];
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_pre.(block_num); 
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_body_generated_results := list_cmd_BB_gen cmd_BB_gen body [] BB_body in

    let BB_next := {|
      block_num := S (BB_body_generated_results.(current_block_num));
      commands := [];
      jump_info := BB_now.(jump_info)
    |} in

    let BB_pre' := {|
      block_num := S (BB_next.(block_num)); 
      commands := [];
      jump_info := {|
        jump_kind := CJump;
        jump_dist_1 := BB_body.(block_num); (* jump to the body *)
        jump_dist_2 := Some BB_next.(block_num); (* jump out of the loop *)
        jump_condition := Some e
      |}
    |} in

    let BB_pre_generated_results' := list_cmd_BB_gen cmd_BB_gen pre [] BB_pre' in

      
    {| BasicBlocks := BBs ++ [BB_now'] ++ BB_pre_generated_results'.(BasicBlocks) ++ [BB_pre_generated_results'.(BBn)] ++ BB_body_generated_results.(BasicBlocks) ++ [BB_body_generated_results.(BBn)];
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

(* main function, which generates BBs for the whole cmds *)
Definition BB_gen (cmds: list cmd):
list BasicBlock := to_result (list_cmd_BB_gen cmd_BB_gen cmds [] EmptyBlock).




