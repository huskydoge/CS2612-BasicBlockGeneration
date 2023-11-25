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



(* Create a global variable recording the current block number *)
Definition global_block_num : nat := 0.
  
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

Section basic_block_gen.

Variable cmd_BB_gen : cmd -> BasicBlock -> basic_block_gen_results.

Fixpoint basic_block_gen (cmds: list cmd) (BB_now: BasicBlock): basic_block_gen_results :=
  match cmds with
  | [] =>
    (* No more commands, return the current basic block *)
    {| BasicBlocks := [BB_now]; current_block_num := BB_now.(block_num) |}
  
  | CAsgn x e :: tl =>
    (* Add the assignment command to the current basic block *)
    let BB_next := {|
      block_num := BB_now.(block_num); (* 这里block_num是不改的 *)
      commands := BB_now.(commands) ++ [CAsgn x e]; (* 这里是把CAsgn x e加到commands的末尾 *)
      jump_info := BB_now.(jump_info) (* 这里其实还是空 *)
    |} in

    let cmd_BB_result := cmd_BB_gen (CAsgn x e) BB_now in

    {| 
      BasicBlocks := cmd_BB_result.(BasicBlocks) ++ (basic_block_gen tl BB_next).(BasicBlocks); 
      current_block_num := BB_now.(block_num) |} (* 用剩下的cmd和更新后的BB来进一步递归 *)
  
  | CIf e c1 c2 :: tl => 
    let BB_if_branch := cmd_BB_gen (CIf e c1 c2) BB_now in 

    (* ! 这里的block_num怎么传还没想好，可能要继续在basic_block_gen_results里添加两个跳转编号，用于then/else or pre/body *)

    let BB_now' := {|
      block_num := BB_now.(block_num);
      commands := BB_now.(commands);
      jump_info := {|
        jump_kind := CJump;
        jump_dist_1 := BB_now.(block_num); (* TODO *)
        jump_dist_2 := Some (BB_now.(block_num)); (* TODO *)
        jump_condition := Some (e);
      |}
    |} in

    let BB_next := {|
      block_num := S (BB_now.(block_num)); (* TODO *)
      commands := []; (* 创建一个空的命令列表 *)
      (* 占位符，后续在递归中会修改 *)
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := 0;
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    {| 
      BasicBlocks := [BB_now] ++ BB_if_branch.(BasicBlocks) ++ (basic_block_gen tl BB_next).(BasicBlocks); 
      current_block_num := BB_now.(block_num) |}

  | CWhile pre e body :: tl => 

    let BB_next := {|
      block_num := S(BB_now.(block_num)); (* a + 1 *)
      commands := []; (* 创建一个空的命令列表 *)
      (* 占位符，后续在递归中会修改 *)
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := 0;
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_now' := {|
      block_num := BB_now.(block_num); (* TODO *)
      commands := BB_now.(commands);
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_now.(block_num); (* TODO *)
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_while_branch := cmd_BB_gen (CWhile pre e body) BB_now in

    {|
      BasicBlocks := [BB_now'] ++ BB_while_branch.(BasicBlocks) ++ (basic_block_gen tl BB_next).(BasicBlocks);
      current_block_num := BB_next.(block_num)
    |}

  end.
End basic_block_gen.


Fixpoint cmd_BB_gen (c: cmd) (BB_now: BasicBlock) : basic_block_gen_results :=
  match c with
  | CIf e c1 c2 =>

    let c1_base_block := {|
      block_num := S (BB_now.(block_num)); (* TODO *)
      commands := [];
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := 0; 
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_c1 := basic_block_gen cmd_BB_gen c1 c1_base_block in

    let c2_base_block := {|
      block_num := S (BB_c1.(current_block_num)); (* TODO *)
      commands := [];
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := 0; 
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_c2 := basic_block_gen cmd_BB_gen c2 c2_base_block in

    {|
      BasicBlocks := BB_c1.(BasicBlocks) ++ BB_c2.(BasicBlocks);
      current_block_num := BB_c2.(current_block_num)
    |}


  | CWhile pre e body => {| 
      BasicBlocks := [];
      current_block_num := BB_now.(block_num)
    |}

  | _ => {| 
      BasicBlocks := [];
      current_block_num := BB_now.(block_num)
    |}
  end.