Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Main.grammer.

(* Create a global variable recording the current block number *)
Definition global_block_num : nat := 0.
  
Inductive JumpKind : Type :=
| UJump  (* Represents an unconditional jump *)
| CJump.   (* Represents a conditional jump *)


(* Definition of BlockInfo *)
Record BlockInfo : Type := {
  jump_kind : JumpKind; (* Represents the type of jump instruction *)
  jump_dist_1 : nat; (* Represents the target block's identifier or label *)
  jump_dist_2 : option nat; (* Represents the target block's identifier or label, used for if branches *)
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
Notation "s '.(jmp)'" := (jump_info s) (at level 1).



(* Definition
    - cmds is the list of remaining commands that need to be processed.
    - BB_now is the currently constructed basic block, which starts with an empty list of commands 
      and has a jump information specified by end_info.
*)
Fixpoint basic_block_gen (cmds: list cmd) (BB_now: BasicBlock): list BasicBlock :=
  match cmds with
  | [] =>
    (* No more commands, return the current basic block *)
    [BB_now]

    (* 这里是表示取列表的头元素为CAsgn的情况，:: tl表示的是[列表剩下的所有元素] *)
  | CAsgn x e :: tl =>
    (* Add the assignment command to the current basic block *)
    let BB_next := {|
      block_num := BB_now.(block_num); (* 这里block_num是不改的 *)
      commands := BB_now.(commands) ++ [CAsgn x e]; (* 这里是把CAsgn x e加到commands的末尾 *)
      jump_info := BB_now.(jump_info) (* 这里其实还是空 *)
    |} in
    basic_block_gen tl BB_next (* 用剩下的cmd和更新后的BB来进一步递归 *)

  (* block_num的设置逻辑还要调整 *)
  | CIf e c1 c2 :: tl =>
    let BB_then := {|
      block_num := S (BB_now.(block_num)); 
      commands := c1;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := S (BB_now.(block_num)); (* 不知道跳哪去了 *)
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in
    let BB_else := {|
      block_num := S (BB_then.(block_num));
      commands := c2;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := S (BB_then.(block_num)) + length c2; (* 不知道跳哪去了 *)
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in
    let BB_now' := {|
      block_num := BB_now.(block_num);
      commands := BB_now.(commands);
      jump_info := {|
        jump_kind := CJump;
        jump_dist_1 := BB_then.(block_num);
        jump_dist_2 := BB_else.(block_num);
        jump_condition := e;
      |}
    |} in
    BB_now' :: (BB_then :: BB_else :: basic_block_gen tl BB_else)

  (* | CWhile pre e body :: tl =>
    let BB_next := {|
      block_num := S (BB_now.(block_num));
      commands := CWhile pre e body :: tl;
      jump_info := {|
        jump_kind := CJump;
        jump_dist_1 := S (BB_now.(block_num));
        jump_dist_2 := Some (S (BB_now.(block_num)) + length body);
        jump_condition := Some e
      |}
    |} in
    BB_now :: (basic_block_gen pre BB_now ++ basic_block_gen body BB_next ++ basic_block_gen tl BB_next) *)
  end.