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

  | CIf e c1 c2 :: tl =>
    (*
        Structure: If | Then | Else | Next, each of them represents a basic block
        Corresponds to BB_now' | BB_then | BB_else | BB_next
        Block_num is set to be a | a + 2 | a + 3 | a + 1
    *)
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

    let BB_then := {|
      block_num := S (BB_next.(block_num)); (* a + 2 *)
      commands := c1;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_next.(block_num); 
        jump_dist_2 := None; 
        jump_condition := None
      |}
    |} in

    let BB_else := {|
      block_num := S (BB_then.(block_num)); (* a + 3 *)
      commands := c2;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_next.(block_num); (* a + 1 *)
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
        jump_dist_2 := Some (BB_else.(block_num));
        jump_condition := Some (e);
      |}
    |} in
    BB_now' :: (BB_then :: BB_else :: basic_block_gen tl BB_next)

  | CWhile pre e body :: t1 => 
    (*
        Structure: Now | Pre | Body | Next, each of them represents a basic block
        Corresponds to BB_now' | BB_pre | BB_else | BB_next
        Block_num is set to be a | a + 2 | a + 3 | a + 1
    *)
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
    
    let BB_pre := {|
      block_num := S (BB_next.(block_num)); (* a + 2 *)
      commands := pre;
      jump_info := {|
        jump_kind := CJump;
        jump_dist_1 := S (S (BB_next.(block_num))); (* a + 3 *)
        jump_dist_2 := Some BB_next.(block_num); (* jump out of the loop *)
        jump_condition := Some e
      |}
    |} in

    let BB_body := {|
      block_num := S (BB_pre.(block_num));
      commands := body;
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_pre.(block_num); (* a + 2 *)
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in

    let BB_now' := {|
      block_num := BB_now.(block_num);
      commands := BB_now.(commands);
      jump_info := {|
        jump_kind := UJump;
        jump_dist_1 := BB_pre.(block_num);
        jump_dist_2 := None;
        jump_condition := None
      |}
    |} in
    
    BB_now' :: (BB_pre :: BB_body :: basic_block_gen t1 BB_next)
  end.
