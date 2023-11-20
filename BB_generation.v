Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition var_name: Type := string.

(* Syntax definition for expr, would be modified later according to detailed requirements *)
(* Note that here the conditions for If and While are <nat> not <expr> *)
(* ! ATTENTION! expr is defined recursively, but actually it shouldn't. 
   ! We should modify it and get an abstract block <expr> and construct all the expressions using expr.
   ! e.g. Here c1 c2 shouldn't be recursive? *)
Inductive expr : Type :=
  | CAsgn (x : var_name) (a : nat)
  | CIf (b : nat) (c1 c2 : expr)
  | CWhile (b : nat) (c : expr).

  
Inductive JumpKind : Type :=
| UJump  (* Represents an unconditional jump *)
| CJump.   (* Represents a conditional jump *)


(* Definition of BlockInfo *)
Record BlockInfo : Type := {
  jump_kind : JumpKind; (* Represents the type of jump instruction *)
  jump_target : nat; (* Represents the target block's identifier or label *)
  jump_condition : option nat (* Represents the condition for conditional jumps, if any *)
}.


(* Definition of BasicBlock *)
Record BasicBlock : Type := {
  commands : list expr; (* Represents a command *)
  jump_info : BlockInfo (* Defines the jump information *)
}.

Notation "s '.(cmd)'" := (commands s) (at level 1).
Notation "s '.(jmp)'" := (jump_info s) (at level 1).



(* Definition
    - cmds is the list of remaining commands that need to be processed.
    - BB_now is the currently constructed basic block, which starts with an empty list of commands 
      and has a jump information specified by end_info.
*)
Fixpoint basic_block_gen (cmds: list expr) (BB_now: BasicBlock): list BasicBlock :=
    match cmds with 
    | [] => [BB_now]

    | CAsgn x a :: rest_cmds => 
        let BB_next := {| 
            commands := BB_now.(cmd) ++ [CAsgn x a]; jump_info := jump_info BB_now |} in
        basic_block_gen rest_cmds BB_next

    | _ => [BB_now]
    end.