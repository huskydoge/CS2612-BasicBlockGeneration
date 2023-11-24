Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Require Import Coq.Init.Specif.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
(* Local Open Scope sets. *)


(* Each assignment statement is evaluated only once*)

Definition var_name: Type := string.
Definition const: Type := Z.

Definition Int: Type := Z.
Definition Char: Type := string.

Inductive binop : Type :=
  | OOr | OAnd
  | OLt | OLe | OGt | OGe | OEq | ONe
  | OPlus | OMinus | OMul | ODiv | OMod.

Inductive unop : Type :=
  | ONot | ONeg.

Inductive Const_or_Var: Type :=
  | EConst (n : Z): Const_or_Var
  | EVar (x: var_name): Const_or_Var.

Inductive expr : Type :=
  | EBinop (op: binop) (e1 e2: Const_or_Var) : expr
  | EUnop (op: unop) (e1: Const_or_Var) : expr.


(* Minimal Compute Unit *)
Inductive cmd: Type :=
| CAsgn (x: var_name) (e: expr)
| CIf (e: expr) (c1 c2: list cmd)
| CWhile (pre: list cmd) (e: expr) (body: list cmd).


Section cmd_len.

Variable cmd_len : cmd -> nat.

Fixpoint cmd_list_len (cl : list cmd) : nat :=
  match cl with
  | [] => 0
  | c :: tl => cmd_len c + cmd_list_len tl
  end.

End cmd_len.

Fixpoint cmd_len (c : cmd) : nat :=
  match c with
  | CAsgn _ _ => 1
  | CIf _ c1 c2 => 1 + cmd_list_len cmd_len c1 + cmd_list_len cmd_len c2
  | CWhile _ _ body => 1 + cmd_list_len cmd_len body
  end.
