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
Import ListNotations.
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

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (x1 x2: var_name) : expr
  | EUnop (op: unop) (e: x) : expr.


(* Minimal Compute Unit *)
Inductive cmd: Type :=
| CAsgn (x: var_name) (e: expr)
| CIf (e: expr) (c1 c2: list cmd)
| CWhile (pre: list cmd) (e: expr) (body: list cmd).

