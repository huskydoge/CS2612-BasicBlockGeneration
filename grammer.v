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


(* Definition void_ptr (A : Type) := option A.

Definition null_ptr {A : Type} : void_ptr A := None. *)

(* Definition null_ptr  := void_ptr None. *)


(* Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A. *)


Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr) : expr
  | EUnop (op: unop) (e: expr) : expr.


(* Minimal Compute Unit *)
Inductive cmd: Type :=
| CAsgn (x: var_name) (e: expr)
| CIf (e: expr) (c1 c2: list cmd)
| CWhile (pre: list cmd) (e: expr) (body: list cmd).

