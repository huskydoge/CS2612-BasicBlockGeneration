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
Open Scope nat.


Program Fixpoint bla (n:nat) {measure n} :=
match n with
| 0 => 0
| S n' => S (bla n')
end.

Lemma obvious: forall n, bla n = n. 
induction n. reflexivity.
(* I'm stuck here. For a normal fixpoint, I could for instance use 
simpl. rewrite IHn. reflexivity. But here, I couldn't find a tactic 
transforming bla (S n) to S (bla n).*)