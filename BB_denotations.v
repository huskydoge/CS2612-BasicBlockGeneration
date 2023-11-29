Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import PL.SyntaxInCoq.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.
Require Import Main.grammer.
Require Import Main.cmd_denotations.



Definition state: Type := var_name -> int64.

Definition BB_state: Type := nat -> state.

Module BDenote.

Record BDenote: Type := {
  nrm: BB_state -> BB_state -> Prop;
  err: BB_state -> Prop;
  inf: BB_state -> Prop
}.
  
End BDenote.

Definition ujmp_sem (jum_dist: nat): BDenote :=
  {|
    nrm := fun s1 s2 =>
      exists i,
        D.(nrm) s1 i /\ s2 X = Vint i /\
        (forall Y, X <> Y -> s2 Y = s1 Y);
    err := ∅;
    inf := ∅;
  |}.