Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. 
Import SetsNotation.
Require Import compcert.lib.Integers.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.
Require Import Main.grammer.
Require Import Main.cmd_denotations.
Require Import Main.BB_generation.

Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.

Record BB_state: Type := {
  BB_num: nat;
  st: state
}.

Module BDenote.
Record BDenote: Type := {
  Bnrm: BB_state -> BB_state -> Prop;
  Berr: BB_state -> Prop;
  Binf: BB_state -> Prop
}.
End BDenote.

Import BDenote.

Definition ujmp_sem (jum_dist: nat): BDenote :=
  {|
    Bnrm := fun (bs1: BB_state) (bs2 :BB_state) =>
      bs1.(st) = bs2.(st) /\ bs2.(BB_num) = jum_dist;
    Berr := ∅;
    Binf := ∅;
  |}.


Definition test_true_jmp (D: EDenote):
  state -> Prop :=
    (fun s => exists i, D.(nrm) s i /\ Int64.signed i <> 0).


Definition test_false_jmp (D: EDenote):
  state -> Prop :=
    (fun s => D.(nrm) s (Int64.repr 0)).


Definition cjmp_sem (jmp_dist1: nat) (jmp_dist2: nat) (D: EDenote) : BDenote :=
  {|
    Bnrm := fun bs1 bs2 => ((bs1.(st) = bs2.(st)) /\ 
            ((bs2.(BB_num) = jmp_dist1) /\ (test_true_jmp D bs1.(st)) \/ ((bs2.(BB_num) = jmp_dist2) /\ (test_false_jmp D bs1.(st)))));
    Berr := ∅; (* Ignore err cases now *)
    Binf := ∅;
  |}.


Definition empty_sem : BDenote := {|
  Bnrm := ∅;
  Berr := ∅;
  Binf := ∅
|}.

Definition jmp_sem (jmp_dist1: nat) (jmp_dist2: option nat)(D: option EDenote) : BDenote :=
  match D with 
  | None => ujmp_sem jmp_dist1 (* No expr *)
  | Some D => match jmp_dist2 with
              | None => ujmp_sem jmp_dist1
              | Some jmp_dist2 => cjmp_sem jmp_dist1 jmp_dist2 D
              end
  end.

Definition BAsgn_sem (x: var_name) (e:EDenote) : BDenote := {|
  Bnrm := fun (bs1:BB_state) (bs2:BB_state) => 
     exists i,
     (e.(nrm) bs1.(st) i) /\  (bs2.(st) x = Vint i) /\ (forall y, x <> y -> bs1.(st) y = bs2.(st) y);
  Berr := fun(bs1:BB_state) => bs1.(st) ∈ e.(err);
  Binf := ∅;
|}.


Definition BJump_sem (jmp_dist1: nat) (jmp_dist2: option nat) (D: option EDenote) : BDenote := {|
  Bnrm := fun bs1 bs2 => 
    exists i,
      bs1.(st) = i.(st) /\ (jmp_sem jmp_dist1 jmp_dist2 D).(Bnrm) i bs2;
  Berr := ∅;
  Binf := ∅;
|}.

(** Now we are certain that BB only contains BAsgn and BJump cmds *)
(* The sementics for a list of BAsgn *)
Print BB_cmd.


Definition BAsgn_denote (BAsgn_cmd: BB_cmd) : BDenote :=   
  let x := BAsgn_cmd.(X) in 
  let e := BAsgn_cmd.(E) in
 {|
  Bnrm :=  fun (bs1: BB_state) (bs2: BB_state) => (BAsgn_sem x (eval_expr e)).(Bnrm) bs1 bs2 /\ (bs1.(BB_num) = bs2.(BB_num)); 
  Berr := (BAsgn_sem x (eval_expr e)).(Berr);
  Binf := ∅;
|}.



Fixpoint BAsgn_list_sem (BAsgn_list: list BB_cmd) : BDenote := 
match BAsgn_list with 
 | BAsgn_cmd :: tl =>
   {|   
      Bnrm := (BAsgn_denote BAsgn_cmd).(Bnrm) ∘ (BAsgn_list_sem tl).(Bnrm);
      Berr := (BAsgn_denote BAsgn_cmd).(Berr) ∪ (BAsgn_denote BAsgn_cmd).(Bnrm) ∘ (BAsgn_list_sem tl).(Berr);
      Binf := ∅;
  |}
  | _ =>
  {|
      Bnrm := Rels.id;
      Berr := ∅;
      Binf := ∅;
  |}
end.


Check EDenote.

Definition eval_cond_expr (e: option expr): option EDenote :=
  match e with
  | Some (EBinop op e1 e2) =>
      Some (binop_sem op (element_sem (e1)) (element_sem (e2)))
  | Some (EUnop op e1) =>
      Some (unop_sem op (element_sem (e1)))
  | None => None
  end.


(* Combine list of BAsgn and the final BJump *)
Definition BB_sem (BB: BasicBlock): BDenote := {| 
  Bnrm := 
    let jmp_dist1 := BB.(jump_info).(jump_dist_1) in
    let jmp_dist2 := BB.(jump_info).(jump_dist_2) in
    let jmp_cond := BB.(jump_info).(jump_condition) in
    (BAsgn_list_sem BB.(cmd)).(Bnrm) ∘ (BJump_sem jmp_dist1 jmp_dist2 (eval_cond_expr jmp_cond)).(Bnrm); 
  Berr := ∅;
  Binf := ∅;
|}.


(* Combine the single_step_stem to form the denotation for BB_list_sem.
   Not certain about its correctness  *)
Fixpoint BB_list_sem (BBs: list BasicBlock): BDenote := {|
  Bnrm := 
    match BBs with 
    | BB :: tl => (BB_sem BB).(Bnrm) ∘ (BB_list_sem tl).(Bnrm)
    | _ => Rels.id
    end;
  Berr := ∅;
  Binf := ∅;
|}.


(* Construct the denotation for the original cmds, should be in cmd_denotations.v 
* For debugging convenience, I have put it here
*)
Section cmd_list_sem.

Variable cmd_sem : cmd -> CDenote.

Fixpoint cmd_list_sem (cmd_list: list cmd): CDenote := {|
  nrm := 
    match cmd_list with
    | cmd :: tl => (cmd_sem cmd).(nrm) ∘ (cmd_list_sem tl).(nrm)
    | _ => Rels.id
    end;
  err := ∅;
  inf := ∅;
|}.

End cmd_list_sem.

Definition empty_CD: CDenote := {|
  nrm := ∅;
  err := ∅;
  inf := ∅;
|}.


Fixpoint cmd_sem (cmd: cmd): CDenote := {|
  nrm := 
    match cmd with 
    | CAsgn x e => (asgn_sem x (eval_expr e)).(nrm)
    | CIf e c1 c2 => (if_sem (eval_expr e) (cmd_list_sem cmd_sem c1)).(nrm)
    | CWhile pre e body => (while_sem (eval_expr e) (cmd_list_sem cmd_sem body) (cmd_list_sem cmd_sem pre)).(nrm)
    end;
  err := ∅;
  inf := ∅;
|}.



(* TODO The ultimate goal of the task *)
(* Theorem BB_gen_sound (cmds: list cmd):
  let BBs := BB_gen cmds in 
  let BBs_list := BB_list_sem BBs in
  let  *)