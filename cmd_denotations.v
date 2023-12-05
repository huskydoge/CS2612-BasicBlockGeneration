Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Init.Specif.
Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Require Import Main.grammer.

Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.


Module Denotation.

Inductive val: Type :=
| Vuninit: val
| Vint (i: int64): val.

Definition state: Type := var_name -> val.

(* 下面定义统一刻画了三种算术运算的语义。*)
Definition arith_compute1_nrm
             (Zfun: Z -> Z -> Z)
             (i1 i2 i: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    i = Int64.repr res /\
    Int64.min_signed <= res <= Int64.max_signed.


Definition arith_compute1_err
             (Zfun: Z -> Z -> Z)
             (i1 i2: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    res < Int64.min_signed \/ res > Int64.max_signed.


(* 下面定义给出了更高level的定义，但实际上在我们这里可能并不需要，因为本质上D1, D2就是i1, i2 *)
Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_nrm Zfun i1 i2 i.


Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute1_err Zfun i1 i2.


(* 一个表达式的语义分为两部分：求值成功的情况与求值出错的情况。*)
Module EDenote.

Record EDenote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

End EDenote.

Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x) (at level 1).
Notation "x '.(err)'" := (EDenote.err x) (at level 1).

Ltac any_nrm x := exact (EDenote.nrm x).

Ltac any_err x := exact (EDenote.err x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed;
    err := fun s =>
             n < Int64.min_signed \/
             n > Int64.max_signed;
  |}.


Definition var_sem (X: var_name): EDenote :=
  {|
    nrm := fun s i => s X = Vint i;
    err := fun s => s X = Vuninit;
  |}.


(**变量与常量构成element，与compiler.pdf一致*)
Definition element_sem (e: element): EDenote :=
  match e with 
  | EConst n => const_sem n
  | EVar var_name => var_sem var_name
  end.



Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
            arith_sem1_err Zfun D1.(nrm) D2.(nrm);
  |}.


(* 一元运算的行为 *)
Definition neg_compute_nrm (i1 i: int64): Prop :=
  i = Int64.neg i1 /\
  Int64.signed i1 <> Int64.min_signed.

Definition neg_compute_err (i1: int64): Prop :=
  Int64.signed i1 = Int64.min_signed.

Definition not_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 0 \/
  i1 = Int64.repr 0 /\ i = Int64.repr 1.

Definition neg_sem_nrm
  (D1: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
    exists i1, D1 s i1 /\ neg_compute_nrm i1 i.


Definition neg_sem_err
  (D1: state -> int64 -> Prop)
  (s: state): Prop :=
    exists i1, D1 s i1 /\ neg_compute_err i1.


Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.


Definition not_sem_nrm
  (D1: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
    exists i1, D1 s i1 /\ not_compute_nrm i1 i.


Definition not_sem (D1: EDenote): EDenote :=
  {|
  nrm := not_sem_nrm D1.(nrm);
  err := D1.(err);
  |}.


Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

(* 定义除法的行为为compute2 *)
Definition arith_compute2_nrm
  (int64fun: int64 -> int64 -> int64)
  (i1 i2 i: int64): Prop :=
    i = int64fun i1 i2 /\
    Int64.signed i2 <> 0 /\
    (Int64.signed i1 <> Int64.min_signed \/
    Int64.signed i2 <> - 1).


Definition arith_compute2_err (i1 i2: int64): Prop :=
  Int64.signed i2 = 0 \/
  (Int64.signed i1 = Int64.min_signed /\
  Int64.signed i2 = - 1).
  

Definition arith_sem2_err
  (D1 D2: state -> int64 -> Prop)
  (s: state): Prop :=
    exists i1 i2,
      D1 s i1 /\ D2 s i2 /\
      arith_compute2_err i1 i2.


Definition arith_sem2_nrm
  (int64fun: int64 -> int64 -> int64)
  (D1 D2: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
    exists i1 i2,
      D1 s i1 /\ D2 s i2 /\
      arith_compute2_nrm int64fun i1 i2 i.


Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
    arith_sem2_err D1.(nrm) D2.(nrm);
  |}.


Definition cmp_compute_nrm
             (c: comparison)
             (i1 i2 i: int64): Prop :=
  i = if Int64.cmp c i1 i2
      then Int64.repr 1
      else Int64.repr 0.


Definition cmp_sem_nrm
  (c: comparison)
  (D1 D2: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
exists i1 i2,
D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.


Definition cmp_sem c (D1 D2: EDenote): EDenote :=
{|
nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
err := D1.(err) ∪ D2.(err);
|}.

(* 短路求值的情况 *)
Definition SC_and_compute_nrm (i1 i: int64): Prop :=
  i1 = Int64.repr 0 /\ i = Int64.repr 0.

Definition SC_or_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 1.

Definition NonSC_and (i1: int64): Prop :=
  Int64.signed i1 <> 0.

Definition NonSC_or (i1: int64): Prop :=
  i1 = Int64.repr 0.

Definition NonSC_compute_nrm (i2 i: int64): Prop :=
  i2 = Int64.repr 0 /\ i = Int64.repr 0 \/
  Int64.signed i2 <> 0 /\ i = Int64.repr 1.

(** 所有运算符的语义中，二元布尔运算由于涉及短路求值，其定义是最复杂的。*)

Definition and_sem_nrm
  (D1 D2: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
    exists i1,
      D1 s i1 /\
      (SC_and_compute_nrm i1 i \/
      NonSC_and i1 /\
    exists i2,
      D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition and_sem_err
  (D1: state -> int64 -> Prop)
  (D2: state -> Prop)
  (s: state): Prop :=
    exists i1,
      D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

Definition or_sem_nrm
  (D1 D2: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
  exists i1,
    D1 s i1 /\
    (SC_or_compute_nrm i1 i \/
    NonSC_or i1 /\
  exists i2,
    D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
  (D1: state -> int64 -> Prop)
  (D2: state -> Prop)
  (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
  |}.


Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2
  | OMinus => arith_sem1 Z.sub D1 D2
  | OMul => arith_sem1 Z.mul D1 D2
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.


(* ! 这里改成了Definition，因为expr不会被展开 *)
Definition eval_expr (e: expr): EDenote :=
  match e with
  | EBinop op e1 e2 =>
      binop_sem op (element_sem e1) (element_sem e2)
  | EUnop op e1 =>
      unop_sem op (element_sem e1)
  end.

Module EmptyEDenote.
Definition EmptyEDenote: EDenote :=
  {|
    nrm := ∅;
    err := ∅;
  |}.

End EmptyEDenote.

Module CDenote.

Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.
  
End CDenote.

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Notation "x '.(inf)'" := (CDenote.inf x)
  (at level 1).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  end.

(** 空语句的语义：*)

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    inf := ∅;
  |}.


(** 赋值语句的语义：*)

Definition asgn_sem
             (X: var_name)
             (D: EDenote): CDenote :=
  {|
    nrm := fun s1 s2 =>
      exists i,
        D.(nrm) s1 i /\ s2 X = Vint i /\
        (forall Y, X <> Y -> s2 Y = s1 Y);
    err := D.(err);
    inf := ∅;
  |}.


(** 顺序执行语句的语义：*)
Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.


Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (Int64.repr 0)).


Module WhileSem.
  Fixpoint iter_nrm_lt_n
             (D0: EDenote)
             (D1: CDenote)
             (PRE: CDenote)
             (n: nat):
    state -> state -> Prop :=
    match n with
    | O => ∅
    | S n0 =>
        (PRE.(nrm) ∘ test_true D0 ∘ ((D1.(nrm) ∘ iter_nrm_lt_n D0 D1 PRE n0))) ∪
        (PRE.(nrm) ∘ (test_false D0))
    end.
  
  Fixpoint iter_err_lt_n
             (D0: EDenote)
             (D1: CDenote)
             (PRE: CDenote)
             (n: nat): state -> Prop :=
    match n with
    | O => ∅
    | S n0 =>
       PRE.(err) ∪ (PRE.(nrm) ∘ test_true D0 ∘ ((D1.(nrm) ∘ iter_err_lt_n D0 D1 PRE n0) ∪ D1.(err))) ∪ (PRE.(nrm) ∘ D0.(err))
    end.
  
  Definition is_inf
               (D0: EDenote)
               (D1: CDenote)
               (PRE: CDenote)
               (X: state -> Prop): Prop :=
    X ⊆ PRE.(nrm) ∘ test_true D0 ∘
          ((D1.(nrm) ∘ X) ∪
           D1.(inf)).
  End WhileSem.

Definition while_sem
  (D0: EDenote)
  (D1: CDenote)
  (PRE: CDenote): CDenote :=
{|
nrm := ⋃ (WhileSem.iter_nrm_lt_n D0 D1 PRE);
err := ⋃ (WhileSem.iter_err_lt_n D0 D1 PRE);
inf := Sets.general_union (WhileSem.is_inf D0 D1 PRE);
|}.
  
Definition if_sem
  (D0: EDenote)
  (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
    (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
    (test_true D0 ∘ D1.(err)) ∪
    (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
    (test_false D0 ∘ D2.(inf))
  |}.
End Denotation.

