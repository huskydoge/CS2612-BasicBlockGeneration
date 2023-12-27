Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. 
Import SetsNotation.
Require Import Coq.Logic.Classical_Prop.
Require Import compcert.lib.Integers.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope sets.
Require Import Main.grammer.
Require Import Main.cmd_denotations.
Require Import Main.BB_generation.
Require Import Coq.Lists.List.
Require Import Main.BB_denotations.
Require Import Main.BB_aux_proof.

Import Denotation.
Import EDenote.
Import CDenote.
Import EmptyEDenote.
Import BDenote.

(*
Then
    BB_num2 =
    (list_cmd_BB_gen cmd_BB_gen c1 (BBs ++ BBnow' :: nil) BB_then BB_num1).(next_block_num) /\
    BB_now_then.(cmd) = BB_then.(cmd) ++ BB_cmds_then /\
    BB_now_then.(block_num) = BB_then.(block_num) /\
    (list_cmd_BB_gen cmd_BB_gen c1 (BBs ++ BBnow' :: nil) BB_then BB_num1).(BasicBlocks) ++
    (list_cmd_BB_gen cmd_BB_gen c1 (BBs ++ BBnow' :: nil) BB_then BB_num1).(BBn) :: nil = 
    (BBs ++ BBnow' :: nil) ++ (BB_now_then :: nil) ++ BBs_then 

*)

(*
Else
     BB_num3 =
     (list_cmd_BB_gen cmd_BB_gen c2
        (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) BB_else
        BB_num2).(next_block_num) /\
     BB_now_else.(cmd) = BB_else.(cmd) ++ BB_cmds_else /\
     BB_now_else.(block_num) = BB_else.(block_num) /\
     (list_cmd_BB_gen cmd_BB_gen c2
        (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) BB_else
        BB_num2).(BasicBlocks) ++
     (list_cmd_BB_gen cmd_BB_gen c2
        (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) BB_else
        BB_num2).(BBn) :: nil =
     (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) ++
     (BB_now_else :: nil) ++ BBs_else
*)

(*
BBnow:
BB_next_num_to_asgn: BBthen的num
S BB_next_num_to_asgn: BBelse的num
SS BB_next_num_to_asgn: BBnext的num
SSS BB_next_num_to_asgn: 以BBthen为起点，下一个分配的num
*)

(* 
    - delta1 ∩ delta2 = ∅ ，一条大引理
    考虑BB1和BB2：
    - BBnum ⪦ BB_next_num_to_asgn -> BBnum ⪦ delta的num ，一条引理
    - Bnum delta ≥ BB_next_num_to_asgn 一条引理
    - delta.(next_block_num) ⪧ BBnum delta 一条引理
    - BBnum ⪦ BBnum delta -> BBnum ∉ BBnum delta 一条引理
        于是有 BB1num < delta1的num < delta1.(next_block_num) = BB_next_num_to_asgn2 ≤ BBnum delta2
        ->
        BB1num  ∉ BBnum delta2
    - 类似地证明， BB2num  ∉ BBnum delta1，但是方向是反一下
    - 再加上BB1num ≠ BB2 num ，到时候用的时候，这是已经有的条件，不需要引理
    那么 BBnumset (BB1::delta1) ∩ BBnumset (BB2::delta2) = ∅
*)

(*以生成一次BBs1，之后拿到的下一个用于分配的BB_next_num_to_asgn继续生成BBs2, 那么两段BBs的number不交*)
Lemma list_cmd_BB_gen_aux1:
    forall (BB1 BB2: BasicBlock)(BB_next_num_to_asgn: nat)(BBlist1 BBlist2: list BasicBlock)(c1 c2: list cmd),
    let next_block_num := (list_cmd_BB_gen cmd_BB_gen c1 BBlist1 BB1 BB_next_num_to_asgn).(next_block_num) in
    let res1 := to_result (list_cmd_BB_gen cmd_BB_gen c1 BBlist1 BB1 BB_next_num_to_asgn) in
    let res2 := to_result (list_cmd_BB_gen cmd_BB_gen c2 BBlist2 BB2 next_block_num) in
    exists BB_delta1 BB_delta2 BB1' BB2',
    res1 = BBlist1 ++ BB1'::nil ++ BB_delta1 /\
    res2 = BBlist2 ++ BB2'::nil ++ BB_delta2 /\
    BB_next_num_to_asgn_set (BB_delta1) ∩ BB_next_num_to_asgn_set (BB_delta2) = ∅. (*我这里先不管BB1和BB2的num，因为这个其实对应的就是then和else, 这两个blocknum都好处理*)
Proof.
Admitted.

(*生成一段BBs得到的BB*)
Lemma list_cmd_BB_gen_aux2:
    forall (BB: BasicBlock) (BB_next_num_to_asgn: nat) (BBlist: list BasicBlock) (c: list cmd),
    let next_block_num := (list_cmd_BB_gen cmd_BB_gen c BBlist BB BB_next_num_to_asgn).(next_block_num) in
    let res := to_result (list_cmd_BB_gen cmd_BB_gen c BBlist BB BB_next_num_to_asgn) in
    exists BB_delta BB',
    res = BBlist ++ BB'::nil ++ BB_delta /\
    ~ (BB_next_num_to_asgn_set (BB_delta) next_block_num).
Proof.
Admitted.