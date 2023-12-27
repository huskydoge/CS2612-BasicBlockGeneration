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
    BBnum' =
    (list_cmd_BB_gen cmd_BB_gen c2
        (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) BB_else BB_num2).(next_block_num) /\
    BBnow'0.(cmd) = BB_else.(cmd) ++ BBcmds /\
    BBnow'0.(block_num) = BB_else.(block_num) /\
    (list_cmd_BB_gen cmd_BB_gen c2
        (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) BB_else BB_num2).(BasicBlocks) ++
    (list_cmd_BB_gen cmd_BB_gen c2
        (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) BB_else BB_num2).(BBn) :: nil =
    (BBs ++ BBnow' :: nil ++ BB_now_then :: nil ++ BBs_then) ++ (BBnow'0 :: nil) ++ BBs'

*)

Lemma list_cmd_BB_gen_aux1: