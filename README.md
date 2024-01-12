# CS2612-Basic Block Generation
> SJTU | CS 2612, Programming Languages and Compilers - Final Project

This repo contains the files for the final project of CS2612, regarding the correctness of Basic Block generation in compiler design. The Coq files can be successfully compiled with Coq version 8.12.0.

We thank Prof. Cao and two TAs for their great help throughout the semester as well as personalized guidance for our project.

## Compilation Order

- `grammar.v`: the basic grammar of the task
- `BB_generation.v`: defines the generation process of the Basic Blocks.
- `BB_denotations.v`: defines the denotation of Basic Blocks.
- `cmd_denotations.v`: defines the notations of original SimpleWhile commands.
- `utils.v`: some fundamental lemmas used for subsequent tasks
- `BB_gen_properties.v`: defines and proves some lemmas regarding the basic properties of the generation process of Basic Blocks.
- `BB_aux_proof.v`: defines important propositions and proves lemmas using `BB_gen_properties.v` and `utils.v`.
- `BB_sem_asgn_equiv.v`: proves the equivalence of a single `CAsgn` command and the corresponding Basic Block results.
- `BB_sem_if_equiv.v`: proves the equivalence of a single `CIf` command and the corresponding Basic Block results.
- `BB_sem_while_equiv.v`: **NOT** required after discussion with the instructor. But it must be compiled for the final theorem.
- `BB_sem_equiv.v`: proves the final theorem integrating the three types of commands.

## Notice

- All the `while` branches and theorems (including those in inductive proofs) have be Admitted with the acknowledgement of the instructor.
- We assume that the program will never go wrong or infinite. Therefore, we have Admitted the following lemmas: `true_or_false_classic1`, `true_or_false_classic2`, `No_err_and_inf_for_expr`.
- For the `CIf` case, we have assumed that the commands in the branches `c1` and `c2` cannot be `nil` with the acknowledgement of the instructor.
- We have proved all the theorems except two: `an_over_pass_bridge` and `BB_list_sem_simplify_r` (both in `BB_aux_proof.v`). The two theorems is used in the `If` branch of the `Pcons` part of the main theorem. Consider the structure `BBs_if ++ BBnext :: BBs` where `BBs_if` is the generated result of the first `CIf` command and `Bnrm (BB_list_sem (BBs_if ++ BBnext :: BBs)) bs1 bs2`. Given the requirements stated in the lemma, we claim that there exists a middle state `x` such that `Bnrm (BB_list_sem BBs_if) bs1 x` and `Bnrm (BB_list_sem (BBnext :: BBs)) x bs2`. We believe that it is theoretically correct.