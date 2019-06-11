From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From osiris.typing Require Import side stype.
From osiris.encodings Require Import channel branching.
From iris.base_logic Require Import invariants.

Section BranchingExamples.
  Context `{!heapG Σ} (N : namespace).

  Definition branch_example b : expr :=
    (let: "c" := new_chan #() in
     select "c" #Left #b;;
     Fork(branch: "c" @ #Right
      left  send "c" #Right #5
      right #());;
     (if: #b then recv "c" #Left else #()))%E.

End BranchingExamples.