From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From osiris.typing Require Import side stype.
From osiris.encodings Require Import channel stype.
From iris.base_logic Require Import invariants.

Section Examples.
  Context `{!heapG Σ} (N : namespace).

  Definition seq_example : expr :=
    (let: "c" := new_chan #() in
     send "c" #Left #5;;
     recv "c" #Right)%E.

  Definition par_example : expr :=
    (let: "c" := new_chan #() in
     Fork(send "c" #Left #5);;
     recv "c" #Right)%E.

  Definition par_2_example : expr :=
    (let: "c" := new_chan #() in
     Fork(let: "v" := recv "c" #Right in send "c" #Right ("v"+#2));;
     send "c" #Left #5;;recv "c" #Left)%E.

  Definition heaplet_example : expr :=
    (let: "c" := new_chan #() in
     Fork(send "c" #Left (ref #5));;
     !(recv "c" #Right))%E.

  Definition channel_example : expr :=
    (let: "c" := new_chan #() in
     Fork(
         let: "c'" := new_chan #() in
         send "c" #Left ("c'");; send "c'" #Left #5);;
     let: "c'" := recv "c" #Right in
     recv "c'" #Right
    )%E.

  Definition bad_seq_example : expr :=
    (let: "c" := new_chan #() in
     let: "v" := recv "c" #Right in
     send "c" #Left #5;; "v")%E.

  Definition bad_par_example : expr :=
    (let: "c" := new_chan #() in
     Fork(#());;
     recv "c" #Right)%E.

  Definition bad_interleave_example : expr :=
    (let: "c" := new_chan #() in
     let: "c'" := new_chan #() in
     Fork(recv "c" #Right;; send "c'" #Right #5);;
     recv "c'" #Left;; send "c" #Left #5)%E.
  
End Examples.