(** This file demonstrates how Löb induction can be used to prove subtyping
of recursive protocols that combine polymorphism and asynchornous subtyping.
In pseudo syntax, the subtyping we show is:

     μ rec. ! (X,Y:★) (X ⊸ Y). !X. ?Y. rec
  <: μ rec. ! (X1,X2:★) (X1 ⊸ bool). !X1. !(X2 ⊸ int). !X2. ?bool. ?int. rec
*)
From actris.channel Require Import proofmode.
From actris.logrel Require Import subtyping_rules.

Section basics.
  Context `{heapG Σ, chanG Σ}.

  Definition prot1_aux (rec : lsty Σ) : lsty Σ :=
    <!! X Y> TY (X ⊸ Y); <!!> TY X; <??> TY Y; rec.
  Instance prot1_aux_contractive : Contractive prot1_aux.
  Proof. solve_proto_contractive. Qed.
  Definition prot1 := lty_rec prot1_aux.

  Definition prot1'_aux (rec : lsty Σ) : lsty Σ :=
    <!! X Y> TY (X ⊸ Y); <!!> TY X; <??> TY Y;
    <!! X Y> TY (X ⊸ Y); <!!> TY X; <??> TY Y; rec.
  Instance prot1'_aux_contractive : Contractive prot1'_aux.
  Proof. solve_proto_contractive. Qed.
  Definition prot1' := lty_rec prot1'_aux.

  Definition prot2_aux (rec : lsty Σ) : lsty Σ :=
    <!! X> TY (X ⊸ lty_bool); <!!> TY X;
    <!! Y> TY (Y ⊸ lty_int); <!!> TY Y;
    <??> TY lty_bool; <??> TY lty_int; rec.
  Instance prot2_aux_contractive : Contractive prot2_aux.
  Proof. solve_proto_contractive. Qed.
  Definition prot2 := lty_rec prot2_aux.

  Lemma rec_swap_example : prot1 <: prot2.
  Proof.
    iApply (lty_le_trans _ prot1').
    { iLöb as "IH".
      iDestruct (lty_le_rec_unfold (prot1_aux)) as "[H1 _]".
      iDestruct (lty_le_rec_unfold (prot1'_aux)) as "[_ H2]".
      iApply (lty_le_trans with "H1"). iApply (lty_le_trans with "[] H2").
      iIntros (X Y). iExists X, Y. iIntros "!>!>!>".
      iApply (lty_le_trans with "H1").
      iIntros (X' Y'). iExists X', Y'. iIntros "!>!>!>".
      iApply "IH". }
    iApply lty_le_rec_internal.
    iIntros (S1 S2) "#Hrec".
    iIntros (X). iExists X, lty_bool. iIntros "!> !>" (Y).
    iApply (lty_le_trans _ (<??> TY lty_bool; <!!> TY Y ⊸ lty_int;
                            <!!> TY Y; <??> TY lty_int; S2)); last first.
    { iApply (lty_le_trans _ (<!!> TY Y ⊸ lty_int; <??> TY lty_bool;
                              <!!> TY Y; <??> TY lty_int; S2)).
      { iApply lty_le_swap_recv_send. }
      iModIntro. iApply lty_le_swap_recv_send. }
    iModIntro. iExists Y, lty_int. by iIntros "!>!>!>".
  Qed.
End basics.
