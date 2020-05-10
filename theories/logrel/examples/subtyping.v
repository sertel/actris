From actris.channel Require Import proofmode proto channel.
From actris.logrel Require Import subtyping_rules.
From iris.proofmode Require Import tactics.

Section basics.
  Context `{heapG Σ, chanG Σ}.

  Definition prot1_aux : (lsty Σ → lsty Σ) :=
    λ rec, (<!!X Y> TY (X ⊸ Y)%lty ; <!!> TY X;
           <??> TY Y; rec)%lty.
  Instance prot1_aux_contractive : Contractive prot1_aux.
  Proof. solve_proto_contractive. Qed.
  Definition prot1 := lty_rec prot1_aux.

  Definition prot1'_aux : (lsty Σ → lsty Σ) :=
    λ rec, (<!!X Y> TY (X ⊸ Y)%lty ; <!!> TY X;
           <??> TY Y;
           <!!X Y> TY (X ⊸ Y)%lty ; <!!> TY X;
           <??> TY Y; rec)%lty.
  Instance prot1'_aux_contractive : Contractive prot1'_aux.
  Proof. solve_proto_contractive. Qed.
  Definition prot1' := lty_rec prot1'_aux.

  Definition prot2_aux : (lsty Σ → lsty Σ) :=
    λ rec, (<!!X> TY (X ⊸ lty_bool)%lty ; <!!> TY X;
            <!!Y> TY (Y ⊸ lty_int)%lty ; <!!> TY Y;
            <??> TY lty_bool; <??> TY lty_int; rec)%lty.
  Instance prot2_aux_contractive : Contractive prot2_aux.
  Proof. solve_proto_contractive. Qed.
  Definition prot2 := lty_rec prot2_aux.

  Lemma rec_swap_example :
    ⊢ prot1 <: prot2.
  Proof.
    iApply (lty_le_trans _ prot1').
    { iLöb as "IH".
      iEval (rewrite /prot1 /prot1').
      iDestruct (lty_le_rec_unfold (prot1_aux)) as "[H1 _]".
      iDestruct (lty_le_rec_unfold (prot1'_aux)) as "[_ H2]".
      iApply (lty_le_trans with "H1"). iApply (lty_le_trans with "[] H2").
      iIntros (X Y). iExists X, Y. do 3 iModIntro.
      iApply (lty_le_trans with "H1").
      iIntros (X' Y'). iExists X', Y'. do 3 iModIntro.
      iApply "IH".
    }
    iApply lty_le_rec.
    iIntros (M1 M2) "#Hrec".
    iIntros (X). iExists X, lty_bool. iModIntro. iModIntro.
    iIntros (Y).
    iApply (lty_le_trans _ (<??> TY lty_bool ; <!!> TY Y ⊸ lty_int ;
                            <!!> TY Y ; <??> TY lty_int ; M2)); last first.
    {
      iApply (lty_le_trans _ (<!!> TY Y ⊸ lty_int ; <??> TY lty_bool ;
                              <!!> TY Y ; <??> TY lty_int ; M2)).
      { iApply lty_le_swap_recv_send. }
      iModIntro. iApply lty_le_swap_recv_send.
    }
    iModIntro. iExists Y, lty_int.
    by do 3 iModIntro.
  Qed.

End basics.
