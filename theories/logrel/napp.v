From actris.logrel Require Import term_typing_rules session_types subtyping_rules.
From actris.channel Require Import proofmode.

Section with_Σ.
  Context `{!heapG Σ}.

  Fixpoint lty_napp (R : lsty Σ) (n : nat) :=
    match n with
    | O => END
    | S n => R <++> lty_napp R n
    end%lty.

  Lemma lty_napp_S_l R n :
    lty_napp R (S n) ≡ (R <++> lty_napp R n)%lty.
  Proof. eauto. Qed.

  Lemma lty_napp_S_r R n :
    lty_napp R (S n) ≡ (lty_napp R n <++> R)%lty.
  Proof.
    induction n; simpl; [ by rewrite lty_app_end_l lty_app_end_r | ].
    rewrite -(assoc _ _ (lty_napp R n) R). by rewrite -IHn.
  Qed.

  Lemma lty_napp_flip R n :
     (lty_napp R n <++> R)%lty ≡ (R <++> lty_napp R n)%lty.
  Proof. by rewrite -lty_napp_S_l lty_napp_S_r. Qed.

  Lemma lty_napp_swap T R n :
    R <++> T <: T <++> R -∗
    lty_napp R n <++> T <: T <++> lty_napp R n.
  Proof.
    iIntros "#Hle".
    iInduction n as [|n] "IHn";
      [ by rewrite lty_app_end_l lty_app_end_r | ].
    rewrite -assoc.
    iApply lty_le_trans.
    { iApply lty_le_app; [ iApply lty_le_refl | iApply "IHn" ]. }
    rewrite assoc.
    iApply lty_le_trans.
    { iApply lty_le_app; [ iApply "Hle" | iApply lty_le_refl ]. }
    rewrite assoc. iApply lty_le_refl.
  Qed.

End with_Σ.
