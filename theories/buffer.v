From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth.
From iris.base_logic.lib Require Import auth.
Set Default Proof Using "Type".

(* Buffer CMRA *)
Definition buff_type := list val.

Definition buffUR : ucmraT :=
  optionUR (exclR (leibnizC (buff_type))).

Definition to_buff (b : buff_type) : buffUR :=
  Excl' (b: leibnizC buff_type).

Class buffG (Σ :gFunctors) := BuffG {
  buffG_authG :> authG Σ buffUR;
}.

Definition buffΣ : gFunctors :=
  #[GFunctor (authR buffUR)].

Instance subG_buffG {Σ} :
  subG buffΣ Σ → buffG Σ.
Proof. solve_inG. Qed.

Section buff.
  Context `{!buffG Σ} (N : namespace).

  Lemma excl_eq γ x y :
      own γ (● to_buff y) -∗ own γ (◯  to_buff x) -∗ ⌜x = y⌝%I.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
    apply auth_valid_discrete_2 in Hvalid.
    destruct Hvalid as [Hincl _].
    apply Excl_included in Hincl.
    unfold to_buff.
    rewrite Hincl.
    iFrame.
    eauto.
  Qed.

  Lemma excl_update γ x y z :
      own γ (● to_buff y) -∗ own γ (◯  to_buff x) -∗ |==> own γ (● to_buff z) ∗ own γ (◯  to_buff z).
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_update_2 with "Hauth Hfrag") as "H".
    { eapply (auth_update _ _ (to_buff z) (to_buff z)).
      eapply option_local_update.
      eapply exclusive_local_update. done. }
    rewrite own_op.
    done.
  Qed.

End buff.
