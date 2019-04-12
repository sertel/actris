From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth.
From iris.base_logic.lib Require Import auth.
Set Default Proof Using "Type".

Definition exclUR (A : Type) : ucmraT :=
  optionUR (exclR (leibnizC A)).

Class auth_exclG (A : Type) (Σ :gFunctors) :=
  AuthExclG {
      exclG_authG :> authG Σ (exclUR A);
    }.

Definition auth_exclΣ (A : Type) : gFunctors :=
  #[GFunctor (authR (exclUR A))].

Instance subG_auth_exclG (A : Type) {Σ} :
  subG (auth_exclΣ A) Σ → (auth_exclG A) Σ.
Proof. solve_inG. Qed.

Definition to_auth_excl {A : Type} (a : A) : exclUR A :=
  Excl' (a: leibnizC A).

Section auth_excl.
  Context `{!auth_exclG A Σ}.

  Lemma excl_eq γ x y :
    own γ (● to_auth_excl y) -∗ own γ (◯  to_auth_excl x) -∗ ⌜x = y⌝%I.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hvalid.
    apply auth_valid_discrete_2 in Hvalid.
    destruct Hvalid as [Hincl _].
    apply Excl_included in Hincl.
    unfold to_auth_excl.
    rewrite Hincl.
    iFrame.
    eauto.
  Qed.

  Lemma excl_update γ x y z :
    own γ (● to_auth_excl y) -∗ own γ (◯  to_auth_excl x) ==∗
    own γ (● to_auth_excl z) ∗ own γ (◯  to_auth_excl z).
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_update_2 with "Hauth Hfrag") as "H".
    { eapply (auth_update _ _ (to_auth_excl z) (to_auth_excl z)).
      eapply option_local_update.
      eapply exclusive_local_update. done. }
    rewrite own_op.
    done.
  Qed.

End auth_excl.
