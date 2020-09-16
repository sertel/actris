(** This file contains the definitions of the semantic typing judgment
[Γ ⊨ e : A ⫤ Γ'], indicating that in context [Γ], the expression [e] has type
[A], producing a new context [Γ']. The context is allowed to change to
accomodate things like changing the type of a channel after a receive.

In addition, we use the adequacy of Iris in order to show type soundness:
programs which satisfy the semantic typing relation are safe. That is,
semantically well-typed programs do not get stuck. *)
From iris.heap_lang Require Import metatheory adequacy.
From actris.logrel Require Export term_types.
From actris.logrel Require Export environments.
From iris.proofmode Require Import tactics.

(** The semantic typing judgment *)
Definition ltyped `{!heapG Σ}
    (Γ1 Γ2 : env Σ) (e : expr) (A : ltty Σ) : iProp Σ :=
  tc_opaque (■ ∀ vs, env_ltyped vs Γ1 -∗
    WP subst_map vs e {{ v, ltty_car A v ∗ env_ltyped vs Γ2 }})%I.
Instance: Params (@ltyped) 2 := {}.

Notation "Γ1 ⊨ e : A ⫤ Γ2" := (ltyped Γ1 Γ2 e A)
  (at level 100, e at next level, A at level 200).
Notation "Γ ⊨ e : A" := (Γ ⊨ e : A ⫤ Γ)
  (at level 100, e at next level, A at level 200).

Section ltyped.
  Context `{!heapG Σ}.

  Global Instance ltyped_plain Γ1 Γ2 e A : Plain (ltyped Γ1 Γ2 e A).
  Proof. rewrite /ltyped /=. apply _. Qed.
  Global Instance ltyped_ne n :
    Proper (dist n ==> dist n ==> (=) ==> dist n ==> dist n) (@ltyped Σ _).
  Proof. solve_proper. Qed.
  Global Instance ltyped_proper :
    Proper ((≡) ==> (≡) ==> (=) ==> (≡) ==> (≡)) (@ltyped Σ _).
  Proof. solve_proper. Qed.
  Global Instance ltyped_Permutation :
    Proper ((≡ₚ) ==> (≡ₚ) ==> (=) ==> (≡) ==> (≡)) (@ltyped Σ _).
  Proof.
    intros Γ1 Γ1' HΓ1 Γ2 Γ2' HΓ2 e ? <- A ? <-. rewrite /ltyped /=.
    setoid_rewrite HΓ1. by setoid_rewrite HΓ2.
  Qed.
End ltyped.

Lemma ltyped_safety `{heapPreG Σ} e σ es σ' e' :
  (∀ `{heapG Σ}, ∃ A, ⊢ [] ⊨ e : A ⫤ []) →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty. apply (heap_adequacy Σ NotStuck e σ (λ _, True))=> // ?.
  destruct (Hty _) as (A & He). iIntros "_".
  iDestruct (He $!∅ with "[]") as "He"; first by rewrite /env_ltyped.
  iEval (rewrite -(subst_map_empty e)). iApply (wp_wand with "He"); auto.
Qed.

Theorem ltyped_mono `{!heapG Σ} Γ1 Γ1' Γ2 Γ2' e τ1 τ2 :
  (■ ∀ vs, env_ltyped Γ1 vs -∗ env_ltyped Γ1' vs) -∗
  (■ ∀ vs, env_ltyped Γ2' vs -∗ env_ltyped Γ2 vs) -∗
  τ1 <: τ2 -∗ (Γ1' ⊨ e : τ1 ⫤ Γ2') -∗ (Γ1 ⊨ e : τ2 ⫤ Γ2).
Proof.
  iIntros "#HΓ1 #HΓ2 #Hle #Hltyped" (vs) "!> Henv".
  iDestruct ("HΓ1" with "Henv") as "Henv".
  iDestruct ("Hltyped" with "Henv") as "Hltyped'".
  iApply (wp_wand with "Hltyped'").
  iIntros (v) "[H1 Henv]".
  iDestruct ("HΓ2" with "Henv") as "Henv".
  iFrame "Henv". by iApply "Hle".
Qed.
