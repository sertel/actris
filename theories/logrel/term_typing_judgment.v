(** This file contains the definitions of the semantic typing judgment
[Γ ⊨ e : A ⫤ Γ'], indicating that in context [Γ], the expression [e] has type
[A], producing a new context [Γ']. The context is allowed to change to
accomodate things like changing the type of a channel after a receive.

In addition, we use the adequacy of Iris in order to show type soundness:
programs which satisfy the semantic typing relation are safe. That is,
semantically well-typed programs do not get stuck. *)
From iris.heap_lang Require Import metatheory adequacy.
From actris.logrel Require Export term_types.
From actris.logrel Require Import environments.
From iris.proofmode Require Import tactics.

(** The semantic typing judgment *)
Definition ltyped `{!heapG Σ}
    (Γ Γ' : gmap string (ltty Σ)) (e : expr) (A : ltty Σ) : iProp Σ :=
  (■ ∀ vs, env_ltyped Γ vs -∗
           WP subst_map vs e {{ v, ltty_car A v ∗ env_ltyped Γ' vs }})%I.

Notation "Γ ⊨ e : A ⫤ Γ'" := (ltyped Γ Γ' e A)
  (at level 100, e at next level, A at level 200).
Notation "Γ ⊨ e : A" := (Γ ⊨ e : A ⫤ Γ)
  (at level 100, e at next level, A at level 200).

Lemma ltyped_safety `{heapPreG Σ} e σ es σ' e' :
  (∀ `{heapG Σ}, ∃ A Γ', ⊢ ∅ ⊨ e : A ⫤ Γ') →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty. apply (heap_adequacy Σ NotStuck e σ (λ _, True))=> // ?.
  destruct (Hty _) as (A & Γ' & He).
  iDestruct (He) as "He".
  iSpecialize ("He" $!∅).
  iSpecialize ("He" with "[]"); first by rewrite /env_ltyped.
  iEval (rewrite -(subst_map_empty e)). iApply (wp_wand with "He"); auto.
Qed.
