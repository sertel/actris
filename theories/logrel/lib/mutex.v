(** This file defines a new semantic type former [mutex A], which is the type of
mutexes containing a value of type [A]. Mutexes are copyable, regardless of
whether the type contained in them is copyable. This makes them very useful for
sharing affine resources (such as channels) between multiple threads.
Internally, mutexes are implemented using a spin lock and a mutable reference.
The operations for spin locks that are used by the mutex are defined in Iris.

The following operations are supported on mutexes:
- [mutex_alloc]: Takes a value and wraps it in a mutex.
- [mutex_acquire]: Acquire the mutex and return the value contained in it.
- [mutex_release]: Release the mutex, storing a given value in it.

The typing rules for these operations additionally contain a type
[mutexguard A], which represents a mutex that has been acquired. The typing
rules for the operations require the [mutex] or [mutexguard] to be in a variable
(i.e., let-bound), and the type of this variable in the typing context changes
as the mutex is acquired and released.

It is only possible to release a mutex after it has been opened. The
[mutexguard A] is not copyable, since that would allow a mutex to be released
multiple times after acquiring it once.

This type former is strongly inspired by the [Mutex] type in the standard
library of Rust, which has also been semantically modelled in the LambdaRust
project.
*)
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Export spin_lock.
From actris.logrel Require Export term_types term_typing_judgment subtyping.
From actris.logrel Require Import environments.
From actris.channel Require Import proofmode.
From iris.heap_lang Require Import metatheory.

(** Mutex functions *)
Definition mutex_alloc : val := λ: "x", (newlock #(), ref "x").
Definition mutex_acquire : val := λ: "x", acquire (Fst "x");; ! (Snd "x").
Definition mutex_release : val :=
  λ: "guard" "inner", Snd "guard" <- "inner";; release (Fst "guard").

(** Semantic types *)
Definition lty_mutex `{heapG Σ, lockG Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w,
  ∃ (γ : gname) (l : loc) (lk : val),
    ⌜ w = PairV lk #l ⌝ ∗
    is_lock γ lk (∃ v_inner, l ↦ v_inner ∗ ltty_car A v_inner))%I.

Definition lty_mutex_guard `{heapG Σ, lockG Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w,
  ∃ (γ : gname) (l : loc) (lk : val) (v : val),
    ⌜ w = PairV lk #l ⌝ ∗
    is_lock γ lk (∃ v_inner, l ↦ v_inner ∗ ltty_car A v_inner) ∗
    spin_lock.locked γ ∗ l ↦ v)%I.

Instance: Params (@lty_mutex) 3 := {}.
Instance: Params (@lty_mutex_guard) 3 := {}.

Notation "'mutex' A" := (lty_mutex A) (at level 10) : lty_scope.
Notation "'mutex_guard' A" := (lty_mutex_guard A) (at level 10) : lty_scope.

Section properties.
  Context `{heapG Σ, lockG Σ}.
  Implicit Types A : ltty Σ.

  Global Instance lty_mutex_contractive : Contractive lty_mutex.
  Proof. solve_contractive. Qed.
  Global Instance lty_mutex_ne : NonExpansive lty_mutex.
  Proof. solve_proper. Qed.

  Global Instance lty_mutex_guard_contractive :
    Contractive lty_mutex_guard.
  Proof. solve_contractive. Qed.
  Global Instance lty_mutex_guard_ne : NonExpansive lty_mutex_guard.
  Proof. solve_proper. Qed.

  Lemma lty_le_mutex A1 A2 :
    ▷ (A1 <:> A2) -∗
    mutex A1 <: mutex A2.
  Proof.
    iIntros "#[Hle1 Hle2]" (v) "!>". iDestruct 1 as (γ l lk ->) "Hinv".
    iExists γ, l, lk. iSplit; first done.
    iApply (spin_lock.is_lock_iff with "Hinv").
    iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle1".
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle2".
  Qed.

  Lemma lty_copyable_mutex A :
    ⊢ lty_copyable (mutex A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_le_mutex_guard A1 A2 :
    ▷ (A1 <:> A2) -∗
    mutex_guard A1 <: mutex_guard A2.
  Proof.
    iIntros "#[Hle1 Hle2]" (v) "!>".
    iDestruct 1 as (γ l lk w ->) "[Hinv [Hlock Hinner]]".
    iExists γ, l, lk, w. iSplit; first done.
    iFrame "Hlock Hinner". iApply (spin_lock.is_lock_iff with "Hinv").
    iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle1".
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle2".
  Qed.
End properties.

Section rules.
  Context `{heapG Σ, lockG Σ}.

  (** Mutex properties *)
  Lemma ltyped_mutex_alloc Γ A :
    ⊢ Γ ⊨ mutex_alloc : A → mutex A ⫤ Γ.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value.
    iFrame "HΓ".
    iIntros "!>" (v) "Hv". rewrite /mutex_alloc. wp_pures.
    wp_alloc l as "Hl".
    wp_bind (newlock _).
    set (N := nroot .@ "makelock").
    iAssert (∃ inner, l ↦ inner ∗ ltty_car A inner)%I with "[Hl Hv]" as "Hlock".
    { iExists v. iFrame "Hl Hv". }
    wp_apply (newlock_spec with "Hlock").
    iIntros (lk γ) "Hlock".
    wp_pures. iExists γ, l, lk. iSplit=> //.
  Qed.

  Lemma ltyped_mutex_acquire Γ (x : string) A :
    Γ !! x = Some (mutex A)%lty →
    ⊢ Γ ⊨ mutex_acquire x : A ⫤ <[x := (mutex_guard A)%lty]> Γ.
  Proof.
    iIntros (Hx vs) "!> HΓ /=".
    iDestruct (env_ltyped_lookup with "HΓ") as (v Hv) "[HA HΓ]"; first done; rewrite Hv.
    rewrite /mutex_acquire. wp_pures.
    iDestruct "HA" as (γ l lk ->) "#Hlock".
    wp_bind (acquire _).
    wp_apply (acquire_spec with "Hlock"). iIntros "[Hlocked Hinner]".
    iDestruct "Hinner" as (v) "[Hl HA]".
    wp_pures. wp_load.
    iFrame "HA".
    iAssert (ltty_car (mutex_guard A)%lty (lk, #l)) with "[Hlocked Hl]" as "Hguard".
    { iExists γ, l, lk, v. iSplit=>//. iFrame "Hlocked Hl Hlock". }
    iDestruct (env_ltyped_insert _ _ x with "Hguard HΓ") as "HΓ".
    rewrite /binder_insert insert_delete (insert_id _ _ _ Hv).
    iFrame "HΓ".
  Qed.

  Lemma ltyped_mutex_release Γ Γ' (x : string) e A :
    Γ' !! x = Some (mutex_guard A)%lty →
    (Γ ⊨ e : A ⫤ Γ') -∗
    Γ ⊨ mutex_release x e : () ⫤ <[x := (mutex A)%lty]> Γ'.
  Proof.
    iIntros (Hx) "#He". iIntros (vs) "!> HΓ /=".
    wp_bind (subst_map vs e).
    iApply (wp_wand with "(He HΓ)"). iIntros (v) "[HA HΓ']".
    iDestruct (env_ltyped_lookup with "HΓ'") as (g Hg) "[Hguard HΓ']"; first done; rewrite Hg.
    iDestruct "Hguard" as (γ l lk inner ->) "(#Hlock & Hlocked & Hinner)".
    rewrite /mutex_release.
    wp_pures. wp_store. wp_pures.
    iAssert (∃ inner, l ↦ inner ∗ ltty_car A inner)%I
      with "[Hinner HA]" as "Hinner".
    { iExists v. iFrame "Hinner HA". }
    wp_apply (release_spec γ _ (∃ inner, l ↦ inner ∗ ltty_car A inner)%I
                with "[Hlocked Hinner]").
    { iFrame "Hlock Hlocked".
      iDestruct "Hinner" as (w) "[Hl HA]". eauto with iFrame. }
    iIntros "_". wp_pures.
    iSplit=> //.
    iAssert (ltty_car (mutex A)%lty (lk, #l)) with "[Hlock]" as "Hmutex".
    { iExists γ, l, lk. iSplit=>//. }
    iDestruct (env_ltyped_insert _ _ x with "Hmutex HΓ'") as "HΓ'".
    rewrite /binder_insert insert_delete (insert_id _ _ _ Hg).
    iFrame "HΓ'".
  Qed.

End rules.
