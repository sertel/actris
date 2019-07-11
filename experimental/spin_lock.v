From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import excl auth frac csum.
From iris.base_logic.lib Require Import cancelable_invariants.
From iris.bi.lib Require Import fractional.
Set Default Proof Using "Type".

Definition new_lock : val := λ: <>, ref #false.
Definition try_acquire : val := λ: "l", CAS "l" #false #true.
Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Definition release : val := λ: "l", "l" <- #false.

Class lockG Σ := LockG {
  lock_tokG :> inG Σ (authR (optionUR (exclR fracR)));
  lock_cinvG :> cinvG Σ;
}.
Definition lockΣ : gFunctors := #[GFunctor (authR (optionUR (exclR fracR))); cinvΣ].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ} (N : namespace).

  Definition lock_inv (γ γi : gname) (lk : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, lk ↦ #b ∗
                 if b then (∃ p, own γ (● (Excl' p)) ∗ cinv_own γi (p/2))
                 else own γ (● None) ∗ R)%I.

  Definition is_lock (lk : loc) (R : iProp Σ) : iProp Σ :=
    (∃ γ γi : gname, meta lk N (γ,γi) ∗ cinv N γi (lock_inv γ γi lk R))%I.

  Definition unlocked (lk : loc) (q : Qp) : iProp Σ :=
    (∃ γ γi : gname, meta lk N (γ,γi) ∗ cinv_own γi q)%I.

  Definition locked (lk : loc) (q : Qp) : iProp Σ :=
    (∃ γ γi : gname, meta lk N (γ,γi) ∗ cinv_own γi (q/2) ∗ own γ (◯ (Excl' q)))%I.

  Global Instance unlocked_fractional lk : Fractional (unlocked lk).
  Proof.
    intros q1 q2. iSplit.
    - iDestruct 1 as (γ γi) "[#Hm [Hq Hq']]". iSplitL "Hq"; iExists γ, γi; by iSplit.
    - iIntros "[Hq1 Hq2]". iDestruct "Hq1" as (γ γi) "[#Hm Hq1]".
      iDestruct "Hq2" as (γ' γi') "[#Hm' Hq2]".
      iDestruct (meta_agree with "Hm Hm'") as %[= <- <-].
      iExists γ, γi; iSplit; first done. by iSplitL "Hq1".
  Qed.
  Global Instance unlocked_as_fractional γ :
    AsFractional (unlocked γ p) (unlocked γ) p.
  Proof. split. done. apply _. Qed.

  Global Instance lock_inv_ne γ γi lk : NonExpansive (lock_inv γ γi lk).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne lk : NonExpansive (is_lock lk).
  Proof. solve_proper. Qed.

  Global Instance is_lock_persistent lk R : Persistent (is_lock lk R).
  Proof. apply _. Qed.
  Global Instance locked_timeless lk q : Timeless (locked lk q).
  Proof. apply _. Qed.
  Global Instance unlocked_timeless lk q : Timeless (unlocked lk q).
  Proof. apply _. Qed.

  Lemma lock_cancel E lk R : ↑ N ⊆ E → is_lock lk R -∗ unlocked lk 1 ={E}=∗ ▷ R.
  Proof.
    intros. iDestruct 1 as (γ γi) "#[Hm Hinv]". iDestruct 1 as (γ' γi') "[Hm' Hq]".
    iDestruct (meta_agree with "Hm Hm'") as %[= <- <-]; iClear "Hm'".
    iMod (cinv_open_strong with "[$] [$]") as "(HR & Hq & Hclose)"; first done.
    iDestruct "HR" as ([]) "[Hl HR]".
    - iDestruct "HR" as (p) "[_ Hq']". iDestruct (cinv_own_1_l with "Hq Hq'") as ">[]".
    - iDestruct "HR" as "[_ $]". iApply "Hclose"; auto.
  Qed.

  Lemma new_lock_spec :
    {{{ True }}}
      new_lock #()
    {{{ lk, RET #lk; unlocked lk 1 ∗ (∀ R, R ={⊤}=∗ is_lock lk R) }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_fupd. wp_lam.
    wp_apply (wp_alloc with "[//]"); iIntros (l) "[Hl Hm]".
    iDestruct (meta_token_difference _ (↑N) with "Hm") as "[Hm1 Hm2]"; first done.
    iMod (own_alloc (● None)) as (γ) "Hγ"; first by apply auth_auth_valid.
    iMod (cinv_alloc_strong (λ _, True))
      as (γi _) "[Hγi H]"; first by apply pred_infinite_True.
    iMod (meta_set _ _ (γ,γi) with "Hm1") as "#Hm1"; first done.
    iApply "HΦ"; iSplitL "Hγi"; first by (iExists γ, γi; auto).
    iIntros "!>" (R) "HR".
    iMod ("H" $! (lock_inv γ γi l R) with "[HR Hl Hγ]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iExists γ, γi; auto.
  Qed.

  Lemma try_acquire_spec lk R q :
    {{{ is_lock lk R ∗ unlocked lk q }}}
      try_acquire #lk
    {{{ b, RET #b; if b is true then locked lk q ∗ R else unlocked lk q }}}.
  Proof.
    iIntros (Φ) "[#Hl Hq] HΦ". iDestruct "Hl" as (γ γi) "#[Hm Hinv]".
    iDestruct "Hq" as (γ' γi') "[Hm' Hq]".
    iDestruct (meta_agree with "Hm Hm'") as %[= <- <-]; iClear "Hm'".
    wp_rec. wp_bind (CmpXchg _ _ _).
    iInv N as "[HR Hq]"; iDestruct "HR" as ([]) "[Hl HR]".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Hl HR"; first (iExists true; iFrame).
      wp_pures. iApply ("HΦ" $! false). iExists γ, γi; auto.
    - wp_cmpxchg_suc. iDestruct "HR" as "[Hγ HR]". iDestruct "Hq" as "[Hq Hq']".
      iMod (own_update with "Hγ") as "[Hγ Hγ']".
      { by apply auth_update_alloc, (alloc_option_local_update (Excl q)). }
      iModIntro. iSplitL "Hl Hγ Hq"; first (iNext; iExists true; eauto with iFrame).
      wp_pures. iApply ("HΦ" $! true with "[$HR Hγ' Hq']"). iExists γ, γi; by iFrame.
  Qed.

  Lemma acquire_spec lk R q :
    {{{ is_lock lk R ∗ unlocked lk q }}} acquire #lk {{{ RET #(); locked lk q ∗ R }}}.
  Proof.
    iIntros (Φ) "[#Hlk Hq] HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "[$Hlk $Hq]"); iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "Hq". wp_if. iApply ("IH" with "[$]"); auto.
  Qed.

  Lemma release_spec lk R q :
    {{{ is_lock lk R ∗ locked lk q ∗ R }}} release #lk {{{ RET #(); unlocked lk q }}}.
  Proof.
    iIntros (Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (γ γi) "#[Hm Hinv]".
    iDestruct "Hlocked" as (γ' γi') "(#Hm' & Hq & Hγ')".
    iDestruct (meta_agree with "Hm Hm'") as %[= <- <-].
    wp_lam. iInv N as "[HR' Hq]"; iDestruct "HR'" as ([]) "[Hl HR']".
    - iDestruct "HR'" as (p) ">[Hγ Hq']".
      iDestruct (own_valid_2 with "Hγ Hγ'")
        as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
      iMod (own_update_2 with "Hγ Hγ'") as "Hγ".
      { eapply auth_update_dealloc, delete_option_local_update; apply _. }
      wp_store. iIntros "!>". iSplitL "Hl Hγ HR"; first (iExists false); iFrame.
      iApply "HΦ". iExists γ, γi. iSplit; first done. by iSplitL "Hq".
    - iDestruct "HR'" as "[>Hγ _]".
      by iDestruct (own_valid_2 with "Hγ Hγ'")
        as %[[[] ?%leibniz_equiv] _]%auth_both_valid.
  Qed.
End proof.

Typeclasses Opaque is_lock locked.
