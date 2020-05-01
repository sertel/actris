From actris.logrel Require Export term_types.
From iris.proofmode Require Import tactics.

Definition env_ltyped {Σ} (Γ : gmap string (ltty Σ))
    (vs : gmap string val) : iProp Σ :=
  ([∗ map] i ↦ A ∈ Γ, ∃ v, ⌜vs !! i = Some v⌝ ∗ ltty_car A v)%I.

Definition env_split {Σ} (Γ Γ1 Γ2 : gmap string (ltty Σ)) : iProp Σ :=
  (■ ∀ vs, env_ltyped Γ vs ∗-∗ (env_ltyped Γ1 vs ∗ env_ltyped Γ2 vs))%I.

Definition env_copy {Σ} (Γ Γ' : gmap string (ltty Σ)) : iProp Σ :=
  (■ ∀ vs, env_ltyped Γ vs -∗ □ env_ltyped Γ' vs)%I.

Section env.
  Context {Σ : gFunctors}.
  Implicit Types A : ltty Σ.
  Implicit Types Γ : gmap string (ltty Σ).

  Lemma env_ltyped_empty vs : ⊢@{iPropI Σ} env_ltyped ∅ vs.
  Proof. by iApply big_sepM_empty. Qed.

  Lemma env_ltyped_lookup Γ vs x A :
    Γ !! x = Some A →
    env_ltyped Γ vs -∗
    ∃ v, ⌜ vs !! x = Some v ⌝ ∗ ltty_car A v ∗ env_ltyped (delete x Γ) vs.
  Proof.
    iIntros (HΓx) "HΓ".
    iPoseProof (big_sepM_delete with "HΓ") as "[HA H]"; eauto.
    iDestruct "HA" as (v) "HA"; eauto with iFrame.
  Qed.

  Lemma env_ltyped_insert Γ vs x A v :
    ltty_car A v -∗
    env_ltyped Γ vs -∗
    env_ltyped (binder_insert x A Γ) (binder_insert x v vs).
  Proof.
    destruct x as [|x]=> /=; first by auto.
    iIntros "HA HΓ".
    rewrite /env_ltyped.
    set Γ' := <[x:=A]> Γ.
    assert (Hx: Γ' !! x = Some A).
    { apply lookup_insert. }
    iApply (big_sepM_delete _ _ _ _ Hx).
    iSplitL "HA".
    { iExists v. rewrite lookup_insert. auto. }
    assert (Hsub: delete x Γ' ⊆ Γ).
    { rewrite delete_insert_delete. apply delete_subseteq. }
    iPoseProof (big_sepM_subseteq _ _ _ Hsub with "HΓ") as "HΓ".
    iApply (big_sepM_mono with "HΓ"). simpl.
    iIntros (y B Hy) "HB".
    iDestruct "HB" as (w Hw) "HB".
    iExists w. iFrame. iPureIntro.
    apply lookup_delete_Some in Hy.
    destruct Hy as [Hxy _].
    by rewrite -Hw lookup_insert_ne.
  Qed.

  Lemma env_ltyped_delete Γ vs x v :
    Γ !! x = None ->
    env_ltyped Γ (<[x := v]>vs) -∗
    env_ltyped Γ vs.
  Proof.
    iIntros (HNone) "HΓ".
    rewrite /env_ltyped.
    iApply (big_sepM_impl with "HΓ").
    iIntros "!>" (k A HSome) "H".
    iDestruct "H" as (w Heq) "HA".
    iExists _. iFrame.
    iPureIntro.
    destruct (decide (x = k)).
    - subst. rewrite HNone in HSome. inversion HSome.
    - by rewrite lookup_insert_ne in Heq.
  Qed.

  Lemma env_split_id_l Γ : ⊢ env_split Γ ∅ Γ.
  Proof.
    iIntros "!>" (vs).
    iSplit; [iIntros "$" | iIntros "[_ $]"]; iApply env_ltyped_empty.
  Qed.
  Lemma env_split_id_r Γ : ⊢ env_split Γ Γ ∅.
  Proof.
    iIntros "!>" (vs).
    iSplit; [iIntros "$" | iIntros "[$ _]"]; iApply env_ltyped_empty.
  Qed.

  Lemma env_split_empty : ⊢@{iPropI Σ} env_split ∅ ∅ ∅.
  Proof.
    iIntros "!>" (vs).
    iSplit; [iIntros "HΓ" | iIntros "[HΓ1 HΓ2]"]; auto.
  Qed.

  (* TODO: Get rid of side condition that x does not appear in Γ1 *)
  Lemma env_split_left Γ Γ1 Γ2 x A:
    Γ !! x = None → Γ1 !! x = None →
    env_split Γ Γ1 Γ2 -∗
    env_split (<[x := A]> Γ) (<[x := A]> Γ1) Γ2.
  Proof.
    iIntros (HΓx HΓ2x) "#Hsplit !>". iIntros (vs).
    iSplit.
    - iIntros "HΓ".
      iPoseProof (big_sepM_insert with "HΓ") as "[Hv HΓ]"; first by assumption.
      iDestruct ("Hsplit" with "HΓ") as "[HΓ1 $]".
      iApply (big_sepM_insert_2 with "[Hv]"); simpl; eauto.
    - iIntros "[HΓ1 HΓ2]".
      iPoseProof (big_sepM_insert with "HΓ1") as "[Hv HΓ1]"; first by assumption.
      iApply (big_sepM_insert_2 with "[Hv]")=> //.
      iApply "Hsplit". iFrame "HΓ1 HΓ2".
  Qed.

  Lemma env_split_comm Γ Γ1 Γ2:
    env_split Γ Γ1 Γ2 -∗ env_split Γ Γ2 Γ1.
  Proof.
    iIntros "#Hsplit" (vs) "!>".
    iSplit.
    - iIntros "HΓ". by iDestruct ("Hsplit" with "HΓ") as "[$ $]".
    - iIntros "[HΓ1 HΓ2]". iApply "Hsplit". iFrame.
  Qed.

  (* TODO: Get rid of side condition that x does not appear in Γ2 *)
  Lemma env_split_right Γ Γ1 Γ2 x A:
    Γ !! x = None → Γ2 !! x = None →
    env_split Γ Γ1 Γ2 -∗
    env_split (<[x := A]> Γ) Γ1 (<[x := A]> Γ2).
  Proof.
    iIntros (HΓx HΓ2x) "Hsplit".
    iApply env_split_comm. iApply env_split_left=> //.
    by iApply env_split_comm.
  Qed.

  (* TODO: Get rid of side condition that x does not appear in Γ *)
  Lemma env_split_copyable Γ Γ1 Γ2 (x : string) A:
    Γ !! x = None → Γ1 !! x = None → Γ2 !! x = None →
    lty_copyable A -∗
    env_split Γ Γ1 Γ2 -∗
    env_split (<[x:=A]> Γ) (<[x:=A]> Γ1) (<[x:=A]> Γ2).
  Proof.
    iIntros (HΓx HΓ1x HΓ2x) "#Hcopy #Hsplit". iIntros (vs) "!>".
    iSplit.
    - iIntros "HΓ".
      iPoseProof (big_sepM_insert with "HΓ") as "[Hv HΓ]"; first by assumption.
      iDestruct "Hv" as (v ?) "HAv2".
      iDestruct ("Hcopy" with "HAv2") as "#HAv".
      iDestruct ("Hsplit" with "HΓ") as "[HΓ1 HΓ2]".
      iSplitL "HΓ1"; iApply big_sepM_insert_2; simpl; eauto.
    - iIntros "[HΓ1 HΓ2]".
      iPoseProof (big_sepM_insert with "HΓ1") as "[Hv HΓ1]"; first by assumption.
      iPoseProof (big_sepM_insert with "HΓ2") as "[_ HΓ2]"; first by assumption.
      iApply (big_sepM_insert_2 with "[Hv]")=> //.
      iApply "Hsplit". iFrame "HΓ1 HΓ2".
  Qed.

  Lemma env_copy_empty : ⊢@{iPropI Σ} env_copy ∅ ∅.
  Proof. iIntros (vs) "!> _ !> ". by rewrite /env_ltyped. Qed.

  Lemma env_copy_extend x A Γ Γ' :
    Γ !! x = None →
    env_copy Γ Γ' -∗
    env_copy (<[x:=A]> Γ) Γ'.
  Proof.
    iIntros (HΓ) "#Hcopy". iIntros (vs) "!> Hvs". rewrite /env_ltyped.
    iDestruct (big_sepM_insert with "Hvs") as "[_ Hvs]"; first by assumption.
    iApply ("Hcopy" with "Hvs").
  Qed.

  Lemma env_copy_extend_copyable x A Γ Γ' :
    Γ !! x = None →
    Γ' !! x = None →
    lty_copyable A -∗
    env_copy Γ Γ' -∗
    env_copy (<[x:=A]> Γ) (<[x:=A]> Γ').
  Proof.
    iIntros (HΓx HΓ'x) "#HcopyA #Hcopy". iIntros (vs) "!> Hvs". rewrite /env_ltyped.
    iDestruct (big_sepM_insert with "Hvs") as "[HA Hvs]"; first done.
    iDestruct ("Hcopy" with "Hvs") as "#Hvs'".
    iDestruct "HA" as (v ?) "HA2".
    iDestruct ("HcopyA" with "HA2") as "#HA".
    iIntros "!>". iApply big_sepM_insert; first done. iSplitL; eauto.
  Qed.
End env.
