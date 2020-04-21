From actris.logrel Require Import types.
From actris.channel Require Import channel.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.

Definition lty_le {Σ} (A1 A2 : lty Σ) : iProp Σ :=
  □ ∀ v, A1 v -∗ A2 v.
Arguments lty_le {_} _%lty _%lty.
Infix "<:" := lty_le (at level 70).
Instance: Params (@lty_le) 1 := {}.
Instance lty_le_ne {Σ} : NonExpansive2 (@lty_le Σ).
Proof. solve_proper. Qed.
Instance lty_le_proper {Σ} : Proper ((≡) ==> (≡) ==> (≡)) (@lty_le Σ).
Proof. solve_proper. Qed.

Definition lty_bi_le {Σ} (A1 A2 : lty Σ) : iProp Σ :=
  A1 <: A2 ∧ A2 <: A1.
Arguments lty_bi_le {_} _%lty _%lty.
Infix "<:>" := lty_bi_le (at level 70).
Instance: Params (@lty_bi_le) 1 := {}.
Instance lty_bi_le_ne {Σ} : NonExpansive2 (@lty_bi_le Σ).
Proof. solve_proper. Qed.
Instance lty_bi_le_proper {Σ} : Proper ((≡) ==> (≡) ==> (≡)) (@lty_bi_le Σ).
Proof. solve_proper. Qed.

Definition lsty_le {Σ} (P1 P2 : lsty Σ) : iProp Σ :=
  □ iProto_le P1 P2.
Arguments lsty_le {_} _%lsty _%lsty.
Infix "<s:" := lsty_le (at level 70).
Instance: Params (@lsty_le) 1 := {}.
Instance lsty_le_ne {Σ} : NonExpansive2 (@lsty_le Σ).
Proof. solve_proper. Qed.
Instance lsty_le_proper {Σ} : Proper ((≡) ==> (≡) ==> (≡)) (@lsty_le Σ).
Proof. solve_proper. Qed.

Definition lsty_bi_le {Σ} (S1 S2 : lsty Σ) : iProp Σ :=
  S1 <s: S2 ∧ S2 <s: S1.
Arguments lty_bi_le {_} _%lsty _%lsty.
Infix "<s:>" := lsty_bi_le (at level 70).
Instance: Params (@lsty_bi_le) 1 := {}.
Instance lsty_bi_le_ne {Σ} : NonExpansive2 (@lsty_bi_le Σ).
Proof. solve_proper. Qed.
Instance lsty_bi_le_proper {Σ} : Proper ((≡) ==> (≡) ==> (≡)) (@lsty_bi_le Σ).
Proof. solve_proper. Qed.

Section subtype.
  Context `{heapG Σ, chanG Σ}.
  Implicit Types A : lty Σ.
  Implicit Types S : lsty Σ.

  Lemma lty_le_refl (A : lty Σ) : ⊢ A <: A.
  Proof. by iIntros (v) "!> H". Qed.
  Lemma lty_le_trans A1 A2 A3 : A1 <: A2 -∗ A2 <: A3 -∗ A1 <: A3.
  Proof. iIntros "#H1 #H2" (v) "!> H". iApply "H2". by iApply "H1". Qed.

  Lemma lty_bi_le_refl A : ⊢ A <:> A.
  Proof. iSplit; iApply lty_le_refl. Qed.
  Lemma lty_bi_le_trans A1 A2 A3 : ⊢ A1 <:> A2 -∗ A2 <:> A3 -∗ A1 <:> A3.
  Proof. iIntros "#[H11 H12] #[H21 H22]". iSplit; by iApply lty_le_trans. Qed.

  Lemma lty_le_copy A : ⊢ copy A <: A.
  Proof. by iIntros (v) "!> #H". Qed.

  Lemma lty_le_copyable A `{LTyCopy Σ A} : ⊢ A <: copy A.
  Proof. by iIntros (v) "!> #H". Qed.

  Lemma lty_le_arr A11 A12 A21 A22 :
    ▷ (A21 <: A11) -∗ ▷ (A12 <: A22) -∗
    (A11 ⊸ A12) <: (A21 ⊸ A22).
  Proof.
    iIntros "#H1 #H2" (v) "!> H". iIntros (w) "H'".
    iApply (wp_step_fupd); first done.
    { iIntros "!>!>!>". iExact "H2". }
    iApply (wp_wand with "(H (H1 H'))"). iIntros (v') "H Hle !>".
    by iApply "Hle".
  Qed.

  Lemma lty_le_arr_copy A11 A12 A21 A22 :
    ▷ (A21 <: A11) -∗ ▷ (A12 <: A22) -∗
    (A11 → A12) <: (A21 → A22).
  Proof. iIntros "#H1 #H2" (v) "!> #H !>". by iApply lty_le_arr. Qed.

  Lemma lty_le_prod A11 A12 A21 A22 :
    ▷ (A11 <: A21) -∗ ▷ (A12 <: A22) -∗
    A11 * A12 <: A21 * A22.
  Proof.
    iIntros "#H1 #H2" (v) "!>". iDestruct 1 as (w1 w2 ->) "[H1' H2']".
    iExists _, _.
    iDestruct ("H1" with "H1'") as "$".
    by iDestruct ("H2" with "H2'") as "$".
  Qed.

  Lemma lty_le_sum A11 A12 A21 A22 :
    ▷ (A11 <: A21) -∗ ▷ (A12 <: A22) -∗
    A11 + A12 <: A21 + A22.
  Proof.
    iIntros "#H1 #H2" (v) "!> [H | H]"; iDestruct "H" as (w ->) "H".
    - iDestruct ("H1" with "H") as "H1'". iLeft; eauto.
    - iDestruct ("H2" with "H") as "H2'". iRight; eauto.
  Qed.

  Lemma lty_le_any A : ⊢ A <: lty_any.
  Proof. by iIntros (v) "!> H". Qed.

  Lemma lty_le_forall C1 C2 :
    ▷ (∀ A, C1 A <: C2 A) -∗
    (∀ A, C1 A) <: (∀ A, C2 A).
  Proof.
    iIntros "#Hle" (v) "!> H". iIntros (w).
    iApply (wp_step_fupd); first done.
    { iIntros "!>!>!>". iExact "Hle". }
    iApply (wp_wand with "H"). iIntros (v') "H Hle' !>".
    by iApply "Hle'".
  Qed.

  Lemma lty_le_exist C1 C2 :
    ▷ (∀ A, C1 A <: C2 A) -∗
    (∃ A, C1 A) <: (∃ A, C2 A).
  Proof.
    iIntros "#Hle" (v) "!>". iDestruct 1 as (A) "H". iExists A. by iApply "Hle".
  Qed.

  Lemma lty_le_exist_elim C B :
    ⊢ C B <: ∃ A, C A.
  Proof. iIntros "!>" (v) "Hle". by iExists B. Qed.

  Lemma lty_le_rec_unfold (C : lty Σ → lty Σ) `{!Contractive C} :
    ⊢ lty_rec C <:> C (lty_rec C).
  Proof.
    iSplit.
    - rewrite {1}/lty_rec {1}fixpoint_unfold {1}/lty_rec_aux. iApply lty_le_refl.
    - rewrite {2}/lty_rec {1}fixpoint_unfold {1}/lty_rec_aux. iApply lty_le_refl.
  Qed.

  Lemma lty_le_rec `{Contractive C1, Contractive C2} :
    (□ ∀ A B, ▷ (A <: B) -∗ C1 A <: C2 B) -∗
    lty_rec C1 <: lty_rec C2.
  Proof.
    iIntros "#Hle".
    iLöb as "IH".
    iIntros (v) "!> H".
    rewrite /lty_rec {2}fixpoint_unfold.
    iEval (rewrite fixpoint_unfold).
    rewrite {3}/lty_rec_aux {4}/lty_rec_aux.
    iApply ("Hle" with "[] H").
    iNext. iApply "IH".
  Qed.

  Lemma lty_le_ref_mut A1 A2 :
    ▷ (A1 <: A2) -∗
    ref_mut A1 <: ref_mut A2.
  Proof.
    iIntros "#H1" (v) "!>". iDestruct 1 as (l w ->) "[Hl HA]".
    iDestruct ("H1" with "HA") as "HA".
    iExists l, w. by iFrame.
  Qed.

  Lemma lty_le_weak_ref A1 A2 :
    ▷ (A1 <: A2) -∗ ▷ (A2 <: A1) -∗
    ref_shr A1 <: ref_shr A2.
  Proof.
    iIntros "#Hle1 #Hle2" (v) "!>". iDestruct 1 as (l ->) "Hinv".
    iExists l. iSplit; first done.
    iApply (inv_iff with "Hinv"). iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle1".
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle2".
  Qed.

  Lemma lty_le_mutex A1 A2 :
    ▷ (A1 <: A2) -∗ ▷ (A2 <: A1) -∗
    mutex A1 <: mutex A2.
  Proof.
    iIntros "#Hle1 #Hle2" (v) "!>". iDestruct 1 as (γ l lk ->) "Hinv".
    iExists γ, l, lk. iSplit; first done.
    iApply (spin_lock.is_lock_iff with "Hinv").
    iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle1".
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle2".
  Qed.

  Lemma lty_le_mutexguard A1 A2 :
    ▷ (A1 <: A2) -∗ ▷ (A2 <: A1) -∗
    mutexguard A1 <: mutexguard A2.
  Proof.
    iIntros "#Hle1 #Hle2" (v) "!>".
    iDestruct 1 as (γ l lk w ->) "[Hinv [Hlock Hinner]]".
    iExists γ, l, lk, w. iSplit; first done.
    iFrame "Hlock Hinner". iApply (spin_lock.is_lock_iff with "Hinv").
    iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle1".
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle2".
  Qed.

  Lemma lsty_le_refl (S : lsty Σ) : ⊢ S <s: S.
  Proof. iApply iProto_le_refl. Qed.
  Lemma lsty_le_trans S1 S2 S3 : S1 <s: S2 -∗ S2 <s: S3 -∗ S1 <s: S3.
  Proof. iIntros "#H1 #H2 !>". by iApply iProto_le_trans. Qed.

  Lemma lsty_bi_le_refl S : ⊢ S <s:> S.
  Proof. iSplit; iApply lsty_le_refl. Qed.
  Lemma lsty_bi_le_trans S1 S2 S3 : ⊢ S1 <s:> S2 -∗ S2 <s:> S3 -∗ S1 <s:> S3.
  Proof. iIntros "#[H11 H12] #[H21 H22]". iSplit; by iApply lsty_le_trans. Qed.

  Lemma lsty_le_send A1 A2 S1 S2 :
    ▷ (A2 <: A1) -∗ ▷ (S1 <s: S2) -∗
    (<!!> A1 ; S1) <s: (<!!> A2 ; S2).
  Proof.
    iIntros "#HAle #HPle !>". iApply iProto_le_send; iIntros "!> /=" (x) "H".
    iDestruct ("HAle" with "H") as "H".
    eauto with iFrame.
  Qed.

  Lemma lsty_le_recv A1 A2 S1 S2 :
    ▷ (A1 <: A2) -∗ ▷ (S1 <s: S2) -∗
    (<??> A1 ; S1) <s: (<??> A2 ; S2).
  Proof.
    iIntros "#HAle #HSle !>". iApply iProto_le_recv; iIntros "!> /=" (x) "H".
    iDestruct ("HAle" with "H") as "H".
    eauto with iFrame.
  Qed.

  Lemma lsty_le_swap (A1 A2 : lty Σ) (P : lsty Σ) :
    ⊢ (<??> A1 ; <!!> A2 ; P) <s: (<!!> A2 ; <??> A1 ; P).
  Proof.
    iIntros "!>". iApply iProto_le_swap. iIntros "!>" (x1 x2) "/= HS1 HS2".
    iExists _, _,
      (tele_app (TT:=[tele _]) (λ x2, (x2, A2 x2, (P:iProto Σ)))),
      (tele_app (TT:=[tele _]) (λ x1, (x1, A1 x1, (P:iProto Σ)))),
      x2, x1; simpl.
    do 2 (iSplit; [done|]).
    iFrame "HS1 HS2".
    do 2 (iSplitR; [iApply iProto_le_refl|]). by iFrame.
  Qed.

  Lemma lsty_le_select (Ps1 Ps2 : gmap Z (lsty Σ)) :
    (▷ [∗ map] i ↦ S1;S2 ∈ Ps1; Ps2, S1 <s: S2) -∗
    lsty_select Ps1 <s: lsty_select Ps2.
  Proof.
    iIntros "#H1 !>". iApply iProto_le_send; iIntros "!>" (x Hsome).
    iExists x. iSplit; first done. iSplit.
    - iDestruct (big_sepM2_forall with "H1") as "[% _]".
      iPureIntro. naive_solver.
    - iDestruct (big_sepM2_forall with "H1") as "[% H]".
      iApply ("H" with "[] []").
      + iPureIntro. apply lookup_lookup_total; naive_solver.
      + iPureIntro. by apply lookup_lookup_total.
  Qed.

  Lemma lsty_le_select_subseteq (Ps1 Ps2 : gmap Z (lsty Σ)) :
    Ps2 ⊆ Ps1 →
    ⊢ lsty_select Ps1 <s: lsty_select Ps2.
  Proof.
    iIntros (Hsub) "!>". iApply iProto_le_send; iIntros "!>" (x Hsome).
    iExists _. iSplit; first done. iSplit.
    { iPureIntro. by eapply lookup_weaken_is_Some. }
    destruct Hsome as [P H1].
    assert (Ps1 !! x = Some P) by eauto using lookup_weaken.
    rewrite (lookup_total_correct Ps1 x P) //.
    rewrite (lookup_total_correct Ps2 x P) //.
    iApply iProto_le_refl.
  Qed.

  Lemma lsty_le_branch (Ps1 Ps2 : gmap Z (lsty Σ)) :
    (▷ [∗ map] i ↦ S1;S2 ∈ Ps1; Ps2, S1 <s: S2) -∗
    lsty_branch Ps1 <s: lsty_branch Ps2.
  Proof.
    iIntros "#H1 !>". iApply iProto_le_recv; iIntros "!>" (x Hsome).
    iExists x. iSplit; first done. iSplit.
    - iDestruct (big_sepM2_forall with "H1") as "[% _]".
      iPureIntro. by naive_solver.
    - iDestruct (big_sepM2_forall with "H1") as "[% H]".
      iApply ("H" with "[] []").
      + iPureIntro. by apply lookup_lookup_total.
      + iPureIntro. by apply lookup_lookup_total; naive_solver.
  Qed.

  Lemma lsty_le_branch_subseteq (Ps1 Ps2 : gmap Z (lsty Σ)) :
    Ps1 ⊆ Ps2 →
    ⊢ lsty_branch Ps1 <s: lsty_branch Ps2.
  Proof.
    iIntros (Hsub) "!>". iApply iProto_le_recv; iIntros "!>" (x Hsome).
    iExists _. iSplit; first done. iSplit.
    { iPureIntro. by eapply lookup_weaken_is_Some. }
    destruct Hsome as [P ?].
    assert (Ps2 !! x = Some P) by eauto using lookup_weaken.
    rewrite (lookup_total_correct Ps1 x P) //.
    rewrite (lookup_total_correct Ps2 x P) //.
    iApply iProto_le_refl.
  Qed.

  Lemma lsty_le_app S11 S12 S21 S22 :
    (S11 <s: S21) -∗ (S12 <s: S22) -∗
    (S11 <++> S12) <s: (S21 <++> S22).
  Proof. iIntros "#H1 #H2 !>". by iApply iProto_le_app. Qed.

  Lemma lsty_le_app_assoc S1 S2 S3 :
    ⊢ (S1 <++> S2) <++> S3 <s:> S1 <++> (S2 <++> S3).
  Proof. rewrite assoc. iApply lsty_bi_le_refl. Qed.

  Lemma lsty_le_app_id_l S : ⊢ (END <++> S) <s:> S.
  Proof. rewrite left_id. iApply lsty_bi_le_refl. Qed.
  Lemma lsty_le_app_id_r S : ⊢ (S <++> END) <s:> S.
  Proof. rewrite right_id. iApply lsty_bi_le_refl. Qed.

  Lemma lsty_le_dual S1 S2 : S2 <s: S1 -∗ lsty_dual S1 <s: lsty_dual S2.
  Proof. iIntros "#H !>". by iApply iProto_le_dual. Qed.
  Lemma lsty_le_dual_l S1 S2 : lsty_dual S2 <s: S1 -∗ lsty_dual S1 <s: S2.
  Proof. iIntros "#H !>". by iApply iProto_le_dual_l. Qed.
  Lemma lsty_le_dual_r S1 S2 : S2 <s: lsty_dual S1 -∗ S1 <s: lsty_dual S2.
  Proof. iIntros "#H !>". by iApply iProto_le_dual_r. Qed.

  Lemma lsty_le_dual_message a A S :
    ⊢ lsty_dual (lsty_message a A S) <s:>
      lsty_message (action_dual a) A (lsty_dual S).
  Proof.
    iSplit; iIntros "!>"; rewrite /lsty_dual iProto_dual_message_tele;
      iApply iProto_le_refl.
  Qed.
  Lemma lsty_le_dual_send A S : ⊢ lsty_dual (<!!> A; S) <s:> (<??> A; lsty_dual S).
  Proof. apply lsty_le_dual_message. Qed.
  Lemma lsty_le_dual_recv A S : ⊢ lsty_dual (<??> A; S) <s:> (<!!> A; lsty_dual S).
  Proof. apply lsty_le_dual_message. Qed.

  Lemma lsty_le_dual_choice a (Ss : gmap Z (lsty Σ)) :
    ⊢ lsty_dual (lsty_choice a Ss) <s:> lsty_choice (action_dual a) (lsty_dual <$> Ss).
  Proof.
    iSplit.
    - iIntros "!>".
      rewrite /lsty_dual iProto_dual_message_tele /lsty_choice /=.
      destruct a.
      + iApply iProto_le_recv.
        iIntros "!>" (x) "%".
        iExists _.
        iSplit; first done. iSplit.
        * by rewrite lookup_fmap fmap_is_Some.
        * destruct a as [S HSs]=> /=.
          rewrite lookup_total_alt lookup_total_alt lookup_fmap HSs.
          iApply iProto_le_refl.
      + iApply iProto_le_send.
        iIntros "!>" (x) "%".
        iExists _.
        iSplit; first done. iSplit.
        * rewrite lookup_fmap in a. rewrite ->fmap_is_Some in a. done.
        * destruct a as [S HSs]=> /=.
          rewrite lookup_total_alt lookup_total_alt HSs /=.
          rewrite lookup_fmap in HSs.
          apply fmap_Some_1 in HSs as [S' [-> ->]].
          iApply iProto_le_refl.
        - iIntros "!>".
          rewrite /lsty_dual iProto_dual_message_tele /lsty_choice /=.
          destruct a.
          + iApply iProto_le_recv.
            iIntros "!>" (x) "%". iExists _.
            iSplit; first done. iSplit.
            * rewrite lookup_fmap in a. rewrite ->fmap_is_Some in a. done.
            * destruct a as [S HSs]=> /=.
              rewrite lookup_total_alt lookup_total_alt HSs /=.
              rewrite lookup_fmap in HSs.
              apply fmap_Some_1 in HSs as [S' [-> ->]].
              iApply iProto_le_refl.
          + iApply iProto_le_send.
            iIntros "!>" (x) "%". iExists _.
            iSplit; first done. iSplit.
            * by rewrite lookup_fmap fmap_is_Some.
            * destruct a as [S HSs]=> /=.
              rewrite lookup_total_alt lookup_total_alt lookup_fmap HSs.
              iApply iProto_le_refl.
  Qed.

  Lemma lsty_le_dual_select (Ss : gmap Z (lsty Σ)) :
    ⊢ lsty_dual (lsty_select Ss) <s:> lsty_branch (lsty_dual <$> Ss).
  Proof. iApply lsty_le_dual_choice. Qed.

  Lemma lsty_le_dual_branch (Ss : gmap Z (lsty Σ)) :
    ⊢ lsty_dual (lsty_branch Ss) <s:> lsty_select (lsty_dual <$> Ss).
  Proof. iApply lsty_le_dual_choice. Qed.

  Lemma lsty_le_dual_end : ⊢ lsty_dual (Σ:=Σ) END <s:> END.
  Proof. rewrite /lsty_dual iProto_dual_end=> /=. apply lsty_bi_le_refl. Qed.

  Lemma lsty_le_rec_unfold (C : lsty Σ → lsty Σ) `{!Contractive C} :
    ⊢ lsty_rec C <s:> C (lsty_rec C).
  Proof.
    iSplit.
    - rewrite {1}/lsty_rec {1}fixpoint_unfold {1}/lsty_rec1. iApply lsty_le_refl.
    - rewrite {2}/lsty_rec {1}fixpoint_unfold {1}/lsty_rec1. iApply lsty_le_refl.
  Qed.

  Lemma lsty_le_rec `{Contractive C1, Contractive C2} :
    (□ ∀ S S', ▷ (S <s: S') -∗ C1 S <s: C2 S') -∗
    lsty_rec C1 <s: lsty_rec C2.
  Proof.
    iIntros "#Hle !>".
    iLöb as "IH".
    rewrite /lsty_rec.
    iEval (rewrite fixpoint_unfold).
    iEval (rewrite (fixpoint_unfold (lsty_rec1 C2))).
    rewrite {1 3}/lsty_rec1.
    iApply ("Hle" with "[]").
    iNext. iApply "IH".
  Qed.

  Lemma lty_le_chan S1 S2 :
    ▷ (S1 <s: S2) -∗ chan S1 <: chan S2.
  Proof.
    iIntros "#Hle" (v) "!> H".
    iApply (iProto_mapsto_le with "H [Hle]"). eauto.
  Qed.

  Theorem ltyped_subsumption Γ e τ1 τ2 :
    τ1 <: τ2 -∗ (Γ ⊨ e : τ1) -∗ (Γ ⊨ e : τ2).
  Proof.
    iIntros "#Hle #Hltyped" (vs) "!> Henv".
    iDestruct ("Hltyped" with "Henv") as "Hltyped'".
    iApply (wp_wand with "Hltyped' [Hle]").
    by iIntros (v).
  Qed.

End subtype.
