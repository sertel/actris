(** This file defines all of the semantic subtyping rules for term types and
session types. *)
From iris.bi.lib Require Import core.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From actris.logrel Require Export subtyping term_types session_types.

Section subtyping_rules.
  Context `{heapG Σ, chanG Σ}.
  Implicit Types A : ltty Σ.
  Implicit Types S : lsty Σ.

  (** Generic rules *)
  Lemma lty_le_refl {k} (K : lty Σ k) : ⊢ K <: K.
  Proof. destruct k. by iIntros (v) "!> H". by iModIntro. Qed.
  Lemma lty_le_trans {k} (K1 K2 K3 : lty Σ k) : K1 <: K2 -∗ K2 <: K3 -∗ K1 <: K3.
  Proof.
    destruct k.
    - iIntros "#H1 #H2" (v) "!> H". iApply "H2". by iApply "H1".
    - iIntros "#H1 #H2 !>". by iApply iProto_le_trans.
  Qed.

  Lemma lty_bi_le_refl {k} (K : lty Σ k) : ⊢ K <:> K.
  Proof. iSplit; iApply lty_le_refl. Qed.
  Lemma lty_bi_le_trans {k} (K1 K2 K3 : lty Σ k) :
    K1 <:> K2 -∗ K2 <:> K3 -∗ K1 <:> K3.
  Proof. iIntros "#[H11 H12] #[H21 H22]". iSplit; by iApply lty_le_trans. Qed.
  Lemma lty_bi_le_sym {k} (K1 K2 : lty Σ k) : K1 <:> K2 -∗ K2 <:> K1.
  Proof. iIntros "#[??]"; by iSplit. Qed.

  Lemma lty_le_l {k} (K1 K2 K3 : lty Σ k) : K1 <:> K2 -∗ K2 <: K3 -∗ K1 <: K3.
  Proof. iIntros "#[H1 _] #H2". by iApply lty_le_trans. Qed.
  Lemma lty_le_r {k} (K1 K2 K3 : lty Σ k) : K1 <: K2 -∗ K2 <:> K3 -∗ K1 <: K3.
  Proof. iIntros "#H1 #[H2 _]". by iApply lty_le_trans. Qed.

  Lemma lty_le_rec_unfold {k} (C : lty Σ k → lty Σ k) `{!Contractive C} :
    ⊢ lty_rec C <:> C (lty_rec C).
  Proof.
    iSplit.
    - rewrite {1}/lty_rec fixpoint_unfold. iApply lty_le_refl.
    - rewrite {2}/lty_rec fixpoint_unfold. iApply lty_le_refl.
  Qed.

  Lemma lty_le_rec {k} (C1 C2 : lty Σ k → lty Σ k)
        `{Contractive C1, Contractive C2} :
    (∀ K1 K2, ▷ (K1 <: K2) -∗ C1 K1 <: C2 K2) -∗
    lty_rec C1 <: lty_rec C2.
  Proof.
    iIntros "#Hle". iLöb as "IH".
    iApply lty_le_l; [iApply lty_le_rec_unfold|].
    iApply lty_le_r; [|iApply lty_bi_le_sym; iApply lty_le_rec_unfold].
    by iApply "Hle".
  Qed.

  (** Term subtyping *)
  Lemma lty_le_any A : ⊢ A <: any.
  Proof. by iIntros (v) "!> H". Qed.
  Lemma lty_copyable_any : ⊢@{iPropI Σ} lty_copyable any.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_le_copy A B : A <: B -∗ copy A <: copy B.
  Proof. iIntros "#Hle". iIntros (v) "!> #HA !>". by iApply "Hle". Qed.
  Lemma lty_le_copy_elim A : ⊢ copy A <: A.
  Proof. by iIntros (v) "!> #H". Qed.
  Lemma lty_copyable_copy A : ⊢@{iPropI Σ} lty_copyable (copy A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_le_copy_inv_mono A B : A <: B -∗ copy- A <: copy- B.
  Proof.
    iIntros "#Hle !>" (v) "#HA". iApply (coreP_wand (ltty_car A v) with "[] HA").
    iIntros "{HA} !> !>". iApply "Hle".
  Qed.
  Lemma lty_le_copy_inv_intro A : ⊢ A <: copy- A.
  Proof. iIntros "!>" (v). iApply coreP_intro. Qed.
  Lemma lty_le_copy_inv_elim A : ⊢ copy- (copy A) <: A.
  Proof. iIntros (v) "!> #H". iApply (coreP_elim with "H"). Qed.
  Lemma lty_copyable_copy_inv A : ⊢ lty_copyable (copy- A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.
  Lemma lty_le_copy_inv_elim_copyable A : lty_copyable A -∗ copy- A <: A.
  Proof.
    iIntros "#Hcp".
    iApply lty_le_trans.
    - iApply lty_le_copy_inv_mono. iApply "Hcp".
    - iApply lty_le_copy_inv_elim.
  Qed.

  Lemma lty_copyable_unit : ⊢@{iPropI Σ} lty_copyable ().
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.
  Lemma lty_copyable_bool : ⊢@{iPropI Σ} lty_copyable lty_bool.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.
  Lemma lty_copyable_int : ⊢@{iPropI Σ} lty_copyable lty_int.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

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
  (** This rule is really trivial, since [A → B] is syntactic sugar for
  [copy (A ⊸ B)], but we include it anyway for completeness' sake. *)
  Lemma lty_copyable_arr_copy A B : ⊢@{iPropI Σ} lty_copyable (A → B).
  Proof. iApply lty_copyable_copy. Qed.

  Lemma lty_le_prod A11 A12 A21 A22 :
    ▷ (A11 <: A21) -∗ ▷ (A12 <: A22) -∗
    A11 * A12 <: A21 * A22.
  Proof.
    iIntros "#H1 #H2" (v) "!>". iDestruct 1 as (w1 w2 ->) "[H1' H2']".
    iExists _, _.
    iDestruct ("H1" with "H1'") as "$".
    by iDestruct ("H2" with "H2'") as "$".
  Qed.

  Lemma lty_le_prod_copy A B :
    ⊢ copy A * copy B <:> copy (A * B).
  Proof.
    iSplit; iModIntro; iIntros (v) "#Hv"; iDestruct "Hv" as (v1 v2 ->) "[Hv1 Hv2]".
    - iModIntro. iExists v1, v2. iSplit; [done|]. iSplitL; auto.
    - iExists v1, v2. iSplit; [done|]. auto.
  Qed.

  Lemma lty_copyable_prod A B :
    lty_copyable A -∗ lty_copyable B -∗ lty_copyable (A * B).
  Proof.
    iIntros "#HcpA #HcpB". rewrite /lty_copyable /=.
    iApply lty_le_r; last by iApply lty_le_prod_copy.
    iApply lty_le_prod. iApply "HcpA". iApply "HcpB".
  Qed.

  Lemma lty_le_sum A11 A12 A21 A22 :
    ▷ (A11 <: A21) -∗ ▷ (A12 <: A22) -∗
    A11 + A12 <: A21 + A22.
  Proof.
    iIntros "#H1 #H2" (v) "!> [H | H]"; iDestruct "H" as (w ->) "H".
    - iDestruct ("H1" with "H") as "H1'". iLeft; eauto.
    - iDestruct ("H2" with "H") as "H2'". iRight; eauto.
  Qed.
  Lemma lty_le_sum_copy A B :
    ⊢ copy A + copy B <:> copy (A + B).
  Proof.
    iSplit; iModIntro; iIntros (v);
      iDestruct 1 as "#[Hv|Hv]"; iDestruct "Hv" as (w ?) "Hw";
      try iModIntro; first [iLeft; by auto|iRight; by auto].
  Qed.
  Lemma lty_copyable_sum A B :
    lty_copyable A -∗ lty_copyable B -∗ lty_copyable (A + B).
  Proof.
    iIntros "#HcpA #HcpB". rewrite /lty_copyable /=.
    iApply lty_le_r; last by iApply lty_le_sum_copy.
    iApply lty_le_sum. iApply "HcpA". iApply "HcpB".
  Qed.

  Lemma lty_le_forall C1 C2 :
    ▷ (∀ A, C1 A <: C2 A) -∗
    (∀ A, C1 A) <: (∀ A, C2 A).
  Proof.
    iIntros "#Hle" (v) "!> H". iIntros (w).
    iApply (wp_step_fupd); first done.
    { iIntros "!> !> !>". iExact "Hle". }
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
  Lemma lty_le_exist_copy F :
    ⊢ (∃ A, copy (F A)) <:> copy (∃ A, F A).
  Proof.
    iSplit; iIntros "!>" (v); iDestruct 1 as (A) "#Hv";
      iExists A; repeat iModIntro; iApply "Hv".
  Qed.

  Lemma lty_copyable_exist (C : ltty Σ → ltty Σ) :
    (∀ M, lty_copyable (C M)) -∗ lty_copyable (lty_exist C).
  Proof.
    iIntros "#Hle". rewrite /lty_copyable /tc_opaque.
    iApply lty_le_r; last by iApply lty_le_exist_copy.
    iApply lty_le_exist. iApply "Hle".
  Qed.

  (* TODO(COPY): Commuting rule for recursive types, allowing [copy] to move
  outside the recursive type. This rule should be derivable using Löb
  induction. *)
  Lemma lty_copyable_rec C `{!Contractive C} :
    (∀ A, ▷ lty_copyable A -∗ lty_copyable (C A)) -∗ lty_copyable (lty_rec C).
  Proof.
    iIntros "#Hcopy".
    iLöb as "IH".
    iIntros (v) "!> Hv".
    rewrite /lty_rec {2}fixpoint_unfold.
    iDestruct ("Hcopy" with "IH Hv") as "{Hcopy} #Hcopy".
    iModIntro.
    iEval (rewrite fixpoint_unfold).
    iApply "Hcopy".
  Qed.

  Lemma lty_le_ref_uniq A1 A2 :
    ▷ (A1 <: A2) -∗
    ref_uniq A1 <: ref_uniq A2.
  Proof.
    iIntros "#H1" (v) "!>". iDestruct 1 as (l w ->) "[Hl HA]".
    iDestruct ("H1" with "HA") as "HA".
    iExists l, w. by iFrame.
  Qed.

  Lemma lty_le_shr_ref A1 A2 :
    ▷ (A1 <:> A2) -∗
    ref_shr A1 <: ref_shr A2.
  Proof.
    iIntros "#[Hle1 Hle2]" (v) "!>". iDestruct 1 as (l ->) "Hinv".
    iExists l. iSplit; first done.
    iApply (inv_iff with "Hinv"). iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl #HA]". iExists v. iIntros "{$Hl} !>". by iApply "Hle1".
    - iDestruct 1 as (v) "[Hl #HA]". iExists v. iIntros "{$Hl} !>". by iApply "Hle2".
  Qed.
  Lemma lty_copyable_shr_ref A :
    ⊢ lty_copyable (ref_shr A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_le_chan S1 S2 :
    ▷ (S1 <: S2) -∗ chan S1 <: chan S2.
  Proof.
    iIntros "#Hle" (v) "!> H".
    iApply (iProto_mapsto_le with "H [Hle]"). eauto.
  Qed.

  (** Session subtyping *)
  Lemma lty_le_send A1 A2 S1 S2 :
    ▷ (A2 <: A1) -∗ ▷ (S1 <: S2) -∗
    (<!!> TY A1 ; S1) <: (<!!> TY A2 ; S2).
  Proof.
    iIntros "#HAle #HSle !>" (v) "H". iExists v.
    iDestruct ("HAle" with "H") as "$". by iModIntro.
  Qed.

  Lemma lty_le_recv A1 A2 S1 S2 :
    ▷ (A1 <: A2) -∗ ▷ (S1 <: S2) -∗
    (<??> TY A1 ; S1) <: (<??> TY A2 ; S2).
  Proof.
    iIntros "#HAle #HSle !>" (v) "H". iExists v.
    iDestruct ("HAle" with "H") as "$". by iModIntro.
  Qed.

  Lemma lty_le_exist_elim_l k (M : lty Σ k → lmsg Σ) S :
    (∀ (A : lty Σ k), (<??> M A) <: S) -∗
    (<?? (A : lty Σ k)> M A) <: S.
  Proof.
    iIntros "#Hle !>". iApply (iProto_le_exist_elim_l_inhabited M). auto.
  Qed.

  Lemma lty_le_exist_elim_r k (M : lty Σ k → lmsg Σ) S :
    (∀ (A : lty Σ k), S <: (<!!> M A)) -∗
    S <: (<!! (A : lty Σ k)> M A).
  Proof.
    iIntros "#Hle !>". iApply (iProto_le_exist_elim_r_inhabited _ M). auto.
  Qed.

  Lemma lty_le_exist_intro_l k (M : lty Σ k → lmsg Σ) (A : lty Σ k) :
    ⊢ (<!! X> M X) <: (<!!> M A).
  Proof. iIntros "!>". iApply (iProto_le_exist_intro_l). Qed.

  Lemma lty_le_exist_intro_r k (M : lty Σ k → lmsg Σ) (A : lty Σ k) :
    ⊢ (<??> M A) <: (<?? X> M X).
  Proof. iIntros "!>". iApply (iProto_le_exist_intro_r). Qed.

  Lemma lty_le_texist_elim_l {kt} (M : ltys Σ kt → lmsg Σ) S :
    (∀ Xs, (<??> M Xs) <: S) -∗
    (<??.. Xs> M Xs) <: S.
  Proof.
    iIntros "H". iInduction kt as [|k kt] "IH"; simpl; [done|].
    iApply lty_le_exist_elim_l; iIntros (X).
    iApply "IH". iIntros (Xs). iApply "H".
  Qed.

  Lemma lty_le_texist_elim_r {kt : ktele Σ} (M : ltys Σ kt → lmsg Σ) S :
    (∀ Xs, S <: (<!!> M Xs)) -∗
    S <: (<!!.. Xs> M Xs).
  Proof.
    iIntros "H". iInduction kt as [|k kt] "IH"; simpl; [done|].
    iApply lty_le_exist_elim_r; iIntros (X).
    iApply "IH". iIntros (Xs). iApply "H".
  Qed.

  Lemma lty_le_texist_intro_l {kt : ktele Σ} (M : ltys Σ kt → lmsg Σ) Ks :
    ⊢ (<!!.. Xs> M Xs) <: (<!!> M Ks).
  Proof.
    induction Ks as [|k kT X Xs IH]; simpl; [iApply lty_le_refl|].
    iApply lty_le_trans; [by iApply lty_le_exist_intro_l|]. iApply IH.
  Qed.

  Lemma lty_le_texist_intro_r {kt : ktele Σ} (M : ltys Σ kt → lmsg Σ) Ks :
    ⊢ (<??> M Ks) <: (<??.. Xs> M Xs).
  Proof.
    induction Ks as [|k kt X Xs IH]; simpl; [iApply lty_le_refl|].
    iApply lty_le_trans; [|by iApply lty_le_exist_intro_r]. iApply IH.
  Qed.

  Lemma lty_le_swap_recv_send A1 A2 S :
    ⊢ (<??> TY A1; <!!> TY A2; S) <: (<!!> TY A2; <??> TY A1; S).
  Proof.
    iIntros "!>" (v1 v2).
    iApply iProto_le_trans;
      [iApply iProto_le_base; iApply (iProto_le_exist_intro_l _ v2)|].
    iApply iProto_le_trans;
      [|iApply iProto_le_base; iApply (iProto_le_exist_intro_r _ v1)]; simpl.
    iApply iProto_le_base_swap.
  Qed.

  Lemma lty_le_swap_recv_select A Ss :
    ⊢ (<??> TY A; lty_select Ss) <: lty_select ((λ S, <??> TY A; S) <$> Ss)%lty.
  Proof.
    iIntros "!>" (v1 x2).
    iApply iProto_le_trans;
      [iApply iProto_le_base; iApply (iProto_le_exist_intro_l _ x2)|]; simpl.
    iApply iProto_le_payload_elim_r.
    iMod 1 as %HSs. revert HSs.
    rewrite !lookup_total_alt !lookup_fmap fmap_is_Some; iIntros ([S ->]) "/=".
    iApply iProto_le_trans; [iApply iProto_le_base_swap|]. iSplitL; [by eauto|].
    iModIntro. by iExists v1.
  Qed.

  Lemma lty_le_swap_branch_send A Ss :
    ⊢ lty_branch ((λ S, <!!> TY A; S) <$> Ss)%lty <: (<!!> TY A; lty_branch Ss).
  Proof.
    iIntros "!>" (x1 v2).
    iApply iProto_le_trans;
      [|iApply iProto_le_base; iApply (iProto_le_exist_intro_r _ x1)]; simpl.
    iApply iProto_le_payload_elim_l.
    iMod 1 as %HSs. revert HSs.
    rewrite !lookup_total_alt !lookup_fmap fmap_is_Some; iIntros ([S ->]) "/=".
    iApply iProto_le_trans; [|iApply iProto_le_base_swap]. iSplitL; [by eauto|].
    iModIntro. by iExists v2.
  Qed.

  Lemma lty_le_swap_branch_select (Ss1 Ss2 : (gmap Z (gmap Z (lsty Σ)))) :
    (∀ i j Ss1' Ss2',
        Ss1 !! i = Some Ss1' → Ss2 !! j = Some Ss2' →
        (is_Some (Ss1' !! j) ∧ is_Some (Ss2' !! i) ∧
        Ss1' !! j = Ss2' !! i)) →
    ⊢ lty_branch ((λ Ss, lty_select Ss) <$> Ss1) <:
      lty_select ((λ Ss, lty_branch Ss) <$> Ss2).
  Proof.
    intros Hin.
    iIntros "!>" (v1 v2).
    rewrite !lookup_fmap !fmap_is_Some !lookup_total_alt !lookup_fmap.
    iIntros ">% >%".
    destruct H1 as [Ss1' Heq1]. destruct H2 as [Ss2' Heq2].
    rewrite Heq1 Heq2 /=.
    destruct (Hin v1 v2 Ss1' Ss2' Heq1 Heq2) as (Hin1 & Hin2 & Heq).
    iApply iProto_le_trans.
    { iModIntro. iExists v2. by iApply iProto_le_payload_intro_l. }
    iApply iProto_le_trans; [ iApply iProto_le_base_swap |].
    iModIntro. iExists v1.
    iApply iProto_le_trans; [|by iApply iProto_le_payload_intro_r].
    iModIntro. rewrite !lookup_total_alt. by rewrite Heq.
  Qed.

  Lemma lty_le_select (Ss1 Ss2 : gmap Z (lsty Σ)) :
    ▷ ([∗ map] S1;S2 ∈ Ss1; Ss2, S1 <: S2) -∗
    lty_select Ss1 <: lty_select Ss2.
  Proof.
    iIntros "#H !>" (x); iMod 1 as %[S2 HSs2]. iExists x.
    iDestruct (big_sepM2_forall with "H") as "{H} [>% H]".
    assert (is_Some (Ss1 !! x)) as [S1 HSs1] by naive_solver.
    rewrite HSs1. iSplitR; [by eauto|].
    iIntros "!>". rewrite !lookup_total_alt HSs1 HSs2 /=.
    by iApply ("H" with "[] []").
  Qed.
  Lemma lty_le_select_subseteq (Ss1 Ss2 : gmap Z (lsty Σ)) :
    Ss2 ⊆ Ss1 →
    ⊢ lty_select Ss1 <: lty_select Ss2.
  Proof.
    intros; iIntros "!>" (x); iMod 1 as %[S HSs2]. iExists x.
    assert (Ss1 !! x = Some S) as HSs1 by eauto using lookup_weaken.
    rewrite HSs1. iSplitR; [by eauto|].
    iIntros "!>". by rewrite !lookup_total_alt HSs1 HSs2 /=.
  Qed.

  Lemma lty_le_branch (Ss1 Ss2 : gmap Z (lsty Σ)) :
    ▷ ([∗ map] S1;S2 ∈ Ss1; Ss2, S1 <: S2) -∗
    lty_branch Ss1 <: lty_branch Ss2.
  Proof.
    iIntros "#H !>" (x); iMod 1 as %[S1 HSs1]. iExists x.
    iDestruct (big_sepM2_forall with "H") as "{H} [>% H]".
    assert (is_Some (Ss2 !! x)) as [S2 HSs2] by naive_solver.
    rewrite HSs2. iSplitR; [by eauto|].
    iIntros "!>". rewrite !lookup_total_alt HSs1 HSs2 /=.
    by iApply ("H" with "[] []").
  Qed.
  Lemma lty_le_branch_subseteq (Ss1 Ss2 : gmap Z (lsty Σ)) :
    Ss1 ⊆ Ss2 →
    ⊢ lty_branch Ss1 <: lty_branch Ss2.
  Proof.
    intros; iIntros "!>" (x); iMod 1 as %[S HSs1]. iExists x.
    assert (Ss2 !! x = Some S) as HSs2 by eauto using lookup_weaken.
    rewrite HSs2. iSplitR; [by eauto|].
    iIntros "!>". by rewrite !lookup_total_alt HSs1 HSs2 /=.
  Qed.

  (** Algebraic laws *)
  Lemma lty_le_app S11 S12 S21 S22 :
    (S11 <: S21) -∗ (S12 <: S22) -∗
    (S11 <++> S12) <: (S21 <++> S22).
  Proof. iIntros "#H1 #H2 !>". by iApply iProto_le_app. Qed.

  Lemma lty_le_app_id_l S : ⊢ (END <++> S) <:> S.
  Proof. rewrite /lty_app left_id. iSplit; by iModIntro. Qed.
  Lemma lty_le_app_id_r S : ⊢ (S <++> END) <:> S.
  Proof. rewrite /lty_app right_id. iSplit; by iModIntro. Qed.
  Lemma lty_le_app_assoc S1 S2 S3 :
    ⊢ (S1 <++> S2) <++> S3 <:> S1 <++> (S2 <++> S3).
  Proof. rewrite /lty_app assoc. iSplit; by iModIntro. Qed.

  Lemma lty_le_app_send A S1 S2 :
    ⊢ (<!!> TY A; S1) <++> S2 <:> (<!!> TY A; S1 <++> S2).
  Proof.
    rewrite /lty_app iProto_app_message iMsg_app_exist. setoid_rewrite iMsg_app_base.
    iSplit; by iIntros "!> /=".
  Qed.
  Lemma lty_le_app_recv A S1 S2 :
    ⊢ (<??> TY A; S1) <++> S2 <:> (<??> TY A; S1 <++> S2).
  Proof.
    rewrite /lty_app iProto_app_message iMsg_app_exist. setoid_rewrite iMsg_app_base.
    iSplit; by iIntros "!> /=".
  Qed.

  Lemma lty_le_app_choice a (Ss : gmap Z (lsty Σ)) S2 :
    ⊢ lty_choice a Ss <++> S2 <:> lty_choice a ((.<++> S2) <$> Ss)%lty.
  Proof.
    rewrite /lty_app /lty_choice iProto_app_message iMsg_app_exist;
      setoid_rewrite iMsg_app_base; setoid_rewrite lookup_total_alt;
      setoid_rewrite lookup_fmap; setoid_rewrite fmap_is_Some.
    iSplit; iIntros "!> /="; destruct a;
      iIntros (x); iExists x; iMod 1 as %[S ->]; iSplitR; eauto.
  Qed.
  Lemma lty_le_app_select A Ss S2 :
    ⊢ lty_select Ss <++> S2 <:> lty_select ((.<++> S2) <$> Ss)%lty.
  Proof. apply lty_le_app_choice. Qed.
  Lemma lty_le_app_branch A Ss S2 :
    ⊢ lty_branch Ss <++> S2 <:> lty_branch ((.<++> S2) <$> Ss)%lty.
  Proof. apply lty_le_app_choice. Qed.

  Lemma lty_le_dual S1 S2 : S2 <: S1 -∗ lty_dual S1 <: lty_dual S2.
  Proof. iIntros "#H !>". by iApply iProto_le_dual. Qed.
  Lemma lty_le_dual_l S1 S2 : lty_dual S2 <: S1 -∗ lty_dual S1 <: S2.
  Proof. iIntros "#H !>". by iApply iProto_le_dual_l. Qed.
  Lemma lty_le_dual_r S1 S2 : S2 <: lty_dual S1 -∗ S1 <: lty_dual S2.
  Proof. iIntros "#H !>". by iApply iProto_le_dual_r. Qed.

  Lemma lty_le_dual_end : ⊢ lty_dual (Σ:=Σ) END <:> END.
  Proof. rewrite /lty_dual iProto_dual_end=> /=. apply lty_bi_le_refl. Qed.

  Lemma lty_le_dual_message a A S :
    ⊢ lty_dual (lty_message a (TY A; S)) <:> lty_message (action_dual a) (TY A; (lty_dual S)).
  Proof.
    rewrite /lty_dual iProto_dual_message iMsg_dual_exist.
    setoid_rewrite iMsg_dual_base. iSplit; by iIntros "!> /=".
  Qed.
  Lemma lty_le_dual_send A S : ⊢ lty_dual (<!!> TY A; S) <:> (<??> TY A; lty_dual S).
  Proof. apply lty_le_dual_message. Qed.
  Lemma lty_le_dual_recv A S : ⊢ lty_dual (<??> TY A; S) <:> (<!!> TY A; lty_dual S).
  Proof. apply lty_le_dual_message. Qed.

  Lemma lty_le_dual_choice a (Ss : gmap Z (lsty Σ)) :
    ⊢ lty_dual (lty_choice a Ss) <:> lty_choice (action_dual a) (lty_dual <$> Ss).
  Proof.
    rewrite /lty_dual /lty_choice iProto_dual_message iMsg_dual_exist;
      setoid_rewrite iMsg_dual_base; setoid_rewrite lookup_total_alt;
      setoid_rewrite lookup_fmap; setoid_rewrite fmap_is_Some.
    iSplit; iIntros "!> /="; destruct a;
      iIntros (x); iExists x; iMod 1 as %[S ->]; iSplitR; eauto.
  Qed.

  Lemma lty_le_dual_select (Ss : gmap Z (lsty Σ)) :
    ⊢ lty_dual (lty_select Ss) <:> lty_branch (lty_dual <$> Ss).
  Proof. iApply lty_le_dual_choice. Qed.
  Lemma lty_le_dual_branch (Ss : gmap Z (lsty Σ)) :
    ⊢ lty_dual (lty_branch Ss) <:> lty_select (lty_dual <$> Ss).
  Proof. iApply lty_le_dual_choice. Qed.

  (** The instances below make it possible to use the tactics [iIntros],
  [iExist], [iSplitL]/[iSplitR], [iFrame] and [iModIntro] on [lty_le] goals.
  These instances have higher precedence than the ones in [proto.v] to avoid
  needless unfolding of the subtyping relation. *)
  Global Instance lty_le_from_forall_l k (M : lty Σ k → lmsg Σ) (S : lsty Σ) :
    FromForall ((<?? X> M X) <: S) (λ X, (<??> M X) <: S)%I | 0.
  Proof. apply lty_le_exist_elim_l. Qed.
  Global Instance lty_le_from_forall_r k (S : lsty Σ) (M : lty Σ k → lmsg Σ) :
    FromForall (S <: (<!! X> M X)) (λ X, S <: (<!!> M X))%I | 1.
  Proof. apply lty_le_exist_elim_r. Qed.

  Global Instance lty_le_from_exist_l k (M : lty Σ k → lmsg Σ) S :
    FromExist ((<!! X> M X) <: S) (λ X, (<!!> M X) <: S)%I | 0.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (lty_le_trans with "[] H"). iApply lty_le_exist_intro_l.
  Qed.
  Global Instance lty_le_from_exist_r k (M : lty Σ k → lmsg Σ) S :
    FromExist (S <: <?? X> M X) (λ X, S <: (<??> M X))%I | 1.
  Proof.
    rewrite /FromExist. iDestruct 1 as (x) "H".
    iApply (lty_le_trans with "H"). iApply lty_le_exist_intro_r.
  Qed.

  Global Instance lty_le_from_modal_send A (S1 S2 : lsty Σ) :
    FromModal (modality_instances.modality_laterN 1) (S1 <: S2)
              ((<!!> TY A; S1) <: (<!!> TY A; S2)) (S1 <: S2) | 0.
  Proof.
    rewrite /FromModal. iIntros "H". iApply lty_le_send. iApply lty_le_refl. done.
  Qed.

  Global Instance lty_le_from_modal_recv A (S1 S2 : lsty Σ) :
    FromModal (modality_instances.modality_laterN 1) (S1 <: S2)
              ((<??> TY A; S1) <: (<??> TY A; S2)) (S1 <: S2) | 0.
  Proof.
    rewrite /FromModal. iIntros "H". iApply lty_le_recv. iApply lty_le_refl. done.
  Qed.
End subtyping_rules.

Hint Extern 0 (environments.envs_entails _ (?x <: ?y)) =>
  first [is_evar x; fail 1 | is_evar y; fail 1|iApply lty_le_refl] : core.
