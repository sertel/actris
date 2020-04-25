From iris.bi.lib Require Import core.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From actris.logrel Require Export subtyping term_types session_types.

Section subtyping_rules.
  Context `{heapG Σ, chanG Σ}.
  Implicit Types A : ltty Σ.
  Implicit Types S : lsty Σ.

  (** Generic rules *)
  Lemma lty_le_refl {k} (M : lty Σ k) : ⊢ M <: M.
  Proof.
    destruct k.
    - by iIntros (v) "!> H".
    - iModIntro. iApply iProto_le_refl.
  Qed.
  Lemma lty_le_trans {k} (M1 M2 M3 : lty Σ k) : M1 <: M2 -∗ M2 <: M3 -∗ M1 <: M3.
  Proof.
    destruct k.
    - iIntros "#H1 #H2" (v) "!> H". iApply "H2". by iApply "H1".
    - iIntros "#H1 #H2 !>". by iApply iProto_le_trans.
  Qed.

  Lemma lty_bi_le_refl {k} (M : lty Σ k) : ⊢ M <:> M.
  Proof. iSplit; iApply lty_le_refl. Qed.
  Lemma lty_bi_le_trans {k} (M1 M2 M3 : lty Σ k) : M1 <:> M2 -∗ M2 <:> M3 -∗ M1 <:> M3.
  Proof. iIntros "#[H11 H12] #[H21 H22]". iSplit; by iApply lty_le_trans. Qed.
  Lemma lty_bi_le_sym {k} (M1 M2 : lty Σ k) : M1 <:> M2 -∗ M2 <:> M1.
  Proof. iIntros "#[??]"; by iSplit. Qed.

  Lemma lty_le_l {k} (M1 M2 M3 : lty Σ k) : M1 <:> M2 -∗ M2 <: M3 -∗ M1 <: M3.
  Proof. iIntros "#[H1 _] #H2". by iApply lty_le_trans. Qed.
  Lemma lty_le_r {k} (M1 M2 M3 : lty Σ k) : M1 <: M2 -∗ M2 <:> M3 -∗ M1 <: M3.
  Proof. iIntros "#H1 #[H2 _]". by iApply lty_le_trans. Qed.

  Lemma lty_le_rec_unfold {k} (C : lty Σ k → lty Σ k) `{!Contractive C} :
    ⊢ lty_rec C <:> C (lty_rec C).
  Proof.
    iSplit.
    - rewrite {1}/lty_rec fixpoint_unfold. iApply lty_le_refl.
    - rewrite {2}/lty_rec fixpoint_unfold. iApply lty_le_refl.
  Qed.

  Lemma lty_le_rec {k} (C1 C2 : lty Σ k → lty Σ k) `{Contractive C1, Contractive C2} :
    (∀ M1 M2, ▷ (M1 <: M2) -∗ C1 M1 <: C2 M2) -∗
    lty_rec C1 <: lty_rec C2.
  Proof.
    iIntros "#Hle". iLöb as "IH".
    iApply lty_le_l; [iApply lty_le_rec_unfold|].
    iApply lty_le_r; [|iApply lty_bi_le_sym; iApply lty_le_rec_unfold].
    by iApply "Hle".
  Qed.

  (** Term subtyping *)
  Lemma lty_le_bot A : ⊢ ⊥ <: A.
  Proof. by iIntros (v) "!> H". Qed.
  Lemma lty_copyable_bot : ⊢@{iPropI Σ} lty_copyable ⊥.
  Proof. iApply lty_le_bot. Qed.
  Lemma lty_le_top A : ⊢ A <: ⊤.
  Proof. by iIntros (v) "!> H". Qed.
  Lemma lty_copyable_top : ⊢@{iPropI Σ} lty_copyable ⊤.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_le_copy A B : A <: B -∗ copy A <: copy B.
  Proof. iIntros "#Hle". iIntros (v) "!> #HA !>". by iApply "Hle". Qed.
  Lemma lty_le_copy_elim A : ⊢ copy A <: A.
  Proof. by iIntros (v) "!> #H". Qed.
  Lemma lty_copyable_copy A : ⊢@{iPropI Σ} lty_copyable (copy A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_le_copy_inv A B : A <: B -∗ copy- A <: copy- B.
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

  Lemma lty_le_prod A11 A12 A21 A22 :
    ▷ (A11 <: A21) -∗ ▷ (A12 <: A22) -∗
    A11 * A12 <: A21 * A22.
  Proof.
    iIntros "#H1 #H2" (v) "!>". iDestruct 1 as (w1 w2 ->) "[H1' H2']".
    iExists _, _.
    iDestruct ("H1" with "H1'") as "$".
    by iDestruct ("H2" with "H2'") as "$".
  Qed.
  (* TODO(COPY): Show derived rules about copyability of products, sums, etc. *)
  Lemma lty_le_prod_copy A B :
    ⊢ copy A * copy B <:> copy (A * B).
  Proof.
    iSplit; iModIntro; iIntros (v) "#Hv"; iDestruct "Hv" as (v1 v2 ->) "[Hv1 Hv2]".
    - iModIntro. iExists v1, v2. iSplit; [done|]. iSplitL; auto.
    - iExists v1, v2. iSplit; [done|]. auto.
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

  Lemma lty_le_forall {k} (Mlow1 Mup1 Mlow2 Mup2 : lty Σ k) C1 C2 :
    Mlow1 <: Mlow2 -∗ Mup2 <: Mup1 -∗
    ▷ (∀ M, Mlow2 <: M -∗ M <: Mup2 -∗ C1 M <: C2 M) -∗
    lty_forall Mlow1 Mup1 C1 <: lty_forall Mlow2 Mup2 C2.
  Proof.
    iIntros "#Hlow #Hup #Hle" (v) "!> H". iIntros (M) "#Hlow' #Hup'".
    iApply wp_step_fupd; first done.
    { iIntros "!> !> !>". iExact "Hle". }
    iApply (wp_wand with "(H [] [])").
    { iApply (lty_le_trans with "Hlow Hlow'"). }
    { iApply (lty_le_trans with "Hup' Hup"). }
    iIntros (v') "H Hle' !>". by iApply "Hle'".
  Qed.
  (* TODO(COPY) TODO(VALUERES): Do the forall type former, once we have the value restriction *)

  Lemma lty_le_exist {k} (Mlow1 Mup1 Mlow2 Mup2 : lty Σ k) C1 C2 :
    Mlow2 <: Mlow1 -∗ Mup1 <: Mup2 -∗
    ▷ (∀ M, Mlow1 <: M -∗ M <: Mup1 -∗ C1 M <: C2 M) -∗
    lty_exist Mlow1 Mup1 C1 <: lty_exist Mlow2 Mup2 C2.
  Proof.
    iIntros "#Hlow #Hup #Hle" (v) "!>". iDestruct 1 as (M) "(#Hlow' & #Hup' & H)".
    iExists M. iSplit; [|iSplit].
    { iApply (lty_le_trans with "Hlow Hlow'"). }
    { iApply (lty_le_trans with "Hup' Hup"). }
    by iApply "Hle".
  Qed.
  Lemma lty_le_exist_intro {k} (Mlow Mup : lty Σ k) C M :
    Mlow <: M -∗ M <: Mup -∗
    C M <: lty_exist Mlow Mup C.
  Proof. iIntros "#Hlow #Hup !>" (v) "Hle". iExists M. auto. Qed.
  Lemma lty_le_exist_copy {k} (Mlow Mup : lty Σ k) C :
    ⊢ lty_exist Mlow Mup (λ M, copy (C M))%lty <:> copy (lty_exist Mlow Mup C).
  Proof.
    iSplit; iIntros "!>" (v);
      iDestruct 1 as (A) "#(Hlow & Hup & Hv)"; iExists A; auto.
  Qed.

  (* TODO(COPY): Commuting rule for μ, allowing `copy` to move outside the μ *)
  Lemma lty_rec_copy C `{!Contractive C} :
    (∀ A, ▷ lty_copyable A -∗ lty_copyable (C A)) -∗ lty_copyable (lty_rec C).
  Proof.
    iIntros "#Hcopy".
    iLöb as "IH".
    iIntros (v) "!> Hv".
    rewrite /lty_rec.
    rewrite {2}fixpoint_unfold.
    iSpecialize ("Hcopy" with "IH").
    iSpecialize ("Hcopy" with "Hv").
    iDestruct "Hcopy" as "#Hcopy".
    iModIntro.
    iEval (rewrite fixpoint_unfold).
    iApply "Hcopy".
  Qed.

  Lemma lty_le_ref_mut A1 A2 :
    ▷ (A1 <: A2) -∗
    ref_mut A1 <: ref_mut A2.
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
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle1".
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle2".
  Qed.
  Lemma lty_copyable_shr_ref A :
    ⊢ lty_copyable (ref_shr A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

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

  Lemma lty_le_mutexguard A1 A2 :
    ▷ (A1 <:> A2) -∗
    mutexguard A1 <: mutexguard A2.
  Proof.
    iIntros "#[Hle1 Hle2]" (v) "!>".
    iDestruct 1 as (γ l lk w ->) "[Hinv [Hlock Hinner]]".
    iExists γ, l, lk, w. iSplit; first done.
    iFrame "Hlock Hinner". iApply (spin_lock.is_lock_iff with "Hinv").
    iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle1".
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle2".
  Qed.

  Lemma lty_le_chan S1 S2 :
    ▷ (S1 <: S2) -∗ chan S1 <: chan S2.
  Proof.
    iIntros "#Hle" (v) "!> H".
    iApply (iProto_mapsto_le with "H [Hle]"). eauto.
  Qed.

  (** Session subtyping *)
  Lemma lty_le_send A1 A2 S1 S2 :
    ▷ (A2 <: A1) -∗ ▷ (S1 <: S2) -∗
    (<!!> A1 ; S1) <: (<!!> A2 ; S2).
  Proof.
    iIntros "#HAle #HSle !>". iApply iProto_le_send; iIntros "!> /=" (x) "H".
    iDestruct ("HAle" with "H") as "H".
    eauto with iFrame.
  Qed.

  Lemma lty_le_recv A1 A2 S1 S2 :
    ▷ (A1 <: A2) -∗ ▷ (S1 <: S2) -∗
    (<??> A1 ; S1) <: (<??> A2 ; S2).
  Proof.
    iIntros "#HAle #HSle !>". iApply iProto_le_recv; iIntros "!> /=" (x) "H".
    iDestruct ("HAle" with "H") as "H".
    eauto with iFrame.
  Qed.

  Lemma lty_le_swap_recv_send A1 A2 S :
    ⊢ (<??> A1; <!!> A2; S) <: (<!!> A2; <??> A1; S).
  Proof.
    iIntros "!>". iApply iProto_le_swap. iIntros "!>" (v1 v2) "/= HS1 HS2".
    iExists _, _,
      (tele_app (TT:=[tele _]) (λ v2, (v2, ltty_car A2 v2, lsty_car S))),
      (tele_app (TT:=[tele _]) (λ v1, (v1, ltty_car A1 v1, lsty_car S))),
      v2, v1; simpl.
    do 2 (iSplit; [done|]).
    iFrame "HS1 HS2".
    do 2 (iSplitR; [iApply iProto_le_refl|]). by iFrame.
  Qed.

  Lemma lty_le_swap_recv_select A Ss :
    ⊢ (<??> A; lty_select Ss) <: (lty_select ((λ S, <??> A ; S)%lty <$> Ss)).
  Proof.
    iIntros "!>". iApply iProto_le_swap. iIntros "!>" (v1 v2) "/=".
    iIntros "HS1" (HS2).
    iExists _, _,
      (tele_app (TT:=[tele _]) (λ (v2 : Z),(#v2, ⌜is_Some (((λ S : lsty Σ, (<??> A; S)%lty) <$> Ss) !! v2)⌝%I, lsty_car (Ss !!! v2)))),
      (tele_app (TT:=[tele _]) (λ v1, (v1, ltty_car A v1, lsty_car (Ss !!! v2)))),
      v2, v1; simpl.
    do 2 (iSplit; [done|]).
    iFrame "HS1".
    iSplitL.
    - iApply iProto_le_send=> /=.
      iIntros "!>" (x HSsx). iExists _.
      rewrite lookup_fmap in HSsx.
      apply fmap_is_Some in HSsx.
      do 2 (iSplit; first done).
      iApply iProto_le_refl.
    - iSplit; last done.
      destruct HS2 as [x HS2].
      rewrite !lookup_total_alt !lookup_fmap /=.
      rewrite lookup_fmap in HS2.
      destruct (Ss !! v2); inversion HS2.
      iApply iProto_le_recv=> /=.
      iIntros "!>" (y) "H". iExists _.
      iFrame. iSplit; first done.
      iApply iProto_le_refl.
  Qed.

  Lemma lty_le_swap_branch_send A Ss :
    ⊢ lty_branch ((λ S, <!!> A ; S)%lty <$> Ss) <: (<!!> A ; lty_branch Ss).
  Proof.
    iIntros "!>". iApply iProto_le_swap. iIntros "!>" (v1 v2) "/=".
    iIntros (HS1) "HS2".
    iExists _, _,
      (tele_app (TT:=[tele _]) (λ v2, (v2, ltty_car A v2, lsty_car (Ss !!! v1)))),
      (tele_app (TT:=[tele _]) (λ (v1 : Z),(#v1, ⌜is_Some (((λ S : lsty Σ, (<!!> A; S)%lty) <$> Ss) !! v1)⌝%I, lsty_car (Ss !!! v1)))),
      v2, v1; simpl.
    do 2 (iSplit; [done|]).
    iFrame "HS2".
    iSplitL.
    - destruct HS1 as [x HS1].
      rewrite !lookup_total_alt !lookup_fmap /=.
      rewrite lookup_fmap in HS1.
      destruct (Ss !! v1); inversion HS1.
      iApply iProto_le_send=> /=.
      iIntros "!>" (y) "H". iExists _.
      iFrame. iSplit; first done.
      iApply iProto_le_refl.
    - iSplit; last done.
      iApply iProto_le_recv=> /=.
      iIntros "!>" (y HSsy). iExists _.
      rewrite lookup_fmap in HSsy.
      apply fmap_is_Some in HSsy.
      do 2 (iSplit; first done).
      iApply iProto_le_refl.
  Qed.

  Lemma lty_le_select (Ss1 Ss2 : gmap Z (lsty Σ)) :
    ▷ ([∗ map] S1;S2 ∈ Ss1; Ss2, S1 <: S2) -∗
    lty_select Ss1 <: lty_select Ss2.
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
  Lemma lty_le_select_subseteq (Ss1 Ss2 : gmap Z (lsty Σ)) :
    Ss2 ⊆ Ss1 →
    ⊢ lty_select Ss1 <: lty_select Ss2.
  Proof.
    iIntros (Hle) "!>". iApply iProto_le_send; iIntros "!>" (x Hsome).
    iExists _. iSplit; first done. iSplit.
    { iPureIntro. by eapply lookup_weaken_is_Some. }
    destruct Hsome as [P H1].
    assert (Ss1 !! x = Some P) by eauto using lookup_weaken.
    rewrite (lookup_total_correct Ss1 x P) //.
    rewrite (lookup_total_correct Ss2 x P) //.
    iApply iProto_le_refl.
  Qed.

  Lemma lty_le_branch (Ss1 Ss2 : gmap Z (lsty Σ)) :
    ▷ ([∗ map] S1;S2 ∈ Ss1; Ss2, S1 <: S2) -∗
    lty_branch Ss1 <: lty_branch Ss2.
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
  Lemma lty_le_branch_subseteq (Ss1 Ss2 : gmap Z (lsty Σ)) :
    Ss1 ⊆ Ss2 →
    ⊢ lty_branch Ss1 <: lty_branch Ss2.
  Proof.
    iIntros (Hle) "!>". iApply iProto_le_recv; iIntros "!>" (x Hsome).
    iExists _. iSplit; first done. iSplit.
    { iPureIntro. by eapply lookup_weaken_is_Some. }
    destruct Hsome as [P ?].
    assert (Ss2 !! x = Some P) by eauto using lookup_weaken.
    rewrite (lookup_total_correct Ss1 x P) //.
    rewrite (lookup_total_correct Ss2 x P) //.
    iApply iProto_le_refl.
  Qed.

  (** Algebraic laws *)
  Lemma lty_le_app S11 S12 S21 S22 :
    (S11 <: S21) -∗ (S12 <: S22) -∗
    (S11 <++> S12) <: (S21 <++> S22).
  Proof. iIntros "#H1 #H2 !>". by iApply iProto_le_app. Qed.

  Lemma lty_le_app_id_l S : ⊢ (END <++> S) <:> S.
  Proof. rewrite /lty_app left_id. iSplit; iModIntro; iApply iProto_le_refl. Qed.
  Lemma lty_le_app_id_r S : ⊢ (S <++> END) <:> S.
  Proof. rewrite /lty_app right_id. iSplit; iModIntro; iApply iProto_le_refl. Qed.
  Lemma lty_le_app_assoc S1 S2 S3 :
    ⊢ (S1 <++> S2) <++> S3 <:> S1 <++> (S2 <++> S3).
  Proof. rewrite /lty_app assoc. iSplit; iModIntro; iApply iProto_le_refl. Qed.

  Lemma lty_le_app_send A S1 S2 : ⊢ (<!!> A; S1) <++> S2 <:> (<!!> A; S1 <++> S2).
  Proof.
    rewrite /lty_app iProto_app_message_tele.
    iSplit; iIntros "!>"; iApply iProto_le_refl.
  Qed.
  Lemma lty_le_app_recv A S1 S2 : ⊢ (<??> A; S1) <++> S2 <:> (<??> A; S1 <++> S2).
  Proof.
    rewrite /lty_app iProto_app_message_tele.
    iSplit; iIntros "!>"; iApply iProto_le_refl.
  Qed.

  Lemma lty_le_app_choice a (Ss : gmap Z (lsty Σ)) S2 :
    ⊢ lty_choice a Ss <++> S2 <:> lty_choice a ((.<++> S2) <$> Ss)%lty.
  Proof.
    destruct a.
    - rewrite /lty_app iProto_app_message_tele. iSplit; iIntros "!> /=".
      + iApply iProto_le_send; iIntros "!>" (x [S HSs]); simpl in *.
        move: HSs; rewrite lookup_fmap fmap_Some; intros (S'&HSs&->).
        iExists _; do 2 (iSplit; [by eauto|]).
        rewrite !lookup_total_alt lookup_fmap !HSs /=. iApply iProto_le_refl.
      + iApply iProto_le_send; iIntros "!>" (x [S HSs]); simpl in *.
        iExists _; iSplit; [by eauto|].
        rewrite !lookup_total_alt lookup_fmap !HSs /=.
        iSplit; [by eauto|]. iApply iProto_le_refl.
    - rewrite /lty_app iProto_app_message_tele. iSplit; iIntros "!> /=".
      + iApply iProto_le_recv; iIntros "!>" (x [S HSs]); simpl in *.
        iExists _; iSplit; [by eauto|].
        rewrite !lookup_total_alt lookup_fmap !HSs /=.
        iSplit; [by eauto|]. iApply iProto_le_refl.
      + iApply iProto_le_recv; iIntros "!>" (x [S HSs]); simpl in *.
        move: HSs; rewrite lookup_fmap fmap_Some; intros (S'&HSs&->).
        iExists _; iSplit; [by eauto|].
        rewrite !lookup_total_alt lookup_fmap !HSs /=.
        iSplit; [by eauto|]. iApply iProto_le_refl.
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
    ⊢ lty_dual (lty_message a A S) <:> lty_message (action_dual a) A (lty_dual S).
  Proof.
    iSplit; iIntros "!>"; rewrite /lty_dual iProto_dual_message_tele;
      iApply iProto_le_refl.
  Qed.
  Lemma lty_le_dual_send A S : ⊢ lty_dual (<!!> A; S) <:> (<??> A; lty_dual S).
  Proof. apply lty_le_dual_message. Qed.
  Lemma lty_le_dual_recv A S : ⊢ lty_dual (<??> A; S) <:> (<!!> A; lty_dual S).
  Proof. apply lty_le_dual_message. Qed.

  Lemma lty_le_dual_choice a (Ss : gmap Z (lsty Σ)) :
    ⊢ lty_dual (lty_choice a Ss) <:> lty_choice (action_dual a) (lty_dual <$> Ss).
  Proof.
    destruct a.
    - rewrite /lty_dual iProto_dual_message_tele. iSplit; iIntros "!> /=".
      + iApply iProto_le_recv; iIntros "!>" (x [S HSs]); simpl in *.
        iExists _; iSplit; [by eauto|].
        rewrite !lookup_total_alt lookup_fmap !HSs /=.
        iSplit; [by eauto|]. iApply iProto_le_refl.
      + iApply iProto_le_recv; iIntros "!>" (x [S HSs]); simpl in *.
        move: HSs; rewrite lookup_fmap fmap_Some; intros (S'&HSs&->).
        iExists _; iSplit; [by eauto|].
        rewrite !lookup_total_alt lookup_fmap !HSs /=.
        iSplit; [by eauto|]. iApply iProto_le_refl.
    - rewrite /lty_dual iProto_dual_message_tele. iSplit; iIntros "!> /=".
      + iApply iProto_le_send; iIntros "!>" (x [S HSs]); simpl in *.
        move: HSs; rewrite lookup_fmap fmap_Some; intros (S'&HSs&->).
        iExists _; do 2 (iSplit; [by eauto|]).
        rewrite !lookup_total_alt lookup_fmap !HSs /=. iApply iProto_le_refl.
      + iApply iProto_le_send; iIntros "!>" (x [S HSs]); simpl in *.
        iExists _; iSplit; [by eauto|].
        rewrite !lookup_total_alt lookup_fmap !HSs /=.
        iSplit; [by eauto|]. iApply iProto_le_refl.
  Qed.

  Lemma lty_le_dual_select (Ss : gmap Z (lsty Σ)) :
    ⊢ lty_dual (lty_select Ss) <:> lty_branch (lty_dual <$> Ss).
  Proof. iApply lty_le_dual_choice. Qed.
  Lemma lty_le_dual_branch (Ss : gmap Z (lsty Σ)) :
    ⊢ lty_dual (lty_branch Ss) <:> lty_select (lty_dual <$> Ss).
  Proof. iApply lty_le_dual_choice. Qed.

End subtyping_rules.
