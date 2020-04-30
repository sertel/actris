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
  Proof. destruct k. by iIntros (v) "!> H". by iModIntro. Qed.
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
    rewrite !lookup_total_alt !lookup_fmap fmap_is_Some; iIntros ([S ->]) "/=".
    iApply iProto_le_trans; [|iApply iProto_le_base_swap]. iSplitL; [by eauto|].
    iModIntro. by iExists v2.
  Qed.

  Lemma lty_le_select (Ss1 Ss2 : gmap Z (lsty Σ)) :
    ▷ ([∗ map] S1;S2 ∈ Ss1; Ss2, S1 <: S2) -∗
    lty_select Ss1 <: lty_select Ss2.
  Proof.
    iIntros "#H !>" (x); iDestruct 1 as %[S2 HSs2]. iExists x.
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
    intros; iIntros "!>" (x); iDestruct 1 as %[S HSs2]. iExists x.
    assert (Ss1 !! x = Some S) as HSs1 by eauto using lookup_weaken.
    rewrite HSs1. iSplitR; [by eauto|].
    iIntros "!>". by rewrite !lookup_total_alt HSs1 HSs2 /=.
  Qed.

  Lemma lty_le_branch (Ss1 Ss2 : gmap Z (lsty Σ)) :
    ▷ ([∗ map] S1;S2 ∈ Ss1; Ss2, S1 <: S2) -∗
    lty_branch Ss1 <: lty_branch Ss2.
  Proof.
    iIntros "#H !>" (x); iDestruct 1 as %[S1 HSs1]. iExists x.
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
    intros; iIntros "!>" (x); iDestruct 1 as %[S HSs1]. iExists x.
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

  Lemma lty_le_app_send A S1 S2 : ⊢ (<!!> TY A; S1) <++> S2 <:> (<!!> TY A; S1 <++> S2).
  Proof.
    rewrite /lty_app iProto_app_message iMsg_app_exist.
    setoid_rewrite iMsg_app_base. iSplit; by iIntros "!> /=".
  Qed.
  Lemma lty_le_app_recv A S1 S2 : ⊢ (<??> TY A; S1) <++> S2 <:> (<??> TY A; S1 <++> S2).
  Proof.
    rewrite /lty_app iProto_app_message iMsg_app_exist.
    setoid_rewrite iMsg_app_base. iSplit; by iIntros "!> /=".
  Qed.

  Lemma lty_le_app_choice a (Ss : gmap Z (lsty Σ)) S2 :
    ⊢ lty_choice a Ss <++> S2 <:> lty_choice a ((.<++> S2) <$> Ss)%lty.
  Proof.
    rewrite /lty_app /lty_choice iProto_app_message iMsg_app_exist;
      setoid_rewrite iMsg_app_base; setoid_rewrite lookup_total_alt;
      setoid_rewrite lookup_fmap; setoid_rewrite fmap_is_Some.
    iSplit; iIntros "!> /="; destruct a; iIntros (x); iExists x;
      iDestruct 1 as %[S ->]; iSplitR; eauto.
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
    iSplit; iIntros "!> /="; destruct a; iIntros (x); iExists x;
      iDestruct 1 as %[S ->]; iSplitR; eauto.
  Qed.

  Lemma lty_le_dual_select (Ss : gmap Z (lsty Σ)) :
    ⊢ lty_dual (lty_select Ss) <:> lty_branch (lty_dual <$> Ss).
  Proof. iApply lty_le_dual_choice. Qed.
  Lemma lty_le_dual_branch (Ss : gmap Z (lsty Σ)) :
    ⊢ lty_dual (lty_branch Ss) <:> lty_select (lty_dual <$> Ss).
  Proof. iApply lty_le_dual_choice. Qed.

End subtyping_rules.
