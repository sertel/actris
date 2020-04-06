From actris.logrel Require Import types.
From actris.channel Require Import channel.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.

Definition lty_le {Σ} (A1 A2 : lty Σ) : iProp Σ :=
  □ ∀ v, (A1 v -∗ A2 v).

Arguments lty_le {_} _%lty _%lty.
Infix "<:" := lty_le (at level 70).
Instance: Params (@lty_le) 1 := {}.

Instance lty_le_ne {Σ} : NonExpansive2 (@lty_le Σ).
Proof. solve_proper. Qed.
Instance lty_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@lty_le Σ).
Proof. solve_proper. Qed.

Definition lsty_le {Σ} (P1 P2 : lsty Σ) : iProp Σ :=
  □ (iProto_le P1 P2).

Arguments lsty_le {_} _%lsty _%lsty.
Infix "<p:" := lsty_le (at level 70).
Instance: Params (@lsty_le) 1 := {}.

Instance lsty_le_ne {Σ} : NonExpansive2 (@lsty_le Σ).
Proof. solve_proper_prepare. f_equiv. solve_proper. Qed.
Instance lsty_le_proper {Σ} :
  Proper ((≡) ==> (≡) ==> (≡)) (@lsty_le Σ).
Proof. apply ne_proper_2. apply _. Qed.

Section subtype.
  Context `{heapG Σ, chanG Σ}.
  Implicit Types A : lty Σ.
  Implicit Types P : lsty Σ.

  Lemma lty_le_refl A : ⊢ A <: A.
  Proof. by iIntros (v) "!> H". Qed.

  Lemma lty_le_trans A1 A2 A3 : A1 <: A2 -∗ A2 <: A3 -∗ A1 <: A3.
  Proof. iIntros "#H1 #H2" (v) "!> H". iApply "H2". by iApply "H1". Qed.

  Lemma lty_le_copy A : ⊢ copy A <: A.
  Proof. by iIntros (v) "!> #H". Qed.

  Lemma lty_le_copyable A `{LTyCopy Σ A} : ⊢ A <: copy A.
  Proof. by iIntros (v) "!> #H". Qed.

  Lemma lty_arr_le A11 A12 A21 A22 :
    ▷ (A21 <: A11) -∗ ▷ (A12 <: A22) -∗
    (A11 ⊸ A12) <: (A21 ⊸ A22).
  Proof.
    iIntros "#H1 #H2" (v) "!> H". iIntros (w) "H'".
    iApply (wp_step_fupd); first done.
    { iIntros "!>!>!>". iExact "H2". }
    iApply (wp_wand with "(H (H1 H'))"). iIntros (v') "H Hle !>".
    by iApply "Hle".
  Qed.

  Lemma lty_arr_copy_le A11 A12 A21 A22 :
    ▷ (A21 <: A11) -∗ ▷ (A12 <: A22) -∗
    (A11 → A12) <: (A21 → A22).
  Proof. iIntros "#H1 #H2" (v) "!> #H !>". by iApply lty_arr_le. Qed.

  Lemma lty_prod_le A11 A12 A21 A22 :
    ▷ (A11 <: A21) -∗ ▷ (A12 <: A22) -∗
    A11 * A12 <: A21 * A22.
  Proof.
    iIntros "#H1 #H2" (v) "!>". iDestruct 1 as (w1 w2 ->) "[H1' H2']".
    iExists _, _.
    iDestruct ("H1" with "H1'") as "$".
    by iDestruct ("H2" with "H2'") as "$".
  Qed.

  Lemma lty_sum_le A11 A12 A21 A22 :
    ▷ (A11 <: A21) -∗ ▷ (A12 <: A22) -∗
    A11 + A12 <: A21 + A22.
  Proof.
    iIntros "#H1 #H2" (v) "!> [H | H]"; iDestruct "H" as (w ->) "H".
    - iDestruct ("H1" with "H") as "H1'". iLeft; eauto.
    - iDestruct ("H2" with "H") as "H2'". iRight; eauto.
  Qed.

  Lemma lty_any_le A : ⊢ A <: lty_any.
  Proof. by iIntros (v) "!> H". Qed.

  Lemma lty_forall_le C1 C2 :
    ▷ (∀ A, C1 A <: C2 A) -∗
    (∀ A, C1 A) <: (∀ A, C2 A).
  Proof.
    iIntros "#Hle" (v) "!> H". iIntros (w).
    iApply (wp_step_fupd); first done.
    { iIntros "!>!>!>". iExact "Hle". }
    iApply (wp_wand with "H"). iIntros (v') "H Hle' !>".
    by iApply "Hle'".
  Qed.

  Lemma lty_exist_le C1 C2 :
    ▷ (∀ A, C1 A <: C2 A) -∗
    (∃ A, C1 A) <: (∃ A, C2 A).
  Proof.
    iIntros "#Hle" (v) "!>". iDestruct 1 as (A) "H". iExists A. by iApply "Hle".
  Qed.

  Lemma lty_rec_le_1 (C : lty Σ → lty Σ) `{!Contractive C} :
    ⊢ lty_rec C <: C (lty_rec C).
  Proof.
    rewrite {1}/lty_rec {1}fixpoint_unfold {1}/lty_rec_aux. iApply lty_le_refl.
  Qed.
  Lemma lty_rec_le_2 (C : lty Σ → lty Σ) `{!Contractive C} :
    ⊢ C (lty_rec C) <: lty_rec C.
  Proof.
    rewrite {2}/lty_rec {1}fixpoint_unfold {1}/lty_rec_aux. iApply lty_le_refl.
  Qed.

  Lemma lty_rec_le `{Contractive C1, Contractive C2} :
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

  Lemma lty_ref_mut_le A1 A2 :
    ▷ (A1 <: A2) -∗
    ref_mut A1 <: ref_mut A2.
  Proof.
    iIntros "#H1" (v) "!>". iDestruct 1 as (l w ->) "[Hl HA]".
    iDestruct ("H1" with "HA") as "HA".
    iExists l, w. by iFrame.
  Qed.

  Lemma lty_weak_ref_le A1 A2 :
    ▷ (A1 <: A2) -∗ ▷ (A2 <: A1) -∗
    ref_shr A1 <: ref_shr A2.
  Proof.
    iIntros "#Hle1 #Hle2" (v) "!>". iDestruct 1 as (l ->) "Hinv".
    iExists l. iSplit; first done.
    iApply (inv_iff with "Hinv"). iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle1".
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl". by iApply "Hle2".
  Qed.

  Lemma lty_mutex_le A1 A2 :
    ▷ (A1 <: A2) -∗ ▷ (A2 <: A1) -∗
    mutex A1 <: mutex A2.
  Proof.
    iIntros "#Hle1 #Hle2" (v) "!>". iDestruct 1 as (γ l lk ->) "Hinv".
    rewrite /spin_lock.is_lock.
    iExists γ, l, lk. iSplit; first done.
    rewrite /spin_lock.is_lock.
    iDestruct "Hinv" as (l' ->) "Hinv".
    iExists l'.
    iSplit; first done.
    iApply (inv_iff with "Hinv"); iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl".
      destruct v; first done.
      iDestruct "HA" as "[Hown HA]". iDestruct "HA" as (inner) "[Hinner HA]".
      iDestruct ("Hle1" with "HA") as "HA". eauto with iFrame.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl".
      destruct v; first done.
      iDestruct "HA" as "[Hown HA]". iDestruct "HA" as (inner) "[Hinner HA]".
      iDestruct ("Hle2" with "HA") as "HA". eauto with iFrame.
  Qed.

  Lemma lty_mutexguard_le A1 A2 :
    ▷ (A1 <: A2) -∗ ▷ (A2 <: A1) -∗
    mutexguard A1 <: mutexguard A2.
  Proof.
    iIntros "#Hle1 #Hle2" (v) "!>".
    iDestruct 1 as (γ l lk w ->) "[Hinv [Hlock Hinner]]".
    rewrite /spin_lock.is_lock.
    iExists γ, l, lk, w. iSplit; first done.
    rewrite /spin_lock.is_lock.
    iFrame "Hlock Hinner".
    iDestruct "Hinv" as (l' ->) "Hinv".
    iExists l'.
    iSplit; first done.
    iApply (inv_iff with "Hinv"); iIntros "!> !>". iSplit.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl".
      destruct v; first done.
      iDestruct "HA" as "[Hown HA]". iDestruct "HA" as (inner) "[Hinner HA]".
      iDestruct ("Hle1" with "HA") as "HA". eauto with iFrame.
    - iDestruct 1 as (v) "[Hl HA]". iExists v. iFrame "Hl".
      destruct v; first done.
      iDestruct "HA" as "[Hown HA]". iDestruct "HA" as (inner) "[Hinner HA]".
      iDestruct ("Hle2" with "HA") as "HA". eauto with iFrame.
  Qed.

  Lemma lsty_le_refl P : ⊢ P <p: P.
  Proof. iApply iProto_le_refl. Qed.

  Lemma lsty_send_le A1 A2 P1 P2 :
    ▷ (A2 <: A1) -∗ ▷ (P1 <p: P2) -∗
    (<!!> A1 ; P1) <p: (<!!> A2 ; P2).
  Proof.
    iIntros "#HAle #HPle !>".
    iApply iProto_le_send=> /=.
    iIntros (x) "H !>".
    iDestruct ("HAle" with "H") as "H".
    eauto with iFrame.
  Qed.

  Lemma lsty_recv_le A1 A2 P1 P2 :
    ▷ (A1 <: A2) -∗ ▷ (P1 <p: P2) -∗
    (<??> A1 ; P1) <p: (<??> A2 ; P2).
  Proof.
    iIntros "#HAle #HPle !>".
    iApply iProto_le_recv=> /=.
    iIntros (x) "H !>".
    iDestruct ("HAle" with "H") as "H".
    eauto with iFrame.
  Qed.

  Lemma lsty_swap_le (A1 A2 : lty Σ) (P : lsty Σ) :
    ⊢ (<??> A1 ; <!!> A2 ; P) <p: (<!!> A2 ; <??> A1 ; P).
  Proof.
    iIntros "!>".
    iApply iProto_le_swap. iIntros (x1 x2) "/= HP1 HP2".
    iExists _, _,
      (tele_app (TT:=[tele _]) (λ x2, (x2, A2 x2, (P:iProto Σ)))),
      (tele_app (TT:=[tele _]) (λ x1, (x1, A1 x1, (P:iProto Σ)))),
    x2, x1.
    simpl.
    do 2 (iSplit; [done|]).
    iFrame "HP1 HP2".
    iModIntro.
    do 2 (iSplitR; [iApply iProto_le_refl|]). by iFrame.
  Qed.

  Lemma lsty_select_le P11 P12 P21 P22 :
    ▷ (P11 <p: P21) -∗ ▷ (P12 <p: P22) -∗
    (P11 <+++> P12) <p: (P21 <+++> P22).
  Proof.
    iIntros "#H1 #H2 !>".
    rewrite /lsty_select /iProto_branch=> /=.
    iApply iProto_le_send=> /=.
    iIntros (x) "_ !>".
    destruct x; eauto with iFrame.
  Qed.

  Lemma lsty_branch_le P11 P12 P21 P22 :
    ▷ (P11 <p: P21) -∗ ▷ (P12 <p: P22) -∗
    (P11 <&&&> P12) <p: (P21 <&&&> P22).
  Proof.
    iIntros "#H1 #H2 !>".
    rewrite /lsty_branch /iProto_branch=> /=.
    iApply iProto_le_recv=> /=.
    iIntros (x) "_ !>".
    destruct x; eauto with iFrame.
  Qed.

  Lemma lsty_app_le P11 P12 P21 P22 :
    (P11 <p: P21) -∗ (P12 <p: P22) -∗
    (P11 <++++> P12) <p: (P21 <++++> P22).
  Proof. iIntros "#H1 #H2 !>". by iApply iProto_le_app. Qed.

  Lemma lsty_dual_le P1 P2 : P2 <p: P1 -∗ lsty_dual P1 <p: lsty_dual P2.
  Proof. iIntros "#H !>". by iApply iProto_le_dual. Qed.

  Lemma lsty_rec_le_1 (C : lsty Σ → lsty Σ) `{!Contractive C} :
    ⊢ lsty_rec C <p: C (lsty_rec C).
  Proof.
    rewrite {1}/lsty_rec {1}fixpoint_unfold {1}/lsty_rec1.
    iApply lsty_le_refl.
  Qed.
  Lemma lsty_rec_le_2 (C : lsty Σ → lsty Σ) `{!Contractive C} :
    ⊢ C (lsty_rec C) <p: lsty_rec C.
  Proof.
    rewrite {2}/lsty_rec {1}fixpoint_unfold {1}/lsty_rec1.
    iApply lsty_le_refl.
  Qed.

  Lemma lsty_rec_le `{Contractive C1, Contractive C2} :
    (□ ∀ P P', ▷ (P <p: P') -∗ C1 P <p: C2 P') -∗
    lsty_rec C1 <p: lsty_rec C2.
  Proof.
    iIntros "#Hle".
    iLöb as "IH".
    iIntros "!>".
    rewrite /lsty_rec.
    iEval (rewrite fixpoint_unfold).
    iEval (rewrite (fixpoint_unfold (lsty_rec1 C2))).
    rewrite {1 3}/lsty_rec1.
    iApply ("Hle" with "[]").
    iNext. iApply "IH".
  Qed.

  Lemma lty_chan_le P1 P2 :
    ▷ (P1 <p: P2) -∗ chan P1 <: chan P2.
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
