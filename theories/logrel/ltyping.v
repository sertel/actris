From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import adequacy notation proofmode.

(* The domain of semantic types: Iris predicates over values *)
Record lty Σ := Lty {
  lty_car :> val → iProp Σ;
}.
Arguments Lty {_} _%I.
Arguments lty_car {_} _ _ : simpl never.
Bind Scope lty_scope with lty.
Delimit Scope lty_scope with lty.

(* The COFE structure on semantic types *)
Section lty_ofe.
  Context `{Σ : gFunctors}.

  (* Equality of semantic types is extensional equality *)
  Instance lty_equiv : Equiv (lty Σ) := λ A B, ∀ w, A w ≡ B w.
  Instance lty_dist : Dist (lty Σ) := λ n A B, ∀ w, A w ≡{n}≡ B w.

  (* OFE and COFE structure is taken from isomorphism with val -d> iProp Σ *)
  Lemma lty_ofe_mixin : OfeMixin (lty Σ).
  Proof. by apply (iso_ofe_mixin (lty_car : _ → val -d> _)). Qed.
  Canonical Structure ltyO := OfeT (lty Σ) lty_ofe_mixin.

  Global Instance lty_cofe : Cofe ltyO.
  Proof. by apply (iso_cofe (@Lty _ : (val -d> _) → ltyO) lty_car). Qed.

  Global Instance lty_inhabited : Inhabited (lty Σ) := populate (Lty inhabitant).

  Global Instance lty_car_ne n : Proper (dist n ==> (=) ==> dist n) lty_car.
  Proof. by intros A A' ? w ? <-. Qed.
  Global Instance lty_car_proper : Proper ((≡) ==> (=) ==> (≡)) lty_car.
  Proof. by intros A A' ? w ? <-. Qed.

  Global Instance lty_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) Lty.
  Proof. by intros ???. Qed.
  Global Instance lty_proper : Proper (pointwise_relation _ (≡) ==> (≡)) Lty.
  Proof. by intros ???. Qed.
End lty_ofe.

Arguments ltyO : clear implicits.

(* Typing for operators *)
Class LTyUnboxed {Σ} (A : lty Σ) :=
  lty_unboxed v : A v -∗ ⌜ val_is_unboxed v ⌝.

Class LTyUnOp {Σ} (op : un_op) (A B : lty Σ) :=
  lty_un_op v : A v -∗ ∃ w, ⌜ un_op_eval op v = Some w ⌝ ∗ B w.

Class LTyBinOp {Σ} (op : bin_op) (A1 A2 B : lty Σ) :=
  lty_bin_op v1 v2 : A1 v1 -∗ A2 v2 -∗ ∃ w, ⌜ bin_op_eval op v1 v2 = Some w ⌝ ∗ B w.

(* Copy types *)
Class LTyCopy `{invG Σ} (A : lty Σ) :=
  lty_copy_pers v :> Persistent (A v).

Section Environment.
  Context `{invG Σ}.
  Implicit Types A : lty Σ.

  Definition env_ltyped (Γ : gmap string (lty Σ))
             (vs : gmap string val) : iProp Σ :=
    ([∗ map] i ↦ A ∈ Γ, ∃ v, ⌜vs !! i = Some v⌝ ∗ lty_car A v)%I.

  Lemma env_ltyped_empty vs : ⊢ env_ltyped ∅ vs.
  Proof. by iApply big_sepM_empty. Qed.

  Lemma env_ltyped_lookup Γ vs x A :
    Γ !! x = Some A →
    env_ltyped Γ vs -∗ ∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v ∗ env_ltyped (delete x Γ) vs.
  Proof.
    iIntros (HΓx) "HΓ".
    iPoseProof (big_sepM_delete with "HΓ") as "[H1 H2]"; eauto.
    iDestruct "H1" as (v) "H1".
    eauto with iFrame.
  Qed.

  Lemma env_ltyped_insert Γ vs x A v :
    A v -∗ env_ltyped Γ vs -∗
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

  Definition env_split (Γ Γ1 Γ2 : gmap string (lty Σ)) : iProp Σ :=
    □ ∀ vs, (env_ltyped Γ vs ∗-∗ (env_ltyped Γ1 vs ∗ env_ltyped Γ2 vs)).

  Lemma env_split_None Γ Γ1 Γ2 x :
    Γ !! x = None → env_split Γ Γ1 Γ2 -∗ ⌜Γ1 !! x = None ∧ Γ2 !! x = None⌝.
  Proof.
    iIntros (HΓx) "Hsplit".
    rewrite /env_split. rewrite /env_ltyped.
  Admitted.

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

  Lemma env_split_empty : ⊢ env_split ∅ ∅ ∅.
  Proof.
    iIntros "!>" (vs).
    iSplit.
    - iIntros "HΓ". rewrite /env_ltyped. auto.
    - iIntros "[HΓ1 HΓ2]". auto.
  Qed.

  Lemma env_split_left Γ Γ1 Γ2 x A:
    Γ !! x = None →
    env_split Γ Γ1 Γ2 -∗
    env_split (<[x := A]> Γ) (<[x := A]> Γ1) Γ2.
  Proof.
    iIntros (HΓx) "#Hsplit !>". iIntros (vs).
    iSplit.
    - iIntros "HΓ".
      iPoseProof (big_sepM_insert with "HΓ") as "[Hv HΓ]"; first by assumption.
      iDestruct ("Hsplit" with "HΓ") as "[HΓ1 $]".
      iApply (big_sepM_insert_2 with "[Hv]"); simpl; eauto.
    - iIntros "[HΓ1 HΓ2]".
      iPoseProof (env_split_None with "Hsplit") as "[% %]"; first by apply HΓx.
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

  Lemma env_split_right Γ Γ1 Γ2 x A:
    Γ !! x = None →
    env_split Γ Γ1 Γ2 -∗
    env_split (<[x := A]> Γ) Γ1 (<[x := A]> Γ2).
  Proof.
    iIntros (HΓx) "Hsplit".
    iApply env_split_comm. iApply env_split_left; first by assumption.
    by iApply env_split_comm.
  Qed.

  (* TODO: Get rid of side condition that x does not appear in Γ *)
  Lemma env_split_copy Γ Γ1 Γ2 (x : string) A:
    Γ !! x = None →
    LTyCopy A →
    env_split Γ Γ1 Γ2 -∗
    env_split (<[x:=A]> Γ) (<[x:=A]> Γ1) (<[x:=A]> Γ2).
  Proof.
    iIntros (HΓx Hcopy) "#Hsplit". iIntros (vs) "!>".
    iSplit.
    - iIntros "HΓ".
      iPoseProof (big_sepM_insert with "HΓ") as "[Hv HΓ]"; first by assumption.
      iDestruct "Hv" as (v ?) "#HAv".
      iDestruct ("Hsplit" with "HΓ") as "[HΓ1 HΓ2]".
      iSplitL "HΓ1"; iApply big_sepM_insert_2; simpl; eauto.
    - iIntros "[HΓ1 HΓ2]".
      iPoseProof (env_split_None with "Hsplit") as "[% %]"; first by apply HΓx.
      iPoseProof (big_sepM_insert with "HΓ1") as "[Hv HΓ1]"; first by assumption.
      iPoseProof (big_sepM_insert with "HΓ2") as "[_ HΓ2]"; first by assumption.
      iApply (big_sepM_insert_2 with "[Hv]")=> //.
      iApply "Hsplit". iFrame "HΓ1 HΓ2".
  Qed.

  (* (* TODO: Prove lemmas about this *) *)
  Definition env_copy (Γ Γ' : gmap string (lty Σ)) : iProp Σ :=
    □ ∀ vs, env_ltyped Γ vs -∗ □ env_ltyped Γ' vs.

  Lemma env_copy_empty : ⊢ env_copy ∅ ∅.
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

  Lemma env_copy_extend_copy x A Γ Γ' :
    Γ !! x = None →
    Γ' !! x = None →
    LTyCopy A →
    env_copy Γ Γ' -∗
    env_copy (<[x:=A]> Γ) (<[x:=A]> Γ').
  Proof.
    iIntros (HΓx HΓ'x HcopyA) "#Hcopy". iIntros (vs) "!> Hvs". rewrite /env_ltyped.
    iDestruct (big_sepM_insert with "Hvs") as "[HA Hvs]"; first done.
    iDestruct ("Hcopy" with "Hvs") as "#Hvs'".
    iDestruct "HA" as (v ?) "#HA".
    iIntros "!>". iApply big_sepM_insert; first done. iSplitL; eauto.
  Qed.
End Environment.

(* The semantic typing judgement *)
Definition ltyped `{!heapG Σ}
    (Γ Γ' : gmap string (lty Σ)) (e : expr) (A : lty Σ) : iProp Σ :=
  □ ∀ vs, env_ltyped Γ vs -∗
          WP subst_map vs e {{ v, A v ∗ env_ltyped Γ' vs }}.

Notation "Γ ⊨ e : A ⫤ Γ'" := (ltyped Γ Γ' e A)
  (at level 100, e at next level, A at level 200).

Notation "Γ ⊨ e : A" := (ltyped Γ Γ e A)
  (at level 100, e at next level, A at level 200).

Lemma ltyped_frame `{!heapG Σ} (Γ Γ' Γ1 Γ1' Γ2 : gmap string (lty Σ)) e A :
  env_split Γ Γ1 Γ2 -∗ env_split Γ' Γ1' Γ2 -∗
  (Γ1 ⊨ e : A ⫤ Γ1') -∗ Γ ⊨ e : A ⫤ Γ'.
Proof.
  iIntros "#Hsplit #Hsplit' #Htyped !>" (vs) "Henv".
  iDestruct ("Hsplit" with "Henv") as "[Henv1 Henv2]".
  iApply (wp_wand with "(Htyped Henv1)").
  iIntros (v) "[$ Henv1']".

  iApply "Hsplit'". iFrame "Henv1' Henv2".
Qed.

Lemma ltyped_safety `{heapPreG Σ} e σ es σ' e' Γ' :
  (∀ `{heapG Σ}, ∃ A, ⊢ ∅ ⊨ e : A ⫤ Γ') →
  rtc erased_step ([e], σ) (es, σ') → e' ∈ es →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hty. apply (heap_adequacy Σ NotStuck e σ (λ _, True))=> // ?.
  destruct (Hty _) as [A He]. iStartProof.
  iDestruct (He) as "He".
  iSpecialize ("He" $!∅).
  iSpecialize ("He" with "[]"); first by rewrite /env_ltyped.
  iEval (rewrite -(subst_map_empty e)). iApply (wp_wand with "He"); auto.
Qed.
