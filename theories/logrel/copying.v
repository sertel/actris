From actris.logrel Require Import ltyping types subtyping.
From actris.channel Require Import channel.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import notation proofmode.
From iris.bi.lib Require Export core.

(* TODO: Coq fails to infer what the Σ should be if I move some of these
definitions out of the section or into a different section with its own Context
declaration. *)

Section copying.
  Context `{heapG Σ, chanG Σ}.
  Implicit Types A : lty Σ.
  Implicit Types S : lsty Σ.

  (* We define the copyability of semantic types in terms of subtyping. *)
  Definition copyable (A : lty Σ) : iProp Σ :=
    A <: copy A.

  (* Subtyping for `copy` and `copy-` *)
  Lemma lty_le_copy A :
    ⊢ copy A <: A.
  Proof. by iIntros (v) "!> #H". Qed.

  Lemma coreP_desired_lemma (P : iProp Σ) :
    □ (P -∗ □ P) -∗ coreP P -∗ P.
  Proof.
    iIntros "HP Hcore".
  Admitted.

  Lemma lty_le_copy_minus A :
    copyable A -∗ copy- A <: A.
  Proof.
    iIntros "#HA". iIntros (v) "!> #Hv".
    iSpecialize ("HA" $! v).
    iApply coreP_desired_lemma.
    - iModIntro. iApply "HA".
    - iApply "Hv".
  Qed.

  (* Copyability of types *)
  Lemma lty_unit_copyable :
    ⊢ copyable ().
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_bool_copyable :
    ⊢ copyable lty_bool.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_int_copyable :
    ⊢ copyable lty_int.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  (* TODO: Use Iris quantification here instead of Coq quantification? (Or doesn't matter?) *)
  Lemma lty_copy_copyable A :
    ⊢ copyable (copy A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_copyminus_copyable A :
    ⊢ copyable (copy- A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_any_copyable :
    ⊢ copyable any.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_ref_shr_copyable A :
    ⊢ copyable (ref_shr A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_mutex_copyable A :
    ⊢ copyable (mutex A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  (* Rules about combining `copy` and other type formers *)
  Lemma lty_prod_copy_comm A B :
    ⊢ copy A * copy B <:> copy (A * B).
  Proof.
    iSplit; iModIntro; iIntros (v) "#Hv"; iDestruct "Hv" as (v1 v2 ->) "[Hv1 Hv2]".
    - iModIntro. iExists v1, v2. iSplit=>//. iSplitL; iModIntro; auto.
    - iExists v1, v2. iSplit=>//. iSplit; iModIntro; iModIntro; auto.
  Qed.

  Lemma lty_sum_copy_comm A B :
    ⊢ copy A + copy B <:> copy (A + B).
  Proof.
    iSplit; iModIntro; iIntros (v) "#Hv";
      iDestruct "Hv" as "[Hv|Hv]"; iDestruct "Hv" as (w) "[Heq Hw]";
        try iModIntro.
    - iLeft. iExists w. iFrame "Heq". iModIntro. iApply "Hw".
    - iRight. iExists w. iFrame "Heq". iModIntro. iApply "Hw".
    - iLeft. iExists w. iFrame "Heq". iModIntro. iModIntro. iApply "Hw".
    - iRight. iExists w. iFrame "Heq". iModIntro. iModIntro. iApply "Hw".
  Qed.

  Lemma lty_exist_copy_comm F :
    ⊢ (∃ A, copy (F A)) <:> copy (∃ A, F A).
  Proof.
    iSplit; iModIntro; iIntros (v) "#Hv";
      iDestruct "Hv" as (A) "Hv"; try iModIntro;
        iExists A; repeat iModIntro; iApply "Hv".
  Qed.

  (* TODO: Do the forall type former, once we have the value restriction *)

  (* Copyability of recursive types *)
  Lemma lty_rec_copy C `{!Contractive C} :
    □ (∀ A, ▷ copyable A -∗ copyable (C A)) -∗ copyable (lty_rec C).
  Proof.
    iIntros "#Hcopy".
    iLöb as "IH".
    iIntros (v) "!> Hv".
    rewrite /lty_rec.
    rewrite {2}fixpoint_unfold.
    iSpecialize ("Hcopy" with "IH").
    rewrite {3}/lty_rec_aux.
    iSpecialize ("Hcopy" with "Hv").
    iDestruct "Hcopy" as "#Hcopy".
    iModIntro.
    iEval (rewrite fixpoint_unfold).
    iApply "Hcopy".
  Qed.

  (* TODO: Get rid of side condition that x does not appear in Γ *)
  Lemma env_split_copy Γ Γ1 Γ2 (x : string) A:
    Γ !! x = None → Γ1 !! x = None → Γ2 !! x = None →
    copyable A -∗
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
    copyable A -∗
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

  (* TODO: Maybe move this back to `typing.v` (requires restructuring to avoid
  circular dependencies). *)
  (* Typing rule for introducing copyable functions *)

  Lemma ltyped_rec Γ Γ' f x e A1 A2 :
    env_copy Γ Γ' -∗
    (binder_insert f (A1 → A2)%lty (binder_insert x A1 Γ') ⊨ e : A2) -∗
    Γ ⊨ (rec: f x := e) : A1 → A2 ⫤ ∅.
  Proof.
    iIntros "#Hcopy #He". iIntros (vs) "!> HΓ /=". iApply wp_fupd. wp_pures.
    iDestruct ("Hcopy" with "HΓ") as "HΓ".
    iMod (fupd_mask_mono with "HΓ") as "#HΓ"; first done.
    iModIntro. iSplitL; last by iApply env_ltyped_empty.
    iLöb as "IH".
    iIntros (v) "!> HA1". wp_pures. set (r := RecV f x _).
    iDestruct ("He" $!(binder_insert f r (binder_insert x v vs))
                  with "[HΓ HA1]") as "He'".
    { iApply (env_ltyped_insert with "IH").
      iApply (env_ltyped_insert with "HA1 HΓ"). }
    iDestruct (wp_wand _ _ _ _ (λ v, A2 v) with "He' []") as "He'".
    { iIntros (w) "[$ _]". }
    destruct x as [|x], f as [|f]; rewrite /= -?subst_map_insert //.
    destruct (decide (x = f)) as [->|].
    - by rewrite subst_subst delete_idemp !insert_insert -subst_map_insert.
    - rewrite subst_subst_ne // -subst_map_insert.
      by rewrite -delete_insert_ne // -subst_map_insert.
  Qed.

End copying.
