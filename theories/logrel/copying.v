From actris.logrel Require Import types subtyping.
From actris.channel Require Import channel.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.

Section copying.
  Context `{heapG Σ, chanG Σ}.
  Implicit Types A : lty Σ.
  Implicit Types S : lsty Σ.

  Definition copyable (A : lty Σ) : iProp Σ :=
    A <: copy A.

  (* Subtyping for `copy` *)
  Lemma lty_le_copy A :
    ⊢ copy A <: A.
  Proof. by iIntros (v) "!> #H". Qed.

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

  Lemma lty_any_copyable :
    ⊢ copyable any.
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_ref_shr_copyable A :
    ⊢ copyable (ref_shr A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  Lemma lty_mutex_copyable A :
    ⊢ copyable (mutex A).
  Proof. iIntros (v) "!> #Hv !>". iFrame "Hv". Qed.

  (* Commuting rules for `copy` and other type formers *)
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
    □ (∀ A, copyable A -∗ copyable (C A)) -∗ copyable (lty_rec C).
  Proof.
    iIntros "#Hcopy".
    iLöb as "#IH".
    iIntros (v) "!> Hv".
    rewrite /lty_rec {2}fixpoint_unfold.
    (* iEval (rewrite fixpoint_unfold) *)
    (* Rewriting goes crazy here *)
  Admitted.

End copying.
