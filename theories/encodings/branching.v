From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.
From osiris.encodings Require Export stype_enc.

Section DualBranch.
  Context `{PROP : bi}.

  Definition TSB (a : action)
             (st1 st2 : stype val PROP) : stype val PROP :=
    TSR' a (λ _, True)%I (λ v, if v : bool then st1 else st2).

  Global Instance is_dual_tsb a1 a2 st1 st1' st2 st2' :
    IsDualAction a1 a2 →
    IsDualStype st1 st1' → IsDualStype st2 st2' →
    IsDualStype (TSB a1 st1 st2) (TSB a2 st1' st2').
  Proof.
    rewrite /IsDualAction.
    rewrite /IsDualStype.
    intros Ha Hst1 Hst2.
    destruct a1.
    - simpl.
      simpl in Ha. rewrite -Ha.
      rewrite -(stype_force_eq (dual_stype _)).
      constructor.
      f_equiv.
      f_equiv.
      destruct (decode a).
      by destruct b. apply is_dual_end.
    - simpl.
      simpl in Ha. rewrite -Ha.
      rewrite -(stype_force_eq (dual_stype _)).
      constructor.
      f_equiv.
      f_equiv.
      destruct (decode a).
      by destruct b.
      apply is_dual_end.
  Qed.
End DualBranch.
Global Typeclasses Opaque TSB.

Infix "<+>" := (TSB Send) (at level 85) : stype_scope.
Infix "<&>" := (TSB Receive) (at level 85) : stype_scope.

Section branching_specs.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Definition select : val :=
    λ: "c" "s" "b",
      send "c" "s" "b".

  Lemma select_st_spec st1 st2 γ c s (b : side) :
    {{{ ⟦ c @ s : st1 <+> st2 ⟧{N,γ} }}}
      select c #s #b
    {{{ RET #(); ⟦ c @ s : (if b then st1 else st2) ⟧{N,γ} }}}.
  Proof.
    iIntros (Φ) "Hst HΦ".
    wp_pures. wp_lam.
    wp_pures. rewrite /TSB.
    wp_apply (send_st_spec N bool with "[$Hst //]");
    iIntros "Hstl".
    iApply "HΦ".
    by destruct b.
  Qed.
  
  Definition branch : val :=
    λ: "c" "s" "b1" "b2",
      if: recv "c" "s"
       then "b1"
       else "b2".

  Lemma branch_st_spec st1 st2 γ c s (b1 b2 : val) :
    {{{ ⟦ c @ s : st1 <&> st2 ⟧{N,γ} }}}
      branch c #s b1 b2
    {{{ v, RET v; (⌜v = b1%V⌝ ∧ ⟦ c @ s : st1 ⟧{N,γ}) ∨
                  (⌜v = b2%V⌝ ∧ ⟦ c @ s : st2 ⟧{N,γ})}}}.
  Proof.
    iIntros (Φ').
    iIntros "Hst HΦ'".
    wp_pures.
    wp_lam. rewrite /TSB. simpl.
    wp_apply (recv_st_spec N bool with "[$Hst //]").
    iIntros (v) "[Hstl _]".
    destruct v.
    - wp_pures. iApply ("HΦ'"). eauto with iFrame.
    - wp_pures. iApply ("HΦ'"). eauto with iFrame.
  Qed.

End branching_specs.