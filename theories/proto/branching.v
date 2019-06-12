From iris.heap_lang Require Import proofmode notation.
From osiris.proto Require Export proto_enc.

Definition TSB {PROP : bi} (a : action)
    (prot1 prot2 : proto val PROP) : proto val PROP :=
  TSR' a (λ _, True)%I (λ v, if v : bool then prot1 else prot2).
Global Typeclasses Opaque TSB.
Infix "<+>" := (TSB Send) (at level 85) : proto_scope.
Infix "<&>" := (TSB Receive) (at level 85) : proto_scope.

Definition select : val := λ: "c" "s" "b", send "c" "s" "b".
Definition branch : val := λ: "c" "s" "b1" "b2",
  if: recv "c" "s" then "b1" else "b2".
(* TODO: This notation should be fixed *)
Notation "'branch:' c @ s 'left' e1 'right' e2" :=
  (branch c s (λ: <>, e1)%E (λ: <>, e2)%E #())
    (at level 200, c, s, e1, e2 at level 200) : expr_scope.

Global Instance is_dual_tsb {PROP : bi} a1 a2
    (proto1 proto1' proto2 proto2' : proto val PROP) :
  IsDualAction a1 a2 →
  IsDualProto proto1 proto1' → IsDualProto proto2 proto2' →
  IsDualProto (TSB a1 proto1 proto2) (TSB a2 proto1' proto2').
Proof.
  rewrite /IsDualAction.
  rewrite /IsDualProto.
  intros Ha Hst1 Hst2.
  destruct a1.
  - simpl.
    simpl in Ha. rewrite -Ha.
    rewrite -(proto_force_eq (dual_proto _)).
    constructor.
    f_equiv.
    f_equiv.
    destruct (val_decode a).
    by destruct b. apply is_dual_end.
  - simpl.
    simpl in Ha. rewrite -Ha.
    rewrite -(proto_force_eq (dual_proto _)).
    constructor.
    f_equiv.
    f_equiv.
    destruct (val_decode a).
    by destruct b.
    apply is_dual_end.
Qed.

Section branching_specs.
  Context `{!heapG Σ, !logrelG val Σ} (N : namespace).

  Lemma select_st_spec proto1 proto2 γ c s (b : side) :
    {{{ ⟦ c @ s : proto1 <+> proto2 ⟧{N,γ} }}}
      select c #s #b
    {{{ RET #(); ⟦ c @ s : (if b then proto1 else proto2) ⟧{N,γ} }}}.
  Proof.
    iIntros (Φ) "Hproto HΦ".
    wp_pures. wp_lam.
    wp_pures. rewrite /TSB.
    wp_apply (send_st_spec (A:=bool) with "[$Hproto //]"); iIntros "Hstl".
    iApply "HΦ". by destruct b.
  Qed.

  Lemma branch_st_spec proto1 proto2 γ c s (b1 b2 : val) :
    {{{ ⟦ c @ s : proto1 <&> proto2 ⟧{N,γ} }}}
      branch c #s b1 b2
    {{{ v, RET v; (⌜v = b1%V⌝ ∧ ⟦ c @ s : proto1 ⟧{N,γ}) ∨
                  (⌜v = b2%V⌝ ∧ ⟦ c @ s : proto2 ⟧{N,γ})}}}.
  Proof.
    iIntros (Φ').
    iIntros "Hproto HΦ'".
    wp_pures.
    wp_lam. rewrite /TSB. simpl.
    wp_apply (recv_st_spec (A:=bool) with "[$Hproto //]").
    iIntros ([]) "[Hstl _]".
    - wp_pures. iApply ("HΦ'"). eauto with iFrame.
    - wp_pures. iApply ("HΦ'"). eauto with iFrame.
  Qed.
End branching_specs.
