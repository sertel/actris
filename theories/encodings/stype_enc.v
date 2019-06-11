From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.
From osiris.encodings Require Export encodable stype.

Section DualStypeEnc.
  Context `{EncDec V} `{PROP: bi} .

  Definition TSR'
    (a : action) (P : V → PROP) (st : V → stype val PROP) : stype val PROP :=
  TSR a
    (λ v, if decode v is Some x then P x else False)%I
    (λ v, if decode v is Some x then st x else TEnd (* dummy *)).
  Global Instance: Params (@TSR') 3.

  Global Instance is_dual_tsr' a1 a2 P (st1 st2 : V → stype val PROP) :
    IsDualAction a1 a2 →
    (∀ x, IsDualStype (st1 x) (st2 x)) →
    IsDualStype (TSR' a1 P st1) (TSR' a2 P st2).
  Proof.
    rewrite /IsDualAction /IsDualStype. intros <- Hst.
    rewrite -(stype_force_eq (dual_stype _)).
    constructor=> x. done. destruct (decode x)=> //.
    apply is_dual_end.
  Qed.

End DualStypeEnc.

Notation "<!> x @ P , st" :=
  (TSR' Send (λ x, P%I) (λ x, st%stype))
  (at level 200, x pattern, st at level 200) : stype_scope.
Notation "<?> x @ P , st" :=
  (TSR' Receive (λ x, P%I) (λ x, st%stype))
  (at level 200, x pattern, st at level 200) : stype_scope.
Notation "<!> x , st" := (<!> x @ True, (st x))%stype
  (at level 200, x pattern, st at level 200) : stype_scope.
Notation "<?> x , st" := (<?> x @ True, (st x))%stype
  (at level 200, x pattern, st at level 200) : stype_scope.
Notation "<!> @ P , st" := (<!> dummy__ @ P dummy__, st dummy__)%stype
  (at level 200, st at level 200) : stype_scope.
Notation "<?> @ P , st" := (<?> dummy__ @ P dummy__, st dummy__)%stype
  (at level 200, st at level 200) : stype_scope.

Section stype_enc_specs.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Lemma send_st_spec (A : Type) `{EncDec A}
        st γ c s (P : A → iProp Σ) w :
    {{{ P w ∗ ⟦ c @ s : <!> @ P, st ⟧{N,γ} }}}
      send c #s (encode w)
    {{{ RET #(); ⟦ c @ s : st w ⟧{N,γ} }}}.
  Proof.
    iIntros (Φ) "[HP Hsend] HΦ".
    iApply (send_st_spec with "[HP Hsend]").
    simpl.
    iFrame.
    by rewrite encdec.
    iNext.
    rewrite encdec.
    by iApply "HΦ".
  Qed.

  Lemma recv_st_spec (A : Type) `{EncDec A}
        st γ c s (P : A → iProp Σ) :
    {{{ ⟦ c @ s : <?> @ P, st ⟧{N,γ} }}}
      recv c #s
    {{{ v, RET (encode v); ⟦ c @ s : st v ⟧{N,γ} ∗ P v }}}.
  Proof.
    iIntros (Φ) "Hrecv HΦ".
    iApply (recv_st_spec with "Hrecv").
    iNext. iIntros (v).
    iIntros "[H HP]".
    iAssert ((∃ w, ⌜decode v = Some w⌝ ∗ P w)%I) with "[HP]" as (w Hw) "HP".
    { destruct (decode v).
      iExists a. by iFrame. iDestruct "HP" as %HP=>//. }
    iSpecialize ("HΦ" $!w).
    apply enc_dec in Hw. rewrite Hw.
    iApply "HΦ".
    iFrame.
    apply enc_dec in Hw.
    destruct (decode v).
    - inversion Hw. subst. iApply "H".
    - inversion Hw.
  Qed.

End stype_enc_specs.