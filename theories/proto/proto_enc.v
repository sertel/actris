From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.
From osiris.proto Require Export encodable proto_specs.

Section DualProtoEnc.
  Context `{EncDec V} `{PROP: bi} .

  Definition TSR'
    (a : action) (P : V → PROP) (prot : V → proto val PROP) : proto val PROP :=
  TSR a
    (λ v, if decode v is Some x then P x else False)%I
    (λ v, if decode v is Some x then prot x else TEnd (* dummy *)).
  Global Instance: Params (@TSR') 3.

  Global Instance is_dual_tsr' a1 a2 P (st1 st2 : V → proto val PROP) :
    IsDualAction a1 a2 →
    (∀ x, IsDualProto (st1 x) (st2 x)) →
    IsDualProto (TSR' a1 P st1) (TSR' a2 P st2).
  Proof.
    rewrite /IsDualAction /IsDualProto. intros <- Hst.
    rewrite -(proto_force_eq (dual_proto _)).
    constructor=> x. done. destruct (decode x)=> //.
    apply is_dual_end.
  Qed.

End DualProtoEnc.

Notation "<!> x @ P , prot" :=
  (TSR' Send (λ x, P%I) (λ x, prot%proto))
  (at level 200, x pattern, prot at level 200) : proto_scope.
Notation "<?> x @ P , prot" :=
  (TSR' Receive (λ x, P%I) (λ x, prot%proto))
  (at level 200, x pattern, prot at level 200) : proto_scope.
Notation "<!> x , prot" := (<!> x @ True, (prot x))%proto
  (at level 200, x pattern, prot at level 200) : proto_scope.
Notation "<?> x , prot" := (<?> x @ True, (prot x))%proto
  (at level 200, x pattern, prot at level 200) : proto_scope.
Notation "<!> @ P , prot" := (<!> dummy__ @ P dummy__, prot dummy__)%proto
  (at level 200, prot at level 200) : proto_scope.
Notation "<?> @ P , prot" := (<?> dummy__ @ P dummy__, prot dummy__)%proto
  (at level 200, prot at level 200) : proto_scope.

Section proto_enc_specs.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Lemma send_st_spec (A : Type) `{EncDec A}
        prot γ c s (P : A → iProp Σ) w :
    {{{ P w ∗ ⟦ c @ s : <!> @ P, prot ⟧{N,γ} }}}
      send c #s (encode w)
    {{{ RET #(); ⟦ c @ s : prot w ⟧{N,γ} }}}.
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
        prot γ c s (P : A → iProp Σ) :
    {{{ ⟦ c @ s : <?> @ P, prot ⟧{N,γ} }}}
      recv c #s
    {{{ v, RET (encode v); ⟦ c @ s : prot v ⟧{N,γ} ∗ P v }}}.
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

End proto_enc_specs.