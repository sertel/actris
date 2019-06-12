From iris.heap_lang Require Import proofmode notation.
From osiris.proto Require Export encodable proto_specs.

Section DualProtoEnc.
  Context `{ValEncDec V} {PROP: bi} .

  Definition TSR'
      (a : action) (P : V → PROP) (prot : V → proto val PROP) : proto val PROP :=
    TSR a
      (λ v, if val_decode v is Some x then P x else False)%I
      (λ v, if val_decode v is Some x then prot x else TEnd (* dummy *)).
  Global Instance: Params (@TSR') 3.

  Global Instance is_dual_tsr' a1 a2 P (st1 st2 : V → proto val PROP) :
    IsDualAction a1 a2 →
    (∀ x, IsDualProto (st1 x) (st2 x)) →
    IsDualProto (TSR' a1 P st1) (TSR' a2 P st2).
  Proof.
    rewrite /IsDualAction /IsDualProto. intros <- Hst.
    rewrite -(proto_force_eq (dual_proto _)).
    constructor=> x. done. destruct (val_decode x)=> //.
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
  Context `{!heapG Σ, !logrelG val Σ} `{ValEncDec A} (N : namespace).

  Lemma send_st_spec prot γ c s (P : A → iProp Σ) w :
    {{{ P w ∗ ⟦ c @ s : <!> @ P, prot ⟧{N,γ} }}}
      send c #s (val_encode w)
    {{{ RET #(); ⟦ c @ s : prot w ⟧{N,γ} }}}.
  Proof.
    iIntros (Φ) "[HP Hsend] HΦ".
    iApply (send_st_spec with "[HP $Hsend]").
    { by rewrite val_encode_decode. }
    iNext. rewrite val_encode_decode.
    by iApply "HΦ".
  Qed.

  Lemma recv_st_spec prot γ c s (P : A → iProp Σ) :
    {{{ ⟦ c @ s : <?> @ P, prot ⟧{N,γ} }}}
      recv c #s
    {{{ v, RET (val_encode v); ⟦ c @ s : prot v ⟧{N,γ} ∗ P v }}}.
  Proof.
    iIntros (Φ) "Hrecv HΦ".
    iApply (recv_st_spec with "Hrecv").
    iNext. iIntros (v).
    iIntros "[H HP]".
    iAssert (∃ w, ⌜val_decode v = Some w⌝ ∗ P w)%I with "[HP]" as (w Hw) "HP".
    { destruct (val_decode v) as [x|]; last done.
      iExists x. by iFrame. }
    iSpecialize ("HΦ" $!w).
    apply val_decode_encode in Hw as <-.
    iApply "HΦ". iFrame "HP".
    by rewrite val_encode_decode.
  Qed.
End proto_enc_specs.
