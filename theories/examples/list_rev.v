From actris.channel Require Import proofmode proto channel.
From iris.proofmode Require Import proofmode.
From actris.utils Require Import llist.

Definition list_rev_service : val :=
  λ: "c",
    let: "l" := recv "c" in
    lreverse "l";; send "c" #().

Definition list_rev_client : val :=
  λ: "l",
    let: "c" := start_chan list_rev_service in
    send "c" "l";; recv "c".

Section list_rev_example.
  Context `{heapGS Σ, chanG Σ}.

  Definition list_rev_prot : iProto Σ :=
    (<! (l : loc) (vs : list val)> MSG #l {{ llist internal_eq l vs }} ;
     <?> MSG #() {{ llist internal_eq l (reverse vs) }} ; END)%proto.

  Lemma list_rev_service_spec c prot :
    {{{ c ↣ (iProto_app (iProto_dual list_rev_prot) prot) }}}
      list_rev_service c
    {{{ RET #(); c ↣ prot }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    wp_lam. wp_recv (l vs) as "Hl". wp_smart_apply (lreverse_spec with "Hl").
    iIntros "Hl". wp_send with "[$Hl]". iApply ("HΦ" with "Hc").
  Qed.

  Lemma llist_split {T} (IT : T → val → iProp Σ) xs l :
    ⊢ llist IT l xs ∗-∗
      ∃ (vs : list val), llist internal_eq l vs ∗ [∗ list] x;v ∈ xs;vs, IT x v.
  Proof.
    iSplit.
    - iIntros "Hl".
      iInduction xs as [|x xs] "IH" forall (l).
      + iExists []. eauto.
      + iDestruct "Hl" as (v lcons) "[HIT [Hlcons Hrec]]".
        iDestruct ("IH" with "Hrec") as (vs) "[Hvs H]".
        iExists (v::vs). iFrame.
        iExists v, lcons. eauto with iFrame.
    - iDestruct 1 as (vs) "[Hvs HIT]".
      iInduction xs as [|x xs] "IH" forall (l vs).
      + by iDestruct (big_sepL2_nil_inv_l with "HIT") as %->.
      + iDestruct (big_sepL2_cons_inv_l with "HIT") as (v vs' ->) "[HIT HITs]".
        iDestruct "Hvs" as (w lcons Heq) "[Hl Hvs]".
        iExists w, lcons. iFrame "Hl".
        iSplitL "HIT".
        { by iEval (rewrite -Heq). }
        iApply ("IH" with "Hvs HITs").
  Qed.

  Definition list_rev_protI {T} (IT : T → val → iProp Σ) : iProto Σ :=
    (<! (l : loc) (xs : list T)> MSG #l {{ llist IT l xs }} ;
     <?> MSG #() {{ llist IT l (reverse xs) }} ; END)%proto.

  Lemma list_rev_subprot {T} (IT : T → val → iProp Σ) :
    ⊢ list_rev_prot ⊑ list_rev_protI IT.
  Proof.
    iIntros (l xs) "Hl".
    iDestruct (llist_split with "Hl") as (vs) "[Hl HIT]".
    iExists l, vs. iFrame "Hl".
    iModIntro. iIntros "Hl".
    iSplitL "Hl HIT".
    { iApply llist_split. rewrite big_sepL2_reverse_2.
      iExists (reverse vs). iFrame "Hl HIT". }
    done.
  Qed.

  Lemma list_rev_client_spec {T} (IT : T → val → iProp Σ) l xs :
    {{{ llist IT l xs }}}
      list_rev_client #l
    {{{ RET #(); llist IT l (reverse xs) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ". wp_lam.
    wp_smart_apply (start_chan_spec (list_rev_prot)%proto); iIntros (c) "Hc".
    - rewrite -(iProto_app_end_r list_rev_prot).
      iApply (list_rev_service_spec with "Hc"). eauto.
    - iDestruct (iProto_pointsto_le _ _ (list_rev_protI IT) with "Hc []") as "Hc".
      { iApply list_rev_subprot. }
      wp_send (l xs) with "[$Hl]". wp_recv as "Hl". by iApply "HΦ".
  Qed.

End list_rev_example.
