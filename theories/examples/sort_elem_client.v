From stdpp Require Import sorting.
From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From actris.utils Require Import llist compare.
From actris.examples Require Import sort_elem.

Definition send_all : val :=
  rec: "go" "c" "xs" :=
    if: lisnil "xs" then #() else
    send "c" #cont;; send "c" (lpop "xs");; "go" "c" "xs".

Definition recv_all : val :=
  rec: "go" "c" :=
    if: ~recv "c" then lnil #() else
    let: "x" := recv "c" in
    let: "l" := "go" "c" in lcons "x" "l";; "l".

Definition sort_elem_client : val :=
  λ: "cmp" "xs",
    let: "c" := start_chan sort_elem_service_top in
    send "c" "cmp";;
    send_all "c" "xs";;
    send "c" #stop;;
    recv_all "c".

Section sort_elem_client.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).
  Context {A} (I : A → val → iProp Σ) (R : relation A) `{!RelDecision R, !Total R}.

  Lemma send_all_spec c p xs' l xs :
    {{{ llist I l xs ∗ c ↣ sort_elem_head_protocol I R xs' <++> p @ N }}}
      send_all c #l
    {{{ RET #(); c ↣ sort_elem_head_protocol I R (xs' ++ xs) <++> p @ N }}}.
  Proof.
    iIntros (Φ) "[Hl Hc] HΦ".
    iInduction xs as [|x xs] "IH" forall (xs').
    { wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl"; wp_pures.
      iApply "HΦ". rewrite right_id_L. iFrame. }
    wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl". wp_select.
    wp_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
    wp_send with "[$HIx]". wp_apply ("IH" with "Hl Hc"). by rewrite -assoc_L.
  Qed.

  Lemma recv_all_spec c p xs ys' :
    Sorted R ys' →
    {{{ c ↣ sort_elem_tail_protocol I R xs ys' <++> p @ N }}}
      recv_all c
    {{{ l ys, RET #l;
        ⌜Sorted R (ys' ++ ys)⌝ ∗ ⌜ys' ++ ys ≡ₚ xs⌝ ∗ llist I l ys ∗ c ↣ p @ N
    }}}.
  Proof.
    iIntros (Hsort Φ) "Hc HΦ".
    iLöb as "IH" forall (xs ys' Φ Hsort).
    wp_lam. wp_branch as %_ | %Hperm; wp_pures.
    - wp_recv (y v) as (Htl) "HIx".
      wp_apply ("IH" with "[] Hc"); first by auto using Sorted_snoc.
      iIntros (l ys). rewrite -!assoc_L. iDestruct 1 as (??) "[Hl Hc]".
      wp_apply (lcons_spec with "[$Hl $HIx]"); iIntros "Hl"; wp_pures.
      iApply ("HΦ" with "[$Hl $Hc]"); simpl; eauto.
    - wp_apply (lnil_spec with "[//]"); iIntros (l) "Hl".
      iApply ("HΦ" $! _ []); rewrite /= right_id_L; by iFrame.
  Qed.

  Lemma sort_client_spec cmp l xs :
    cmp_spec I R cmp -∗
    {{{ llist I l xs }}}
      sort_elem_client cmp #l
    {{{ k ys, RET #k; ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗ llist I k ys }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ". wp_lam.
    wp_apply (start_chan_proto_spec N (sort_elem_top_protocol <++> END)%proto);
      iIntros (c) "Hc".
    { wp_apply (sort_elem_service_top_spec N with "Hc"); auto. }
    rewrite /sort_elem_top_protocol.
    wp_send (A I R) with "[$Hcmp]".
    wp_apply (send_all_spec with "[$Hl $Hc]"); iIntros "Hc".
    wp_select.
    wp_apply (recv_all_spec with "Hc"); auto.
    iIntros (k ys) "/=". iDestruct 1 as (??) "[Hk _]".
    iApply "HΦ"; auto with iFrame.
  Qed.
End sort_elem_client.
