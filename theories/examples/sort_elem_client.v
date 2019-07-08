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

  Lemma send_all_spec c p xs' l xs vs :
    {{{ llist l vs ∗ c ↣ sort_elem_head_protocol I R xs' <++> p @ N ∗ [∗ list] x;v ∈ xs;vs, I x v }}}
      send_all c #l
    {{{ RET #(); c ↣ sort_elem_head_protocol I R (xs' ++ xs) <++> p @ N }}}.
  Proof.
    iIntros (Φ) "(Hl & Hc & HI) HΦ".
    iInduction xs as [|x xs] "IH" forall (xs' vs); destruct vs as [|v vs]=>//.
    { wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl"; wp_pures.
      iApply "HΦ". rewrite right_id_L. iFrame. }
    iDestruct "HI" as "[HIxv HI]". wp_lam.
    wp_apply (lisnil_spec with "Hl"); iIntros "Hl". wp_select.
    wp_apply (lpop_spec with "Hl"); iIntros "Hl".
    wp_send with "[$HIxv]". wp_apply ("IH" with "Hl Hc HI"). by rewrite -assoc_L.
  Qed.

  Lemma recv_all_spec c p xs ys' :
    Sorted R ys' →
    {{{ c ↣ sort_elem_tail_protocol I R xs ys' <++> p @ N }}}
      recv_all c
    {{{ l ys ws, RET #l;
        ⌜Sorted R (ys' ++ ys)⌝ ∗ ⌜ys' ++ ys ≡ₚ xs⌝ ∗
        llist l ws ∗ c ↣ p @ N ∗ [∗ list] y;w ∈ ys;ws, I y w
    }}}.
  Proof.
    iIntros (Hsort Φ) "Hc HΦ".
    iLöb as "IH" forall (xs ys' Φ Hsort).
    wp_lam. wp_branch as %_ | %Hperm; wp_pures.
    - wp_recv (y v) as (Htl) "HIxv".
      wp_apply ("IH" with "[] Hc"); first by auto using Sorted_snoc.
      iIntros (l ys ws). rewrite -!assoc_L. iDestruct 1 as (??) "(Hl & Hc & HI)".
      wp_apply (lcons_spec with "Hl"); iIntros "Hl"; wp_pures.
      iApply ("HΦ" $! _ (y :: ys)); simpl; eauto with iFrame.
    - wp_apply (lnil_spec with "[//]"); iIntros (l) "Hl".
      iApply ("HΦ" $! _ [] []); rewrite /= right_id_L; by iFrame.
  Qed.

  Lemma sort_client_spec cmp l vs xs :
    cmp_spec I R cmp -∗
    {{{ llist l vs ∗ [∗ list] x;v ∈ xs;vs, I x v }}}
      sort_elem_client cmp #l
    {{{ k ys ws, RET #k;
        ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗
        llist k ws ∗ [∗ list] y;w ∈ ys;ws, I y w
    }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "[Hl HI] HΦ". wp_lam.
    wp_apply (start_chan_proto_spec N (sort_elem_top_protocol <++> END)%proto);
      iIntros (c) "Hc".
    { wp_apply (sort_elem_service_top_spec N with "Hc"); auto. }
    rewrite /sort_elem_top_protocol.
    wp_send (A I R) with "[$Hcmp]".
    wp_apply (send_all_spec with "[$Hl $HI $Hc]"); iIntros "Hc".
    wp_select.
    wp_apply (recv_all_spec _ _ _ [] with "[$Hc]"); auto.
    iIntros (k ys ws) "/=". iDestruct 1 as (??) "(Hk & _ & HI)".
    iApply "HΦ"; auto with iFrame.
  Qed.
End sort_elem_client.
