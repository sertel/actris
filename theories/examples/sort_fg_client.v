From stdpp Require Import sorting.
From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From actris.utils Require Import llist compare.
From actris.examples Require Export sort_fg.

Definition send_all : val :=
  rec: "go" "c" "xs" :=
    if: lisnil "xs" then #() else
    send "c" #cont;; send "c" (lpop "xs");; "go" "c" "xs".

Definition recv_all : val :=
  rec: "go" "c" "ys" :=
    if: ~recv "c" then #() else
    let: "x" := recv "c" in
    "go" "c" "ys";; lcons "x" "ys".

Definition sort_client_fg : val := λ: "cmp" "xs",
  let: "c" := start_chan (λ: "c", sort_service_fg "cmp" "c") in
  send_all "c" "xs";;
  send "c" #stop;;
  recv_all "c" "xs".

Section sort_fg_client.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).
  Context {A} (I : A → val → iProp Σ) (R : relation A) `{!RelDecision R, !Total R}.

  Lemma send_all_spec c p xs' l xs :
    {{{ llist I l xs ∗ c ↣ sort_fg_head_protocol I R xs' <++> p @ N }}}
      send_all c #l
    {{{ RET #(); llist I l [] ∗ c ↣ sort_fg_head_protocol I R (xs' ++ xs) <++> p @ N }}}.
  Proof.
    iIntros (Φ) "[Hl Hc] HΦ".
    iInduction xs as [|x xs] "IH" forall (xs').
    { wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl"; wp_pures.
      iApply "HΦ". rewrite right_id_L. iFrame. }
    wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl". wp_select.
    wp_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
    wp_send with "[$HIx]". wp_apply ("IH" with "Hl Hc"). by rewrite -assoc_L.
  Qed.

  Lemma recv_all_spec c p l xs ys' :
    Sorted R ys' →
    {{{ llist I l [] ∗ c ↣ sort_fg_tail_protocol I R xs ys' <++> p @ N }}}
      recv_all c #l
    {{{ ys, RET #();
        ⌜Sorted R (ys' ++ ys)⌝ ∗ ⌜ys' ++ ys ≡ₚ xs⌝ ∗ llist I l ys ∗ c ↣ p @ N
    }}}.
  Proof.
    iIntros (Hsort Φ) "[Hl Hc] HΦ".
    iLöb as "IH" forall (xs ys' Φ Hsort).
    wp_lam. wp_branch as %_ | %Hperm; wp_pures.
    - wp_recv (y v) as (Htl) "HIx".
      wp_apply ("IH" with "[] Hl Hc"); first by auto using Sorted_snoc.
      iIntros (ys). rewrite -!assoc_L. iDestruct 1 as (??) "[Hl Hc]".
      wp_apply (lcons_spec with "[$Hl $HIx]"); iIntros "Hl"; wp_pures.
      iApply ("HΦ" with "[$Hl $Hc]"); simpl; eauto.
    - iApply ("HΦ" $! []); rewrite /= right_id_L; by iFrame.
  Qed.

  Lemma sort_client_fg_spec cmp l xs :
    cmp_spec I R cmp -∗
    {{{ llist I l xs }}}
      sort_client_fg cmp #l
    {{{ ys, RET #(); ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗ llist I l ys }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ". wp_lam.
    wp_apply (start_chan_proto_spec N (sort_fg_protocol I R <++> END)%proto);
      iIntros (c) "Hc".
    { wp_apply (sort_service_fg_spec N with "Hcmp Hc"); auto. }
    wp_apply (send_all_spec with "[$Hl $Hc]"); iIntros "[Hl Hc]".
    wp_select.
    wp_apply (recv_all_spec with "[$Hl $Hc]"); auto.
    iIntros (ys) "/=". iDestruct 1 as (??) "[Hk _]".
    iApply "HΦ"; auto with iFrame.
  Qed.
End sort_fg_client.
