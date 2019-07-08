From stdpp Require Import sorting.
From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From actris.examples Require Import sort.

Definition sort_client : val := λ: "cmp" "xs",
  let: "c" := start_chan sort_service in
  send "c" "cmp";; send "c" "xs";;
  recv "c".

Section sort_client.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  Lemma sort_client_spec {A} (I : A → val → iProp Σ) R
       `{!RelDecision R, !Total R} cmp l (xs : list A) :
    cmp_spec I R cmp -∗
    {{{ llist I l xs }}}
      sort_client cmp #l
    {{{ ys, RET #(); ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗ llist I l ys }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ". wp_lam.
    wp_apply (start_chan_proto_spec N sort_protocol); iIntros (c) "Hc".
    { rewrite -(right_id END%proto _ (iProto_dual _)).
      wp_apply (sort_service_spec with "Hc"); auto. }
    wp_send with "[$Hcmp]".
    wp_send with "[$Hl]".
    wp_recv (ys) as "(Hsorted & Hperm & Hl)".
    wp_pures. iApply "HΦ"; iFrame.
  Qed.
End sort_client.
