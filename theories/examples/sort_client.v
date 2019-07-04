From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From osiris.utils Require Import list compare.
From osiris.examples Require Import sort.

Definition sort_client : val := λ: "cmp" "xs",
  let: "c" := start_chan sort_service in
  send "c" "cmp";; send "c" "xs";;
  recv "c".

Section sort_client.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  Lemma sort_client_spec {A} (I : A → val → iProp Σ) R
       `{!RelDecision R, !Total R} cmp l (vs : list val) (xs : list A) :
    cmp_spec I R cmp -∗
    {{{ l ↦ llist vs ∗ [∗ list] x;v ∈ xs;vs, I x v }}}
      sort_client cmp #l
    {{{ ys ws, RET #(); ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗
               l ↦ llist ws ∗ [∗ list] y;w ∈ ys;ws, I y w }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ". wp_lam.
    wp_apply (start_chan_proto_spec N sort_protocol); iIntros (c) "Hc".
    { rewrite -(right_id END%proto _ (iProto_dual _)).
      wp_apply (sort_service_spec with "Hc"); auto. }
    wp_send with "[$Hcmp]".
    wp_send with "[$Hl]".
    wp_recv (ys ws) as "(Hsorted & Hperm & Hl & HI)".
    wp_pures. iApply "HΦ"; iFrame.
  Qed.

  Lemma sort_client_Zle_spec l (xs : list Z) :
    {{{ l ↦ llist (LitV ∘ LitInt <$> xs) }}}
      sort_client cmpZ #l
    {{{ ys, RET #(); ⌜Sorted (≤) ys⌝ ∗ ⌜ ys ≡ₚ xs⌝ ∗ l ↦ llist (LitV ∘ LitInt <$> ys) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    iApply (sort_client_spec IZ (≤) _ _ (LitV ∘ LitInt <$> xs) xs with "[] [Hl] [HΦ]").
    { iApply cmpZ_spec. }
    { iFrame "Hl". iInduction xs as [|x xs] "IH"; csimpl; by iFrame "#". }
    iIntros "!>" (ys ws) "(?&?&?&HI)".
    iAssert ⌜ ws = (LitV ∘ LitInt) <$> ys ⌝%I with "[HI]" as %->.
    { iInduction ys as [|y ys] "IH" forall (ws);
        destruct ws as [|w ws]; csimpl; try done.
      iDestruct "HI" as "[-> HI2]".
      by iDestruct ("IH" with "HI2") as %->. }
    iApply ("HΦ" $! ys with "[$]").
  Qed.
End sort_client.
