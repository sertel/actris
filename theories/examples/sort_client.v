From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel.
From iris.heap_lang Require Import proofmode notation.
From osiris.utils Require Import list compare.
From osiris.examples Require Import sort.

Section sort_client.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  Lemma sort_client_le_spec l (xs : list Z) :
    {{{ l ↦ llist (LitV ∘ LitInt <$> xs) }}}
      sort_client cmpZ #l
    {{{ ys, RET #(); ⌜Sorted (≤) ys⌝ ∗ ⌜ ys ≡ₚ xs⌝ ∗ l ↦ llist (LitV ∘ LitInt <$> ys) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    iApply (sort_client_spec N IZ (≤) _ _ (LitV ∘ LitInt <$> xs) xs with "[] [Hl] [HΦ]").
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
