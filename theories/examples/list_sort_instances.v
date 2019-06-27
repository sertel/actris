From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel.
From iris.heap_lang Require Import proofmode notation.
From osiris.utils Require Import list.
From osiris.examples Require Import list_sort.

Definition cmpZ : val :=
  λ: "x" "y", "x" ≤ "y".

Section list_sort_instances.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  (* Example: Sort of integers *)
  Definition IZ (x : Z) (v : val) : iProp Σ := ⌜v = #x⌝%I.

  Lemma cmpZ_spec : cmp_spec IZ (≤) cmpZ.
  Proof.
    rewrite /IZ. iIntros (x x' v v' Φ [-> ->]) "!> HΦ".
    wp_lam. wp_pures. by iApply "HΦ".
  Qed.

  Local Arguments val_encode _ _ !_ /.

  Lemma list_sort_client_le_spec l (xs : list Z) :
    {{{ l ↦ val_encode xs }}}
      list_sort_client cmpZ #l
      {{{ ys, RET #(); ⌜Sorted (≤) ys⌝ ∗ ⌜ ys ≡ₚ xs⌝ ∗ l ↦ val_encode ys }}}.
  Proof.
    assert (∀ zs : list Z, val_encode zs = val_encode (LitV ∘ LitInt <$> zs)) as Henc.
    { intros zs. induction zs; f_equal/=; auto with f_equal. }
    iIntros (Φ) "Hl HΦ".
    iApply (list_sort_client_spec N IZ (≤) _ _ (LitV ∘ LitInt <$> xs) xs with "[] [Hl] [HΦ]").
    { iApply cmpZ_spec. }
    { rewrite -Henc. iFrame "Hl".
      iInduction xs as [|x xs] "IH"; csimpl; first by iFrame.
      by iFrame "IH". }
    iIntros "!>" (ys ws) "(?&?&?&HI)".
    iAssert ⌜ ws = (LitV ∘ LitInt) <$> ys ⌝%I with "[HI]" as %->.
    { iInduction ys as [|y ys] "IH" forall (ws);
      destruct ws as [|w ws]; csimpl; try done.
      iDestruct "HI" as "[-> HI2]".
      by iDestruct ("IH" with "HI2") as %->. }
    rewrite -Henc. iApply ("HΦ" $! ys with "[$]").
  Qed.
End list_sort_instances.
