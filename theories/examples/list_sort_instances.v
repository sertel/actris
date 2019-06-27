From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel.
From iris.heap_lang Require Import proofmode notation.
From osiris.utils Require Import list.
From osiris.examples Require Import list_sort.

Section list_sort_instances.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  (* Example: Sort of integers *)
  Definition IZ (x : Z) (v : val) : iProp Σ :=
    ⌜∃ w, v = LitV $ LitInt w ∧ x = w⌝%I.

  Definition compareZ : val :=
    λ: "x" "y", "x" ≤ "y".

  Lemma compareZ_spec : cmp_spec IZ (≤) compareZ.
  Proof.
    iIntros (x x' v v' Φ) "!>".
    iIntros ([[w [-> ->]] [w' [-> ->]]]) "HΦ".
    wp_lam. wp_pures. iApply "HΦ". eauto 10 with iFrame.
  Qed.
  
  Local Arguments val_encode _ _ !_ /.

  Lemma list_sort_client_le_spec l (xs : list Z) :
    {{{ l ↦ val_encode xs }}}
      list_sort_client compareZ #l
      {{{ ys, RET #(); ⌜Sorted (≤) ys⌝ ∗ ⌜ ys ≡ₚ xs⌝ ∗ l ↦ val_encode ys }}}.
  Proof.
    assert (∀ zs : list Z, val_encode zs = val_encode (LitV ∘ LitInt <$> zs)) as Henc.
    { intros zs. induction zs; f_equal/=; auto with f_equal. }
    iIntros (Φ) "Hl HΦ".
    iApply (list_sort_client_spec N IZ (≤) _ _ (LitV ∘ LitInt <$> xs) xs with "[] [Hl] [HΦ]").
    { iApply compareZ_spec. }
    { rewrite -Henc. iFrame "Hl".
      iInduction xs as [|x xs] "IH"; csimpl; first by iFrame.
      iFrame "IH". by iExists x. }
    iIntros "!>" (ys ws) "(?&?&?&HI)".
    iAssert ⌜ ws = (LitV ∘ LitInt) <$> ys ⌝%I with "[HI]" as %->.
    { iInduction ys as [|y ys] "IH" forall (ws);
      destruct ws as [|w ws]; csimpl; try done.
      iDestruct "HI" as "[HI1 HI2]"; iDestruct "HI1" as %(?&->&->).
      by iDestruct ("IH" with "HI2") as %->. }
    rewrite -Henc. iApply ("HΦ" $! ys with "[$]").
  Qed.

End list_sort_instances.
