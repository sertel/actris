From iris.heap_lang Require Import proofmode notation.
From osiris.channel Require Import branching.

Definition branch_example b : expr :=
  (let: "c" := new_chan #() in
   select "c" #Left #b;;
   Fork(branch: "c" @ #Right
    left  send "c" #Right #5
    right #());;
   (if: #b then recv "c" #Left else #()))%E.

Section BranchingExampleProofs.
  Context `{!heapG Σ, !logrelG val Σ}.

  Lemma branch_proof b :
    {{{ True }}}
      branch_example b
    {{{ v, RET v; match b with
                  | Left => ⌜v = #5⌝
                  | Right => ⌜v = #()⌝
                  end }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /branch_example.
    wp_apply (new_chan_st_spec nroot ((<?> v @ ⌜v = 5⌝, TEnd) <+> TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]".
    wp_apply (select_st_spec with "Hstl"); iIntros "Hstl".
    wp_pures.
    wp_apply (wp_fork with "[Hstr]").
    - iNext.
      simpl.
      wp_apply (branch_st_spec with "Hstr")=> //;
      iIntros (v) "[[-> Hstr]|[-> Hstr]]".
      + wp_pures.
        wp_apply (send_st_spec (A:=Z) with "[$Hstr //]"); auto.
      + by wp_pures.
    - destruct b.
      + wp_apply (recv_st_spec (A:=Z) with "Hstl");
        iIntros (v) "[Hstl ->]".
        by iApply "HΦ".
      + wp_pures. by iApply "HΦ".
  Qed.
End BranchingExampleProofs.