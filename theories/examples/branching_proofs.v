From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From iris.base_logic Require Import invariants.
From osiris.typing Require Import side stype.
From osiris.encodings Require Import branching.
From osiris.examples Require Import branching_examples.

Section BranchingExampleProofs.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Lemma branch_proof b :
    {{{ True }}}
      branch_example b
    {{{ v, RET v; match b with
                  | Left => ⌜v = #5⌝
                  | Right => ⌜v = #()⌝
                  end }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /branch_example.
    wp_apply (new_chan_st_spec N
      ((<?> v @ ⌜v = 5⌝, TEnd) <+> (TEnd)))=> //;
    iIntros (c γ) "[Hstl Hstr]".
    wp_apply (select_st_spec with "Hstl");
    iIntros "Hstl".
    wp_pures.
    wp_apply (wp_fork with "[Hstr]").
    - iNext.
      simpl.
      wp_apply (branch_st_spec with "Hstr")=> //;
      iIntros (v) "[Hstr | Hstr]"; iDestruct "Hstr" as (->) "Hstr".
      + wp_pures. 
        wp_apply (send_st_spec N Z with "[$Hstr //]").
        iIntros "Hstr". done.
      + wp_pures. done.
    - destruct b.
      + wp_apply (recv_st_spec N Z with "Hstl");
        iIntros (v) "[Hstl HP]".
        iDestruct "HP" as %->.
        by iApply "HΦ".
      + wp_pures. by iApply "HΦ".
  Qed.

End BranchingExampleProofs.