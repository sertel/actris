From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From iris.base_logic Require Import invariants.
From osiris.proto Require Import stype.
From osiris.examples Require Import examples.

Section ExampleProofs.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Lemma seq_proof :
    {{{ True }}} seq_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /seq_example.
    wp_apply (new_chan_st_spec N (<!> v @ ⌜v = #5⌝, TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (send_st_spec N with "[$Hstl //]");
    iIntros "Hstl".
    wp_apply (recv_st_spec _ with "Hstr");
    iIntros (v) "[Hstr HP]".
    by iApply "HΦ".
  Qed.

  Lemma par_proof :
    {{{ True }}} par_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /par_example.
    wp_apply (new_chan_st_spec N (<!> v @ ⌜v = #5⌝, TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext. wp_apply (send_st_spec N with "[$Hstl //]"). eauto.
    - wp_apply (recv_st_spec _ with "[$Hstr //]");
      iIntros (v) "[Hstr HP]". by iApply "HΦ".
  Qed.

  Lemma par_2_proof :
    {{{ True }}}
      par_2_example
    {{{ (v:Z), RET #v; ⌜7 ≤ v⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /par_2_example.
    wp_apply (new_chan_st_spec N
      (<!> v @ ⌜v = #5⌝,
               <?> v' @ (∃ w, ⌜v = LitV $ LitInt $ w⌝ ∧
                         ∃ w', ⌜v' = LitV $ LitInt $ w' ∧ w' >= w+2⌝),
                        TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstr]").
    - iNext.
      wp_apply (recv_st_spec _ with "[$Hstr //]");
      iIntros (v) "[Hstr HP]".
      iDestruct "HP" as %->.
      wp_apply (send_st_spec N with "[Hstr]"); 
        first by iFrame; eauto 10 with iFrame.
      eauto.
    - wp_apply (send_st_spec _ with "[$Hstl //]");
      iIntros "Hstl".
      wp_apply (recv_st_spec _ with "[$Hstl //]");
      iIntros (v) "[Hstl HP]".
      iDestruct "HP" as %[w [HP [w' [-> HQ']]]].
      iApply "HΦ".
      iPureIntro. simplify_eq. lia.
  Qed.

  Lemma heaplet_proof :
    {{{ True }}} heaplet_example {{{ v l, RET v; ⌜v = #5⌝ ∗ l ↦ v }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /heaplet_example.
    wp_apply (new_chan_st_spec N
      (<!> v @ (∃ l, ⌜v = LitV $ LitLoc $ l⌝ ∧ (l ↦ #5)),
               TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext.
      wp_alloc l as "HP".
      wp_apply (send_st_spec N with "[$Hstl HP]"); first by eauto 10 with iFrame.
      eauto.
    - wp_apply (recv_st_spec _ with "[$Hstr]");
      iIntros (v) "[Hstr HP]".
      iDestruct "HP" as (l ->) "HP".
      wp_load.
      iApply "HΦ".
      by iFrame.
  Qed.

  Lemma channel_proof :
    {{{ True }}} channel_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /channel_example.
    wp_apply (new_chan_st_spec N
      (<!> v @ (∃ γ, ⟦ v @ Right : <?> v @ ⌜v = #5⌝, TEnd ⟧{N,γ}),
               TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext.
      wp_apply (new_chan_st_spec N
        (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //;
      iIntros (c' γ') "[Hstl' Hstr']"=> /=.
      wp_apply (send_st_spec N with "[Hstl Hstr']");
        first by eauto 10 with iFrame.
      iIntros "Hstl".
      wp_apply (send_st_spec N with "[$Hstl' //]").
      eauto.
    - wp_apply (recv_st_spec _ with "[$Hstr]");
      iIntros (v) "[Hstr Hstr']".
      iDestruct "Hstr'" as (γ') "Hstr'".
      wp_apply (recv_st_spec _ with "Hstr'");
      iIntros (v') "[Hstr' HP]".
      by iApply "HΦ".
  Qed.

  Lemma bad_seq_proof :
    {{{ True }}} bad_seq_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_seq_example.
    wp_apply (new_chan_st_spec N (<!> v @ ⌜v = #5⌝, TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (recv_st_spec _ with "Hstr");
    iIntros (v) "[Hstr HP]".
    wp_apply (send_st_spec N with "[$Hstl //]").
    iIntros "Hstl".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma bad_par_proof :
    {{{ True }}} bad_par_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_par_example.
    wp_apply (new_chan_st_spec N (<!> v @ ⌜v = #5⌝, TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext. by wp_finish.
    - wp_apply (recv_st_spec _ with "Hstr");
      iIntros (v) "[Hstr HP]". by iApply "HΦ".
  Qed.

  Lemma bad_interleave_proof :
    {{{ True }}} bad_interleave_example {{{ v, RET v; ⌜v = #()⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_interleave_example.
    wp_apply (new_chan_st_spec N (<!> v @ ⌜v = #5⌝, TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (new_chan_st_spec N (<?> v @ ⌜v = #5⌝, TEnd))=> //;
    iIntros (c' γ') "[Hstl' Hstr']"=> /=.
    wp_apply (wp_fork with "[Hstr Hstr']").
    - iNext. wp_apply (recv_st_spec _ with "Hstr");
      iIntros (v) "[Hstr HP]".
      wp_apply (send_st_spec _ with "[$Hstr' //]"). eauto.
    - wp_apply (recv_st_spec _ with "[$Hstl' //]");
      iIntros (v) "[Hstl' HP]".
      wp_apply (send_st_spec _ with "[$Hstl //]");
      iIntros "Hstl".
      by iApply "HΦ".
  Qed.

End ExampleProofs.