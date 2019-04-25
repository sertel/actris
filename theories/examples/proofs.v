From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From iris.base_logic Require Import invariants.
From osiris.typing Require Import side stype.
From osiris.encodings Require Import stype.
From osiris.examples Require Import examples.

Section ExampleProofs.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Notation "⟦ c @ s : sτ ⟧{ γ }" := (interp_st N γ sτ c s)
    (at level 10, s at next level, sτ at next level, γ at next level,
     format "⟦  c  @  s  :  sτ  ⟧{ γ }").

  Lemma seq_proof :
    {{{ True }}} seq_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /seq_example.
    wp_apply (new_chan_st_spec N (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (send_st_spec N with "[$Hstl //]").
    iIntros "Hstl".
    wp_apply (recv_st_spec _ with "Hstr").
    iIntros (v) "[Hstr HP]".
    by iApply "HΦ".
  Qed.

  Lemma par_proof :
    {{{ True }}} par_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /par_example.
    wp_apply (new_chan_st_spec N (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext. wp_apply (send_st_spec N with "[Hstl]"). by iFrame. eauto.
    - wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
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
      (TSR Send
           (λ v, ⌜v = #5⌝%I)
           (λ v, TSR Receive
                     (λ v',
                      (∃ w, ⌜v = LitV $ LitInt $ w⌝ ∧
                       ∃ w', ⌜v' = LitV $ LitInt $ w' ∧ w' >= w+2⌝)%I)
                     (λ v', TEnd))))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstr]").
    - iNext.
      wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
      iIntros (v) "[Hstr HP]".
      iDestruct "HP" as %->.
      wp_apply (send_st_spec N with "[Hstr]"). iFrame; eauto 10 with iFrame.
      eauto.
    - wp_apply (send_st_spec _ with "[Hstl]"). by iFrame.
      iIntros "Hstl".
      wp_apply (recv_st_spec _ with "[Hstl]"). by iFrame.
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
      (TSR Send (λ v, (∃ l, ⌜v = LitV $ LitLoc $ l⌝ ∧ (l ↦ #5))%I)
                (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext.
      wp_apply (wp_alloc)=> //.
      iIntros (l) "HP".
      wp_apply (send_st_spec N with "[Hstl HP]"). eauto 10 with iFrame.
      eauto.
    - wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
      iIntros (v) "[Hstr HP]".
      iDestruct "HP" as (l ->) "HP".
      wp_load.
      iApply "HΦ".
      iFrame. eauto.
  Qed.

  Lemma channel_proof :
    {{{ True }}} channel_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /channel_example.
    wp_apply (new_chan_st_spec N
      (TSR Send (λ v, ∃ γ, ⟦ v @ Right :
        (TSR Receive
             (λ v : val, ⌜v = #5⌝)
             (λ _ : val, TEnd)) ⟧{γ})%I
                (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_pures.
    wp_apply (wp_fork with "[Hstl]").
    - iNext.
      wp_apply (new_chan_st_spec N
        (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
      iIntros (c' γ') "[Hstl' Hstr']"=> /=.
      wp_apply (send_st_spec N with "[Hstl Hstr']").
      iFrame. iExists γ'. iFrame.
      iIntros "Hstl".
      wp_apply (send_st_spec N with "[Hstl']").
      iFrame. eauto. eauto.
    - wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
      iIntros (v) "[Hstr Hstr']".
      iDestruct "Hstr'" as (γ') "Hstr'".
      wp_apply (recv_st_spec _ with "[Hstr']").
      iApply "Hstr'".
      iIntros (v') "[Hstr' HP]".
      by iApply "HΦ".
  Qed.

  Lemma bad_seq_proof :
    {{{ True }}} bad_seq_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_seq_example.
    wp_apply (new_chan_st_spec N
               (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (recv_st_spec _ with "Hstr").
    iIntros (v) "[Hstr HP]".
    wp_apply (send_st_spec N with "[Hstl]"). by iFrame.
    iIntros "Hstl".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma bad_par_proof :
    {{{ True }}} bad_par_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_par_example.
    wp_apply (new_chan_st_spec N
               (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext. wp_finish. eauto.
    - wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
      iIntros (v) "[Hstr HP]". by iApply "HΦ".
  Qed.

  Lemma bad_interleave_proof :
    {{{ True }}} bad_interleave_example {{{ v, RET v; ⌜v = #()⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_interleave_example.
    wp_apply (new_chan_st_spec N (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (new_chan_st_spec N
               (TSR Receive (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c' γ') "[Hstl' Hstr']"=> /=.
    wp_apply (wp_fork with "[Hstr Hstr']").
    - iNext. wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
      iIntros (v) "[Hstr HP]".
      wp_apply (send_st_spec _ with "[Hstr']"). iFrame. eauto.
      eauto.
    - wp_apply (recv_st_spec _ with "[Hstl']"). by iFrame.
      iIntros (v) "[Hstl' HP]".
      wp_apply (send_st_spec _ with "[Hstl]"). iFrame. eauto.
      iIntros "Hstl".
      by iApply "HΦ".
  Qed.

End ExampleProofs.