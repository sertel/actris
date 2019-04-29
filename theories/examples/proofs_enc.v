From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.
From osiris.encodings Require Import stype_enc.
From osiris.examples Require Import examples.

Section ExampleProofsEnc.
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
    wp_apply (new_chan_st_spec N
             (TSend (λ v, ⌜v = 5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (send_st_spec N Z with "[$Hstl //]");
    iIntros "Hstl".
    wp_apply (recv_st_spec N Z with "[Hstr]"). iApply "Hstr".
    iIntros (v) "[Hstr HP]".
    iApply "HΦ".
    iDestruct "HP" as %->.    
    eauto.
  Qed.

  Lemma par_2_proof :
    {{{ True }}}
      par_2_example
    {{{ (v:Z), RET #v; ⌜7 ≤ v⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /par_2_example.
    wp_apply (new_chan_st_spec N
      (TSend
        (λ v:Z, ⌜5 ≤ v⌝%I)
        (λ v:Z, TReceive
                  (λ v':Z, ⌜v+2 ≤ v'⌝%I)
                  (λ v':Z, TEnd))))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstr]").
    - iNext.
      wp_apply (recv_st_spec N Z with "Hstr");
      iIntros (v) "[Hstr HP]".
      wp_apply (send_st_spec N Z with "[$Hstr //]");
      iIntros "Hstr".
      eauto.
    - wp_apply (send_st_spec N Z with "[$Hstl //]");
      iIntros "Hstl".
      wp_apply (recv_st_spec N Z with "Hstl");
      iIntros (v) "[Hstl HP]".
      iApply "HΦ".
      iDestruct "HP" as %HP.
      iPureIntro. lia.
  Qed.

  Lemma heaplet_proof :
    {{{ True }}} heaplet_example {{{ v l, RET v; ⌜v = #5⌝ ∗ l ↦ v }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /heaplet_example.
    wp_apply (new_chan_st_spec N
      (TSend (λ v, (v ↦ #5)%I)
             (λ v, TEnd)))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext.
      wp_alloc l as "HP".
      wp_apply (send_st_spec N loc with "[$Hstl HP]")=> //;
      iIntros "Hstl".
      eauto.
    - wp_apply (recv_st_spec N loc with "Hstr");
      iIntros (v) "[Hstr HP]".
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
      (TSend (λ v, ∃ γ, ⟦ v @ Right :
        (TReceive
          (λ v, ⌜v = 5⌝)
          (λ _, TEnd)) ⟧{γ})%I
      (λ v, TEnd)))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext.
      wp_apply (new_chan_st_spec N
        (TSend (λ v, ⌜v = 5⌝%I) (λ v, TEnd)))=> //;
      iIntros (c' γ') "[Hstl' Hstr']"=> /=.
      wp_apply (send_st_spec N val with "[Hstl Hstr']");
        first by eauto 10 with iFrame.
      iIntros "Hstl".
      wp_apply (send_st_spec N Z with "[$Hstl' //]");
      iIntros "Hstl'".
      eauto.
    - wp_apply (recv_st_spec N val with "Hstr");
      iIntros (v) "[Hstr Hstr']".
      iDestruct "Hstr'" as (γ') "Hstr'".
      wp_apply (recv_st_spec N Z with "Hstr'");
      iIntros (v') "[Hstr' HP]".
      iDestruct "HP" as %<-.
      by iApply "HΦ".
  Qed.

  Lemma bad_seq_proof :
    {{{ True }}} bad_seq_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_seq_example.
    wp_apply (new_chan_st_spec N
               (TSend (λ v, ⌜v = 5⌝%I) (λ v, TEnd)))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (recv_st_spec _ with "Hstr");
    iIntros (v) "[Hstr HP]".
    wp_apply (send_st_spec N with "[$Hstl //]");
    iIntros "Hstl".
    iDestruct "HP" as %->.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma bad_par_proof :
    {{{ True }}} bad_par_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_par_example.
    wp_apply (new_chan_st_spec N
               (TSend (λ v, ⌜v = 5⌝%I) (λ v, TEnd)))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext. by wp_finish.
    - wp_apply (recv_st_spec _ with "Hstr");
      iIntros (v) "[Hstr HP]".
      iDestruct "HP" as %->.
      by iApply "HΦ".
  Qed.

  Lemma bad_interleave_proof :
    {{{ True }}} bad_interleave_example {{{ v, RET v; ⌜v = #()⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_interleave_example.
    wp_apply (new_chan_st_spec N (TSend (λ v, ⌜v = 5⌝%I) (λ v, TEnd)))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (new_chan_st_spec N
               (TReceive (λ v, ⌜v = 5⌝%I) (λ v, TEnd)))=> //;
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

End ExampleProofsEnc.