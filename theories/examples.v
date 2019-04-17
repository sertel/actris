From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From osiris Require Import typing channel logrel.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.

Section Examples.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG Σ}.

  Definition seq_example : expr :=
    (let: "c" := new_chan #() in
     send "c" #Left #5;;
     recv "c" #Right)%E.

  Notation "⟦ c @ s : sτ ⟧{ γ }" := (interp_st N γ sτ c s)
    (at level 10, s at next level, sτ at next level, γ at next level,
     format "⟦  c  @  s  :  sτ  ⟧{ γ }").

  Lemma seq_proof :
    {{{ True }}} seq_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /seq_example.
    wp_bind (new_chan _).
    wp_apply (new_chan_st_spec N (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_pures.
    wp_bind (send _ _ _).
    wp_apply (send_st_spec N with "[Hstl]"). by iFrame.
    iIntros "Hstl".
    wp_pures.
    wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
    iIntros (v) "[Hstr HP]".
    by iApply "HΦ".
  Qed.

  Definition par_example : expr :=
    (let: "c" := new_chan #() in
     Fork(send "c" #Left #5);;
     recv "c" #Right)%E.

  Lemma par_proof :
    {{{ True }}} par_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /par_example.
    wp_bind (new_chan _).
    wp_apply (new_chan_st_spec N (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_pures.
    wp_bind (Fork _).
    wp_apply (wp_fork with "[Hstl]").
    - iNext. wp_apply (send_st_spec N with "[Hstl]"). by iFrame. eauto.
    - wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
      iIntros (v) "[Hstr HP]". by iApply "HΦ".
  Qed.

  Definition par_2_example : expr :=
    (let: "c" := new_chan #() in
     Fork(let: "v" := recv "c" #Right in send "c" #Right ("v"+#2));;
     send "c" #Left #5;;recv "c" #Left)%E.

  Lemma par_2_proof :
    {{{ True }}}
      par_2_example
    {{{ v, RET v; ∃ w, ⌜v = LitV $ LitInt $ w ∧ w >= 7⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /par_2_example.
    wp_bind (new_chan _).
    wp_apply (new_chan_st_spec N
      (TSR Send
           (λ v, ⌜v = #5⌝%I)
           (λ v, TSR Receive
                     (λ v',
                      (∃ w, ⌜v = LitV $ LitInt $ w⌝ ∧
                       ∃ w', ⌜v' = LitV $ LitInt $ w' ∧ w' >= w+2⌝)%I)
                     (λ v', TEnd))))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_pures.
    wp_bind (Fork _).
    wp_apply (wp_fork with "[Hstr]").
    - iNext.
      wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
      iIntros (v) "[Hstr HP]".
      wp_pures.
      iDestruct "HP" as %->.
      wp_apply (send_st_spec N with "[Hstr]"). iFrame.
      iExists _. iSplit=> //.
      iExists _. iSplit=> //.
      eauto.
    - wp_apply (send_st_spec _ with "[Hstl]"). by iFrame.
      iIntros "Hstl".
      wp_apply (recv_st_spec _ with "[Hstl]"). by iFrame.
      iIntros (v) "[Hstl HP]".
      iApply "HΦ".
      iDestruct "HP" as %[w [HP [w' [HQ HQ']]]].
      iExists _.
      iSplit=> //. iPureIntro.
      inversion HP. rewrite -H1 in HQ'.
      eauto.
  Qed.

End Examples.