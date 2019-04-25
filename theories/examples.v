From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From osiris Require Import typing channel logrel.
From iris.algebra Require Import list auth excl.
From iris.base_logic Require Import invariants.

Section Examples.
  Context `{!heapG Σ} (N : namespace).
  Context `{!logrelG val Σ}.

  Notation "⟦ c @ s : sτ ⟧{ γ }" := (interp_st N γ sτ c s)
    (at level 10, s at next level, sτ at next level, γ at next level,
     format "⟦  c  @  s  :  sτ  ⟧{ γ }").

  Definition seq_example : expr :=
    (let: "c" := new_chan #() in
     send "c" #Left #5;;
     recv "c" #Right)%E.

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

  Definition par_example : expr :=
    (let: "c" := new_chan #() in
     Fork(send "c" #Left #5);;
     recv "c" #Right)%E.

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

  Definition par_2_example : expr :=
    (let: "c" := new_chan #() in
     Fork(let: "v" := recv "c" #Right in send "c" #Right ("v"+#2));;
     send "c" #Left #5;;recv "c" #Left)%E.

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

  Definition heaplet_example : expr :=
    (let: "c" := new_chan #() in
     Fork(send "c" #Left (ref #5));;
     !(recv "c" #Right))%E.

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

  Definition channel_example : expr :=
    (let: "c" := new_chan #() in
     Fork(
         let: "c'" := new_chan #() in
         send "c" #Left ("c'");; send "c'" #Left #5);;
     let: "c'" := recv "c" #Right in
     recv "c'" #Right
    )%E.

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

  Definition bad_seq_example : expr :=
    (let: "c" := new_chan #() in
     let: "v" := recv "c" #Right in
     send "c" #Left #5;; "v")%E.

  Lemma bad_seq_proof :
    {{{ True }}} bad_seq_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_seq_example.
    wp_apply (new_chan_st_spec N (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (recv_st_spec _ with "Hstr").
    iIntros (v) "[Hstr HP]".
    wp_apply (send_st_spec N with "[Hstl]"). by iFrame.
    iIntros "Hstl".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Definition bad_par_example : expr :=
    (let: "c" := new_chan #() in
     Fork(#());;
     recv "c" #Right)%E.

  Lemma bad_par_proof :
    {{{ True }}} bad_par_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_par_example.
    wp_apply (new_chan_st_spec N (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext. wp_finish. eauto.
    - wp_apply (recv_st_spec _ with "[Hstr]"). by iFrame.
      iIntros (v) "[Hstr HP]". by iApply "HΦ".
  Qed.

  Definition bad_interleave_example : expr :=
    (let: "c" := new_chan #() in
     let: "c'" := new_chan #() in
     Fork(recv "c" #Right;; send "c'" #Right #5);;
     recv "c'" #Left;; send "c" #Left #5)%E.

  Lemma bad_interleave_proof :
    {{{ True }}} bad_interleave_example {{{ v, RET v; ⌜v = #()⌝ }}}.
  Proof.
    iIntros (Φ H) "HΦ".
    rewrite /bad_interleave_example.
    wp_apply (new_chan_st_spec N (TSR Send (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (new_chan_st_spec N (TSR Receive (λ v, ⌜v = #5⌝%I) (λ v, TEnd)))=> //.
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
  
End Examples.