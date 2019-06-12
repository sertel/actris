From iris.heap_lang Require Import proofmode notation.
From osiris.proto Require Import proto_enc.

Definition seq_example : expr :=
  (let: "c" := new_chan #() in
   send "c" #Left #5;;
   recv "c" #Right)%E.

Definition par_example : expr :=
  (let: "c" := new_chan #() in
   Fork(send "c" #Left #5);;
   recv "c" #Right)%E.

Definition par_2_example : expr :=
  (let: "c" := new_chan #() in
   Fork(let: "v" := recv "c" #Right in send "c" #Right ("v"+#2));;
   send "c" #Left #5;;recv "c" #Left)%E.

Definition heaplet_example : expr :=
  (let: "c" := new_chan #() in
   Fork(send "c" #Left (ref #5));;
   !(recv "c" #Right))%E.

Definition channel_example : expr :=
  (let: "c" := new_chan #() in
   Fork(
       let: "c'" := new_chan #() in
       send "c" #Left ("c'");; send "c'" #Left #5);;
   let: "c'" := recv "c" #Right in
   recv "c'" #Right
  )%E.

Definition bad_seq_example : expr :=
  (let: "c" := new_chan #() in
   let: "v" := recv "c" #Right in
   send "c" #Left #5;; "v")%E.

Definition bad_par_example : expr :=
  (let: "c" := new_chan #() in
   Fork(#());;
   recv "c" #Right)%E.

Definition bad_interleave_example : expr :=
  (let: "c" := new_chan #() in
   let: "c'" := new_chan #() in
   Fork(recv "c" #Right;; send "c'" #Right #5);;
   recv "c'" #Left;; send "c" #Left #5)%E.

Section ExampleProofsEnc.
  Context `{!heapG Σ, !logrelG val Σ}.

  Lemma seq_proof :
    {{{ True }}} seq_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /seq_example.
    wp_apply (new_chan_st_spec nroot (<!> v @ ⌜v = 5⌝, TEnd))=> //;
      iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (send_st_spec (A:=Z) with "[$Hstl //]"); iIntros "Hstl".
    wp_apply (recv_st_spec (A:=Z) with "Hstr").
    iIntros (v) "[Hstr ->]".
    iApply "HΦ".
    eauto.
  Qed.

  Lemma par_2_proof :
    {{{ True }}}
      par_2_example
    {{{ (v:Z), RET #v; ⌜7 ≤ v⌝ }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /par_2_example.
    wp_apply (new_chan_st_spec nroot
      (<!> v @ ⌜5 ≤ v⌝, <?> v' @ ⌜v+2 ≤ v'⌝, TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstr]").
    - iNext.
      wp_apply (recv_st_spec (A:=Z) with "Hstr"); iIntros (v) "[Hstr HP]".
      wp_apply (send_st_spec (A:=Z) with "[$Hstr //]"); iIntros "Hstr".
      eauto.
    - wp_apply (send_st_spec (A:=Z) with "[$Hstl //]"); iIntros "Hstl".
      wp_apply (recv_st_spec (A:=Z) with "Hstl"); iIntros (v) "[Hstl %]".
      iApply "HΦ". iPureIntro. lia.
  Qed.

  Lemma heaplet_proof :
    {{{ True }}} heaplet_example {{{ v l, RET v; ⌜v = #5⌝ ∗ l ↦ v }}}.
  Proof.
    rewrite /heaplet_example.
    iIntros (Φ _) "HΦ".
    wp_apply (new_chan_st_spec nroot (<!> v @ (v ↦ #5), TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext.
      wp_alloc l as "HP".
      wp_apply (send_st_spec (A:=loc) with "[$Hstl HP]")=> //; iIntros "Hstl".
      eauto.
    - wp_apply (recv_st_spec (A:=loc) with "Hstr"); iIntros (v) "[Hstr HP]".
      wp_load.
      iApply "HΦ".
      by iFrame.
  Qed.

  Lemma channel_proof :
    {{{ True }}} channel_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /channel_example.
    wp_apply (new_chan_st_spec nroot
      (<!> v @ (∃ γ, ⟦ v @ Right : <?> v @ ⌜v = 5⌝, TEnd ⟧{nroot,γ}),
               TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext.
      wp_apply (new_chan_st_spec nroot (<!> v @ ⌜v = 5⌝, TEnd))=> //;
        iIntros (c' γ') "[Hstl' Hstr']"=> /=.
      wp_apply (send_st_spec (A:=val) with "[Hstl Hstr']");
        first by eauto 10 with iFrame.
      iIntros "Hstl".
      wp_apply (send_st_spec (A:=Z) with "[$Hstl' //]"); iIntros "Hstl'".
      eauto.
    - wp_apply (recv_st_spec (A:=val) with "Hstr"); iIntros (v) "[Hstr Hstr']".
      iDestruct "Hstr'" as (γ') "Hstr'".
      wp_apply (recv_st_spec (A:=Z) with "Hstr'"); iIntros (v') "[Hstr' <-]".
      by iApply "HΦ".
  Qed.

  Lemma bad_seq_proof :
    {{{ True }}} bad_seq_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /bad_seq_example.
    wp_apply (new_chan_st_spec nroot (<!> v @ ⌜v = 5⌝, TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (recv_st_spec (A:=Z) with "Hstr"); iIntros (v) "[Hstr ->]".
    wp_apply (send_st_spec (A:=Z) with "[$Hstl //]"); iIntros "Hstl".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma bad_par_proof :
    {{{ True }}} bad_par_example {{{ v, RET v; ⌜v = #5⌝ }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /bad_par_example.
    wp_apply (new_chan_st_spec nroot (<!> v @ ⌜v = 5⌝, TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (wp_fork with "[Hstl]").
    - iNext. by wp_finish.
    - wp_apply (recv_st_spec (A:=Z) with "Hstr"); iIntros (v) "[Hstr ->]".
      by iApply "HΦ".
  Qed.

  Lemma bad_interleave_proof :
    {{{ True }}} bad_interleave_example {{{ v, RET v; ⌜v = #()⌝ }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /bad_interleave_example.
    wp_apply (new_chan_st_spec nroot (<!> v @ ⌜v = 5⌝, TEnd))=> //;
    iIntros (c γ) "[Hstl Hstr]"=> /=.
    wp_apply (new_chan_st_spec nroot (<?> v @ ⌜v = 5⌝, TEnd))=> //;
    iIntros (c' γ') "[Hstl' Hstr']"=> /=.
    wp_apply (wp_fork with "[Hstr Hstr']").
    - iNext. wp_apply (recv_st_spec (A:=Z) with "Hstr"); iIntros (v) "[Hstr HP]".
      wp_apply (send_st_spec (A:=Z) with "[$Hstr' //]"). eauto.
    - wp_apply (recv_st_spec (A:=Z) with "[$Hstl' //]"); iIntros (v) "[Hstl' HP]".
      wp_apply (send_st_spec (A:=Z) with "[$Hstl //]"); iIntros "Hstl".
      by iApply "HΦ".
  Qed.
End ExampleProofsEnc.
