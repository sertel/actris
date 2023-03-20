From miniactris Require Export session.
From iris.heap_lang.lib Require Import assert.

Definition new_imp : val :=
  λ: <>,
     let: "c" := new #() in
     (ref "c", ref "c" ).
Definition recv_imp : val :=
  λ: "c" <>,
    let: "r" := recv (!"c") in
    "c" <- (Snd "r");; Fst "r".
Definition send_imp : val := λ: "c" "v",
  "c" <- send (!"c") "v".
Definition close_imp : val :=
  λ: "c" <>, close (!"c");; Free "c".
Definition wait_imp : val :=
  λ: "c" <>, wait (!"c");; Free "c".

Section imp_proofs.
  Context `{!heapGS Σ, !chanG Σ}.

  Notation prot := (prot Σ).

  Definition is_chan_imp ch p : iProp Σ :=
    ∃ (l:loc) ch', ⌜ch = #l⌝ ∗ l ↦ ch' ∗ is_chan ch' p.

  Lemma new_imp_spec p :
    {{{ True }}}
      new_imp #()
    {{{ ch1 ch2, RET (ch1,ch2); is_chan_imp ch1 p ∗ is_chan_imp ch2 (dual p) }}}.
  Proof.
    iIntros (Ψ) "_ HΨ". wp_lam.
    wp_smart_apply new_spec; [done|].
    iIntros (ch) "[Hch1 Hch2]".
    wp_alloc l2 as "Hl2". wp_alloc l1 as "Hl1".
    wp_pures. iApply "HΨ".
    iSplitL "Hch1 Hl1".
    - iModIntro. iExists _, _. iFrame. by iFrame.
    - iModIntro. iExists _, _. iFrame. by iFrame.
  Qed.

  Lemma recv_imp_spec {A} ch (v : A → val) Φ p :
    {{{ is_chan_imp ch (recv_prot v Φ p) }}}
      recv_imp ch #()
    {{{ x, RET v x; is_chan_imp ch (p x) ∗ Φ x }}}.
  Proof.
    iIntros (Ψ) "Hr HΨ". iDestruct "Hr" as (l ch' ->) "[Hl Hch']".
    wp_lam. wp_load. wp_smart_apply (recv_spec with "Hch'").
    iIntros (x ch'') "[Hch'' HΦ]". wp_store. wp_pures.
    iApply "HΨ". iFrame "HΦ". iExists _, _. by iFrame.
  Qed.

  Lemma send_imp_spec {A} x ch (v : A → val) Φ p :
    {{{ is_chan_imp ch (send_prot v Φ p) ∗ ▷ Φ x }}}
      send_imp ch (v x)
    {{{ RET #(); is_chan_imp ch (p x) }}}.
  Proof.
    iIntros (Ψ) "[Hs HΦ] HΨ". iDestruct "Hs" as (l ch' ->) "[Hs Hch']".
    wp_lam. wp_load. wp_smart_apply (send_spec with "[$Hch' $HΦ]").
    iIntros (ch'') "Hch'". wp_store.
    iApply "HΨ". iExists _, _. by iFrame.
  Qed.

  Lemma wait_imp_spec ch :
    {{{ is_chan_imp ch wait_prot }}}
      wait_imp ch #()
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (Ψ) "Hch HΨ". iDestruct "Hch" as (l ch' ->) "[Hs Hch]".
    wp_lam. wp_load. wp_smart_apply (wait_spec with "Hch").
    iIntros "_". wp_free. by iApply "HΨ".
  Qed.

  Lemma close_imp_spec ch :
    {{{ is_chan_imp ch close_prot }}}
      close_imp ch #()
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (Ψ) "Hch HΨ". iDestruct "Hch" as (l ch' ->) "[Hs Hch]".
    wp_lam. wp_load. wp_smart_apply (close_spec with "Hch").
    iIntros "_". wp_free. by iApply "HΨ".
  Qed.

End imp_proofs.

Section imp_examples.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation prot := (prot Σ).

  Definition recv_and_add : val :=
    rec: "go" "c" "l" "n" :=
      if: "n" = #0 then #() else
      "l" <- (recv_imp "c" #()) + !"l";;
      "go" "c" "l" ("n"-#1).

  Definition send_all : val :=
    rec: "go" "c" "n" := 
      if: "n" = #0 then #() else 
        send_imp "c" "n";;
        "go" "c" ("n"-#1).

  Definition prog_imp : val :=
    λ: "<>",
      let: "c" := new_imp #() in
      let: "c1" := Fst "c" in
      let: "c2" := Snd "c" in
      Fork (let: "r" := recv_imp "c2" #() in
            let: "l" := Fst "r" in
            let: "n" := Snd "r" in
            recv_and_add "c2" "l" "n";;               (* For loop *)
            send_imp "c2" #();;
            wait_imp "c2" #());;
      let: "l" := ref #0 in
      send_imp "c1" ("l",#100);;
      send_all "c1" #100%nat;;                       (* For loop *)
      recv_imp "c1" #();;
      close_imp "c1" #();;
      assert: (!"l" = #5050).

  Definition prot_imp_end l (x:Z) : prot :=
    recv_prot (λ (_:unit), #()) (λ _, l ↦ #x)%I (λ _, close_prot).
  
  Fixpoint prot_imp_loop l (x:nat) (p : loc → nat → prot) n : prot :=
    match n with
    | 0 => p l x
    | S n => send_prot (λ (y:nat), #y) (λ _, True)%I
                       (λ y, prot_imp_loop l (x+y) p n)
    end.

  Definition prot_imp : prot :=
    send_prot (λ (ln : loc * nat), PairV #ln.1 #ln.2)
              (λ ln, ln.1 ↦ #0)%I
              (λ ln, prot_imp_loop (ln.1) 0 prot_imp_end (ln.2)).

  Fixpoint sum n :=
    match n with
    | 0 => 0
    | S n => n + sum n
    end.

  Lemma send_all_spec x ch l (p : loc → nat → prot) n :
    {{{ is_chan_imp ch (prot_imp_loop l x p n) }}}
      send_all ch #n
    {{{ RET #(); is_chan_imp ch (p l (x + sum (S n))) }}}.
  Proof.
    iIntros (Φ) "Hch HΦ".
    iInduction n as [|n] "IHn" forall (x)=> /=.
    { wp_rec. wp_pures. iApply "HΦ". rewrite right_id_L. done. }
    wp_rec.
    wp_smart_apply (send_imp_spec (S n) with "[$Hch//]").
    iIntros "Hch".
    wp_pures. replace (S n - 1)%Z with (Z.of_nat n) by lia.
    iApply ("IHn" with "Hch").
    iIntros "!>Hch". iApply "HΦ".
    rewrite !assoc_L.
    by replace (x + S n + n + sum n) with
      (x + S (n + n + sum n)) by lia.
  Qed.

  Lemma recv_and_add_spec (x:nat) ch l (p : loc → nat → prot) n :
    {{{ l ↦ #x ∗ is_chan_imp ch (dual (prot_imp_loop l x p n)) }}}
      recv_and_add ch #l #n
    {{{ (y:nat), RET #(); l ↦ #y ∗ is_chan_imp ch (dual (p l y)) }}}.
  Proof.
    iIntros (Φ) "[Hl Hch] HΦ".
    iInduction n as [|n] "IHn" forall (x)=> /=.
    { wp_rec. wp_pures. iApply "HΦ". by iFrame. }
    wp_rec.
    wp_pures. wp_load.
    wp_smart_apply (recv_imp_spec with "Hch").
    iIntros (?) "[Hch _]"=> /=.
    wp_store. wp_pures.
    replace (S n - 1)%Z with (Z.of_nat n) by lia.
    rewrite -!Nat2Z.inj_add.
    iApply ("IHn" with "Hl [Hch]").
    { by iEval rewrite comm_L. }
    iIntros "!>" (y) "[Hl Hch]". iApply "HΦ". by iFrame.
  Qed.
    
  Lemma prog_imp_spec :
    {{{ True }}}
      prog_imp #()
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_imp_spec prot_imp); [done|].
    iIntros (ch1 ch2) "[Hch1 Hch2]".
    wp_smart_apply (wp_fork with "[Hch2]").
    - iIntros "!>". wp_smart_apply (recv_imp_spec with "Hch2").
      iIntros ([l x]) "[Hch2 Hl]"=> /=.
      wp_smart_apply (recv_and_add_spec with "[Hl Hch2]").
      { iFrame. }
      iIntros (y) "[Hl Hch2]".
      wp_smart_apply (send_imp_spec () with "[$Hch2 Hl//]"). iIntros "Hch2".
      wp_smart_apply (wait_imp_spec with "Hch2"). by iIntros "_".
    - wp_alloc l as "Hl". 
      wp_smart_apply (send_imp_spec (l,100%nat) with "[$Hch1 $Hl]").
      iIntros "Hch1".
      wp_smart_apply (send_all_spec with "Hch1"). iIntros "Hch1".
      wp_smart_apply (recv_imp_spec with "Hch1"). iIntros (_) "[Hch1 Hl]".
      wp_smart_apply (close_imp_spec with "Hch1"). iIntros "_".
      wp_smart_apply wp_assert. wp_load. wp_pures.
      iModIntro. iSplit; [done|]. by iApply "HΦ".
  Qed.

End imp_examples.
