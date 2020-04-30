From iris.algebra Require Import frac.
From iris.heap_lang.lib Require Export par spin_lock.
From actris.channel Require Import proofmode.
From actris.logrel Require Export term_typing_judgment session_types.
From actris.logrel Require Import environments.

Definition prog : val := λ: "c",
  let: "lock" := newlock #() in
  (
    acquire "lock";;
    let: "x1" := recv "c" in
    release "lock";;
    "x1"
  ) ||| (
    acquire "lock";;
    let: "x2" := recv "c" in
    release "lock";;
    "x2"
  ).

Section double.
  Context `{heapG Σ, chanG Σ, inG Σ fracR, spawnG Σ}.

  Definition prog_prot : iProto Σ :=
    (<? (x : Z)> MSG #x; <? (y : Z)> MSG #y; END)%proto.

  Definition chan_inv (c : val) (γ : gname) : iProp Σ :=
    (c ↣ prog_prot ∨
     (own γ (1/2)%Qp ∗ c ↣ <? (x : Z)> MSG #x; END) ∨
     (own γ 1%Qp ∗ c ↣ END))%I.

  Lemma wp_prog c :
    {{{ ▷ c ↣ prog_prot }}}
      prog c
    {{{ (k1 k2 : Z), RET (#k1, #k2); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    rewrite /prog.
    iMod (own_alloc 1%Qp) as (γ) "[Hcredit1 Hcredit2]"; [done|].
    (* Create lock *)
    wp_apply (newlock_spec (chan_inv c γ) with "[Hc]").
    { iLeft. iFrame "Hc". }
    iIntros (lk γlk) "#Hlock".
    wp_pures.
    (* Fork into two threads *)
    wp_apply (wp_par (λ v, ∃ k : Z, ⌜v = #k⌝)%I (λ v, ∃ k : Z, ⌜v = #k⌝)%I
                with "[Hcredit1] [Hcredit2]").
    - (* Acquire lock *)
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[Hc|[Hc|Hc]]".
      + wp_recv (x1) as "_". wp_pures.
        wp_apply (release_spec with "[Hlocked Hcredit1 Hc]").
        { iFrame "Hlock Hlocked". iRight. iLeft. iFrame "Hcredit1 Hc". }
        iIntros "_". wp_pures.
        eauto.
      + iDestruct "Hc" as "[Hcredit2 Hc]".
        wp_recv (x1) as "_". wp_pures.
        iCombine "Hcredit1 Hcredit2" as "Hcredit".
        wp_apply (release_spec with "[Hlocked Hcredit Hc]").
        { iFrame "Hlock Hlocked". iRight. iRight. iFrame "Hcredit Hc". }
        iIntros "_". wp_pures.
        eauto.
      + iDestruct "Hc" as "[Hcredit2 Hc]".
        by iDestruct (own_valid_2 with "Hcredit1 Hcredit2") as %[].
    - (* Acquire lock *)
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[Hc|[Hc|Hc]]".
      + wp_recv (x1) as "_". wp_pures.
        wp_apply (release_spec with "[Hlocked Hcredit2 Hc]").
        { iFrame "Hlock Hlocked". iRight. iLeft. iFrame "Hcredit2 Hc". }
        iIntros "_". wp_pures.
        eauto.
      + iDestruct "Hc" as "[Hcredit1 Hc]".
        wp_recv (x1) as "Hx1". wp_pures.
        iCombine "Hcredit1 Hcredit2" as "Hcredit".
        wp_apply (release_spec with "[Hlocked Hcredit Hc]").
        { iFrame "Hlock Hlocked". iRight. iRight. iFrame "Hcredit Hc". }
        iIntros "_". wp_pures.
        eauto.
      + iDestruct "Hc" as "[Hcredit1 Hc]".
        by iDestruct (own_valid_2 with "Hcredit1 Hcredit2") as %[].
    - iIntros (?? [[x1 ->] [x2 ->]]) "!>". wp_pures. by iApply "HΦ".
  Qed.

  Lemma prog_typed :
    ⊢ ∅ ⊨ prog : chan (<??> lty_int; <??> lty_int; END) ⊸ lty_int * lty_int.
  Proof.
    iIntros (vs) "!> HΓ /=".
    iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros (c) "Hc".
    iApply (wp_prog with "[Hc]").
    { iApply (iProto_mapsto_le _ (lsty_car (<??> lty_int; <??> lty_int; END)) with "Hc").
      iIntros "!> !>" (v1). iMod 1 as %[x1 ->]. iExists x1.
      iIntros "!>" (v2). iMod 1 as %[x2 ->]. iExists x2. auto. }
    iIntros "!>" (k1 k2 _).
    iExists _, _. iSplit; first done. eauto.
  Qed.
End double.
