(** This file contains two proofs that the program

  λ c, (recv c ||| recv c)

can be assigned the semantic type

  chan (?int.?int.end) ⊸ (int * int)

This cannot be shown directly using the semantic typing rules, and therefore
manual proof is used to show that the program is semantically well-typed. This
demonstrates the extensibility of the type system.

The first proof uses a bare minimum weakest precondition for the program,
while the second proof uses a weakest precondition for full functional correctness.
*)
From iris.algebra Require Import frac auth excl updates.
From iris.heap_lang.lib Require Export par spin_lock.
From actris.channel Require Import proofmode.
From actris.logrel Require Export term_typing_judgment session_types.

Local Existing Instance spin_lock.

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
  Context `{!heapGS Σ, !chanG Σ, !spawnG Σ, !lockG Σ}.
  Context `{!inG Σ fracR}.

  Definition prog_prot : iProto Σ :=
    (<? (x : Z)> MSG #x; <? (y : Z)> MSG #y; END)%proto.

  Definition chan_inv (c : val) (γ : gname) : iProp Σ :=
    c ↣ prog_prot ∨
     (own γ (1/2)%Qp ∗ c ↣ <? (x : Z)> MSG #x; END) ∨
     (own γ 1%Qp ∗ c ↣ END).

  Lemma wp_prog c :
    {{{ ▷ c ↣ prog_prot }}}
      prog c
    {{{ (k1 k2 : Z), RET (#k1, #k2); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    rewrite /prog.
    iMod (own_alloc 1%Qp) as (γ) "[Hcredit1 Hcredit2]"; [done|].
    (* Create lock *)
    wp_smart_apply (newlock_spec (chan_inv c γ) with "[Hc]").
    { iLeft. iFrame "Hc". }
    iIntros (lk γlk) "#Hlock".
    wp_pures.
    (* Fork into two threads *)
    wp_smart_apply (wp_par (λ v, ∃ k : Z, ⌜v = #k⌝)%I (λ v, ∃ k : Z, ⌜v = #k⌝)%I
                with "[Hcredit1] [Hcredit2]").
    - (* Acquire lock *)
      wp_smart_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[Hc|[Hc|Hc]]".
      + wp_recv (x1) as "_". wp_pures.
        wp_smart_apply (release_spec with "[Hlocked Hcredit1 Hc]").
        { iFrame "Hlock Hlocked". iRight. iLeft. iFrame "Hcredit1 Hc". }
        iIntros "_". wp_pures.
        eauto.
      + iDestruct "Hc" as "[Hcredit2 Hc]".
        wp_recv (x1) as "_". wp_pures.
        iCombine "Hcredit1 Hcredit2" as "Hcredit".
        wp_smart_apply (release_spec with "[Hlocked Hcredit Hc]").
        { iFrame "Hlock Hlocked". iRight. iRight. iFrame "Hcredit Hc". }
        iIntros "_". wp_pures.
        eauto.
      + iDestruct "Hc" as "[Hcredit2 Hc]".
        by iCombine "Hcredit1 Hcredit2" gives %[].
    - (* Acquire lock *)
      wp_smart_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[Hc|[Hc|Hc]]".
      + wp_recv (x1) as "_". wp_pures.
        wp_smart_apply (release_spec with "[Hlocked Hcredit2 Hc]").
        { iFrame "Hlock Hlocked". iRight. iLeft. iFrame "Hcredit2 Hc". }
        iIntros "_". wp_pures.
        eauto.
      + iDestruct "Hc" as "[Hcredit1 Hc]".
        wp_recv (x1) as "Hx1". wp_pures.
        iCombine "Hcredit1 Hcredit2" as "Hcredit".
        wp_smart_apply (release_spec with "[Hlocked Hcredit Hc]").
        { iFrame "Hlock Hlocked". iRight. iRight. iFrame "Hcredit Hc". }
        iIntros "_". wp_pures.
        eauto.
      + iDestruct "Hc" as "[Hcredit1 Hc]".
        by iCombine "Hcredit1 Hcredit2" gives %[].
    - iIntros (?? [[x1 ->] [x2 ->]]) "!>". by iApply "HΦ".
  Qed.

  Lemma prog_typed :
    [] ⊨ prog : chan (<??> TY lty_int; <??> TY lty_int; END) ⊸ lty_int * lty_int.
  Proof.
    iIntros (vs) "!> HΓ /=".
    iApply wp_value.
    iFrame "HΓ".
    iIntros (c) "Hc".
    iApply (wp_prog with "[Hc]").
    { iApply (iProto_pointsto_le _ (lsty_car (<??> TY lty_int; <??> TY lty_int; END)) with "Hc").
      iIntros "!> !>" (v1). iDestruct 1 as %[x1 ->]. iExists x1.
      iIntros "!>" (v2). iDestruct 1 as %[x2 ->]. iExists x2. auto. }
    iIntros "!>" (k1 k2 _).
    iExists _, _. iSplit; first done. eauto.
  Qed.

End double.

Section double_fc.
  Context `{!heapGS Σ, !chanG Σ, !spawnG Σ, !lockG Σ}.
  Context `{!inG Σ (exclR unitO), inG Σ (prodR fracR (agreeR (optionO valO)))}.

  Definition prog_prot_fc (P : val → val → iProp Σ) : iProto Σ :=
    (<? (v1 : val)> MSG v1; <? (v2 : val)> MSG v2 {{ P v1 v2 }}; END)%proto.

  Definition chan_inv_fc (γ γ1 γ2 : gname) (P : val → val → iProp Σ) (c : val) :
    iProp Σ :=
    own γ (Excl ()) ∗ c ↣ prog_prot_fc P ∨
     (∃ b v1,
       own (if b : bool then γ1 else γ2) (3/4, to_agree (Some v1))%Qp ∗
       c ↣ <? (v2 : val)> MSG v2 {{ P v1 v2 }}; END) ∨
     (∃ v1 v2,
       own γ1 (1/4, to_agree (Some v1))%Qp ∗
       own γ2 (1/4, to_agree (Some v2))%Qp).

  Lemma wp_prog_fc P c :
    {{{ ▷ c ↣ prog_prot_fc P }}}
      prog c
    {{{ v1 v2, RET (v1, v2); P v1 v2 ∨ P v2 v1 }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". rewrite /prog.
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; [done|].
    iMod (own_alloc (1, to_agree None)%Qp) as (γ1) "Hγ1"; [done|].
    iMod (own_alloc (1, to_agree None)%Qp) as (γ2) "Hγ2"; [done|].
    (* Create lock *)
    wp_smart_apply (newlock_spec (chan_inv_fc γ γ1 γ2 P c) with "[Hγ Hc]").
    { iLeft. by iFrame. }
    iIntros (lk γlk) "#Hlock". wp_pures.
    (* Fork into two threads *)
    wp_smart_apply (wp_par
      (λ v1, own γ1 (1/4, to_agree (Some v1))%Qp ∗ own γ (Excl ()) ∨
        (∃ v2, own γ1 (3/4, to_agree (Some v1))%Qp ∗
               own γ2 (1/2, to_agree (Some v2))%Qp ∗ P v2 v1))%I
      (λ v2, own γ2 (1/4, to_agree (Some v2))%Qp ∗ own γ (Excl ()) ∨
        (∃ v1, own γ2 (3/4, to_agree (Some v2))%Qp ∗
               own γ1 (1/2, to_agree (Some v1))%Qp ∗ P v1 v2))%I with "[Hγ1] [Hγ2]").
    - (* Acquire lock *)
      wp_smart_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[[Hγ Hc]|[Hc|Hc]]".
      + wp_recv (v) as "_". wp_pures.
        iMod (own_update _ _ ((3/4 ⋅ 1/4), to_agree (Some v))%Qp with "Hγ1")
          as "[Hγ1a Hγ1b]"; [by apply cmra_update_exclusive|].
        wp_smart_apply (release_spec with "[$Hlock $Hlocked Hγ1a Hc]").
        { iRight. iLeft. iExists true, v. iFrame. }
        iIntros "_". wp_pures. iLeft. by iFrame.
      + iDestruct "Hc" as ([] v) "[Hγ2 Hc]".
        { by iCombine "Hγ1 Hγ2" gives %[]. }
        wp_recv (v') as "HP". wp_pures.
        iMod (own_update _ _ ((1/4 ⋅ 3/4), to_agree (Some v'))%Qp with "Hγ1")
          as "[Hγ1a Hγ1b]"; [by apply cmra_update_exclusive|].
        rewrite {1}(_ : 3/4 = 1/4 + 1/2)%Qp; last (by apply: bool_decide_unpack).
        iDestruct "Hγ2" as "[Hγ2a Hγ2b]".
        wp_smart_apply (release_spec with "[$Hlock $Hlocked Hγ1a Hγ2a Hc]").
        { do 2 iRight. iExists v', v. iFrame. }
        iIntros "_". wp_pures. iRight. iExists v. by iFrame.
      + iDestruct "Hc" as (v v') "[Hγ1' _]".
        by iCombine "Hγ1 Hγ1'" gives %[].
    - (* Acquire lock *)
      wp_smart_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[[Hγ Hc]|[Hc|Hc]]".
      + wp_recv (v) as "_". wp_pures.
        iMod (own_update _ _ ((3/4 ⋅ 1/4), to_agree (Some v))%Qp with "Hγ2")
          as "[Hγ2a Hγ2b]"; [by apply cmra_update_exclusive|].
        wp_smart_apply (release_spec with "[$Hlock $Hlocked Hγ2a Hc]").
        { iRight. iLeft. iExists false, v. iFrame. }
        iIntros "_". wp_pures. iLeft. by iFrame.
      + iDestruct "Hc" as ([] v) "[Hγ1 Hc]"; last first.
        { by iCombine "Hγ1 Hγ2" gives %[]. }
        wp_recv (v') as "HP". wp_pures.
        iMod (own_update _ _ ((1/4 ⋅ 3/4), to_agree (Some v'))%Qp with "Hγ2")
          as "[Hγ2a Hγ2b]"; [by apply cmra_update_exclusive|].
        rewrite {1}(_ : 3/4 = 1/4 + 1/2)%Qp; last (by apply: bool_decide_unpack).
        iDestruct "Hγ1" as "[Hγ1a Hγ1b]".
        wp_smart_apply (release_spec with "[$Hlock $Hlocked Hγ1a Hγ2a Hc]").
        { do 2 iRight. iExists v, v'. iFrame. }
        iIntros "_". wp_pures. iRight. iExists v. by iFrame.
      + iDestruct "Hc" as (v v') "(_ & Hγ2' & _)".
        by iCombine "Hγ2 Hγ2'" gives %[].
    - iIntros (v1 v2) "[[[H1 Hγ]|H1] [[H2 Hγ']|H2]] !>".
      + by iCombine "Hγ Hγ'" gives %[].
      + iDestruct "H2" as (v2') "(_&H1'&HP)".
        iCombine "H1 H1'" gives %[_ [=->]%to_agree_op_inv_L].
        iApply "HΦ"; auto.
      + iDestruct "H1" as (v1') "(_&H2'&HP)".
        iCombine "H2 H2'" gives %[_ [=->]%to_agree_op_inv_L].
        iApply "HΦ"; auto.
      + iDestruct "H1" as (v1') "[H1 _]"; iDestruct "H2" as (v2') "(_&H2&_)".
        by iCombine "H1 H2" gives %[].
  Qed.

  Lemma prog_typed_fc :
    [] ⊨ prog : chan (<??> TY lty_int; <??> TY lty_int; END) ⊸ lty_int * lty_int.
  Proof.
    iIntros (vs) "!> HΓ /=".
    iApply wp_value. iSplitL; last by iApply ctx_ltyped_nil.
    iIntros (c) "Hc".
    iApply (wp_prog_fc (λ v1 v2, ltty_car lty_int v1 ∗ ltty_car lty_int v2)%I with "[Hc]").
    { iApply (iProto_pointsto_le _ (lsty_car (<??> TY lty_int; <??> TY lty_int; END)) with "Hc").
      iIntros "!> !>" (v1). iDestruct 1 as %[x1 ->]. iExists #x1.
      iIntros "!>" (v2). iDestruct 1 as %[x2 ->]. iExists #x2. iSplitL; last done.
      rewrite /ltty_car /=. auto. }
    iIntros "!>" (v1 v2 [[[k1 ->] [k2 ->]]|[[k1 ->] [k2 ->]]]);
      iExists _, _; iSplit; by eauto.
  Qed.

End double_fc.
