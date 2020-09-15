(** This file contains a proof that the program

  λ c, (recv c ||| recv c)

can be assigned the semantic type

  chan (?int.?int.end) ⊸ (int * int)

This cannot be shown directly using the semantic typing rules, and therefore
manual proof is used to show that the program is semantically well-typed. This
demonstrates the extensibility of the type system. *)
From iris.algebra Require Import frac auth excl updates.
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
  Context `{!heapG Σ, !chanG Σ, !spawnG Σ}.
  Context `{!inG Σ (exclR unitO), inG Σ (prodR fracR (agreeR (optionO valO)))}.

  Definition prog_prot (P : val → val → iProp Σ) : iProto Σ :=
    (<? (v1 : val)> MSG v1; <? (v2 : val)> MSG v2 {{ P v1 v2 }}; END)%proto.

  Definition chan_inv (γ γ1 γ2 : gname) (P : val → val → iProp Σ) (c : val) : iProp Σ :=
    (own γ (Excl ()) ∗ c ↣ prog_prot P ∨
     (∃ b v1,
       own (if b : bool then γ1 else γ2) (3/4, to_agree (Some v1))%Qp ∗
       c ↣ <? (v2 : val)> MSG v2 {{ P v1 v2 }}; END) ∨
     (∃ v1 v2,
       own γ1 (1/4, to_agree (Some v1))%Qp ∗
       own γ2 (1/4, to_agree (Some v2))%Qp))%I.

  Lemma wp_prog P c :
    {{{ ▷ c ↣ prog_prot P }}}
      prog c
    {{{ v1 v2, RET (v1, v2); P v1 v2 ∨ P v2 v1 }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". rewrite /prog.
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; [done|].
    iMod (own_alloc (1, to_agree None)%Qp) as (γ1) "Hγ1"; [done|].
    iMod (own_alloc (1, to_agree None)%Qp) as (γ2) "Hγ2"; [done|].
    (* Create lock *)
    wp_apply (newlock_spec (chan_inv γ γ1 γ2 P c) with "[Hγ Hc]").
    { iLeft. by iFrame. }
    iIntros (lk γlk) "#Hlock". wp_pures.
    (* Fork into two threads *)
    wp_apply (wp_par
      (λ v1, own γ1 (1/4, to_agree (Some v1))%Qp ∗ own γ (Excl ()) ∨
        (∃ v2, own γ1 (3/4, to_agree (Some v1))%Qp ∗
               own γ2 (1/2, to_agree (Some v2))%Qp ∗ P v2 v1))%I
      (λ v2, own γ2 (1/4, to_agree (Some v2))%Qp ∗ own γ (Excl ()) ∨
        (∃ v1, own γ2 (3/4, to_agree (Some v2))%Qp ∗
               own γ1 (1/2, to_agree (Some v1))%Qp ∗ P v1 v2))%I with "[Hγ1] [Hγ2]").
    - (* Acquire lock *)
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[[Hγ Hc]|[Hc|Hc]]".
      + wp_recv (v) as "_". wp_pures.
        iMod (own_update _ _ ((3/4 ⋅ 1/4), to_agree (Some v))%Qp with "Hγ1")
          as "[Hγ1a Hγ1b]"; [by apply cmra_update_exclusive|].
        wp_apply (release_spec with "[$Hlock $Hlocked Hγ1a Hc]").
        { iRight. iLeft. iExists true, v. iFrame. }
        iIntros "_". wp_pures. iLeft. iFrame.
      + iDestruct "Hc" as ([] v) "[Hγ2 Hc]".
        { by iDestruct (own_valid_2 with "Hγ1 Hγ2") as %[]. }
        wp_recv (v') as "HP". wp_pures.
        iMod (own_update _ _ ((1/4 ⋅ 3/4), to_agree (Some v'))%Qp with "Hγ1")
          as "[Hγ1a Hγ1b]"; [by apply cmra_update_exclusive|].
        rewrite {1}(_ : 3/4 = 1/4 + 1/2)%Qp; last (by apply: bool_decide_unpack).
        iDestruct "Hγ2" as "[Hγ2a Hγ2b]".
        wp_apply (release_spec with "[$Hlock $Hlocked Hγ1a Hγ2a Hc]").
        { do 2 iRight. iExists v', v. iFrame. }
        iIntros "_". wp_pures. iRight. iExists v. iFrame.
      + iDestruct "Hc" as (v v') "[Hγ1' _]".
        by iDestruct (own_valid_2 with "Hγ1 Hγ1'") as %[].
    - (* Acquire lock *)
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[[Hγ Hc]|[Hc|Hc]]".
      + wp_recv (v) as "_". wp_pures.
        iMod (own_update _ _ ((3/4 ⋅ 1/4), to_agree (Some v))%Qp with "Hγ2")
          as "[Hγ2a Hγ2b]"; [by apply cmra_update_exclusive|].
        wp_apply (release_spec with "[$Hlock $Hlocked Hγ2a Hc]").
        { iRight. iLeft. iExists false, v. iFrame. }
        iIntros "_". wp_pures. iLeft. iFrame.
      + iDestruct "Hc" as ([] v) "[Hγ1 Hc]"; last first.
        { by iDestruct (own_valid_2 with "Hγ1 Hγ2") as %[]. }
        wp_recv (v') as "HP". wp_pures.
        iMod (own_update _ _ ((1/4 ⋅ 3/4), to_agree (Some v'))%Qp with "Hγ2")
          as "[Hγ2a Hγ2b]"; [by apply cmra_update_exclusive|].
        rewrite {1}(_ : 3/4 = 1/4 + 1/2)%Qp; last (by apply: bool_decide_unpack).
        iDestruct "Hγ1" as "[Hγ1a Hγ1b]".
        wp_apply (release_spec with "[$Hlock $Hlocked Hγ1a Hγ2a Hc]").
        { do 2 iRight. iExists v, v'. iFrame. }
        iIntros "_". wp_pures. iRight. iExists v. iFrame.
      + iDestruct "Hc" as (v v') "(_ & Hγ2' & _)".
        by iDestruct (own_valid_2 with "Hγ2 Hγ2'") as %[].
    - iIntros (v1 v2) "[[[H1 Hγ]|H1] [[H2 Hγ']|H2]] !>".
      + by iDestruct (own_valid_2 with "Hγ Hγ'") as %[].
      + iDestruct "H2" as (v2') "(_&H1'&HP)".
        iDestruct (own_valid_2 with "H1 H1'") as %[_ [=->]%to_agree_op_inv_L].
        iApply "HΦ"; auto.
      + iDestruct "H1" as (v1') "(_&H2'&HP)".
        iDestruct (own_valid_2 with "H2 H2'") as %[_ [=->]%to_agree_op_inv_L].
        iApply "HΦ"; auto.
      + iDestruct "H1" as (v1') "[H1 _]"; iDestruct "H2" as (v2') "(_&H2&_)".
        by iDestruct (own_valid_2 with "H1 H2") as %[].
  Qed.

  Lemma prog_typed :
    ⊢ ∅ ⊨ prog : chan (<??> TY lty_int; <??> TY lty_int; END) ⊸ lty_int * lty_int.
  Proof.
    iIntros (vs) "!> HΓ /=".
    iApply wp_value.
    iSplitL; last by iApply env_ltyped_empty.
    iIntros (c) "Hc".
    iApply (wp_prog (λ v1 v2, ltty_car lty_int v1 ∗ ltty_car lty_int v2)%I with "[Hc]").
    { iApply (iProto_mapsto_le _ (lsty_car (<??> TY lty_int; <??> TY lty_int; END)) with "Hc").
      iIntros "!> !>" (v1). iDestruct 1 as %[x1 ->]. iExists #x1.
      iIntros "!>" (v2). iDestruct 1 as %[x2 ->]. iExists #x2. iSplitL; last done.
      rewrite /ltty_car /=. auto. }
    iIntros "!>" (v1 v2 [[[k1 ->] [k2 ->]]|[[k1 ->] [k2 ->]]]);
      iExists _, _; iSplit; by eauto.
  Qed.
End double.
