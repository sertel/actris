From iris.bi Require Import updates.
From iris.base_logic.lib Require Import invariants mono_nat.
From iris.program_logic Require Export step_update.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import primitive_laws.
From actris.channel Require Export proto.

Set Default Proof Using "Type".

Section iProto_step.
  Context `{A : Type}.
  Context `{protoG Σ A, !heapGS Σ}.

  Definition iProto_step_ctx (χ : proto_name) (vsl vsr : list A) : iProp Σ :=
    steps_lb (length vsl) ∗ steps_lb (length vsr) ∗ iProto_ctx χ vsl vsr.

  Lemma iProto_step_init E p :
    ⊢ |~{E}~| ∃ χ, iProto_step_ctx χ [] [] ∗
                   iProto_own χ Left p ∗
                   iProto_own χ Right (iProto_dual p).
  Proof.
    iAssert (|~{E}~| steps_lb 0) as "-#Hlb1"; [by iApply step_get_lb_get|].
    iAssert (|~{E}~| steps_lb 0) as "-#Hlb2"; [by iApply step_get_lb_get|].
    iMod (iProto_init p) as (χ) "(Hctx & Hpl & Hpr)".
    iModIntro. iExists χ. iFrame "#∗".
  Qed.

  Instance step_update_except0 E P : IsExcept0 (|~{E}~> P).
  Proof.
    rewrite /IsExcept0. iIntros "Hstep". iApply fupd_step_update.
    iApply is_except_0. by iMod "Hstep".
  Qed.

  Lemma iProto_step_send_l E χ m vsr vsl vl p :
    ▷ iProto_step_ctx χ vsl vsr -∗
    ▷ iProto_own χ Left (<!> m)%proto -∗
    ▷ iMsg_car m vl (Next p) -∗
    |~{E}~> iProto_step_ctx χ (vsl ++ [vl]) vsr ∗ iProto_own χ Left p.
  Proof.
    iIntros "(>Hlbl & #>Hlbr & Hctx) Hp Hpm".
    iDestruct (step_update_lb_step with "Hlbr [Hctx Hp Hpm]") as "Hctx".
    { simpl. iIntros "!>!>". iMod (iProto_send_l with "Hctx Hp Hpm") as "H".
      iApply step_fupdN_intro; [done|]. iIntros "!>!>". iExact "H". }
    iDestruct (step_update_lb_update with "Hlbl") as "Hlbl'".
    iIntros "!>". iDestruct "Hctx" as "[Hctx Hown]". iFrame "#∗".
    rewrite app_length=> /=.
    replace (S (length vsl)) with ((length vsl) + 1)%nat by lia. by iFrame.
  Qed.

  Lemma iProto_step_send_r E χ m vsr vsl vr p :
    ▷ iProto_step_ctx χ vsl vsr -∗
    ▷ iProto_own χ Right (<!> m)%proto -∗
    ▷ iMsg_car m vr (Next p) -∗
    |~{E}~> iProto_step_ctx χ vsl (vsr ++ [vr]) ∗ iProto_own χ Right p.
  Proof.
    iIntros "(#>Hlbl & >Hlbr & Hctx) Hp Hpm".
    iDestruct (step_update_lb_step with "Hlbl [Hctx Hp Hpm]") as "Hctx".
    { simpl. iIntros "!>!>". iMod (iProto_send_r with "Hctx Hp Hpm") as "H".
      iApply step_fupdN_intro; [done|]. iIntros "!>!>". iExact "H". }
    iDestruct (step_update_lb_update with "Hlbr") as "Hlbr'".
    iIntros "!>". iDestruct "Hctx" as "[Hctx Hown]". iFrame "#∗".
    rewrite (app_length vsr [vr])=> /=.
    replace (S (length vsr)) with ((length vsr) + 1)%nat by lia. by iFrame.
  Qed.

  Lemma iProto_step_recv_l E χ m vr vsr vsl :
    ▷ iProto_step_ctx χ vsl (vr :: vsr) -∗
    ▷ iProto_own χ Left (<?> m)%proto -∗
    |~{E}~> ∃ p, iProto_step_ctx χ vsl vsr ∗ iProto_own χ Left p ∗
                 iMsg_car m vr (Next p).
  Proof.
    iIntros "(#>Hlbl&#>Hlbr&Hctx) Hp".
    iDestruct (step_update_lb_step with "Hlbr [Hctx Hp]") as "Hctx".
    { simpl. iIntros "!>!>". iMod (iProto_recv_l with "Hctx Hp") as "H".
      iApply step_fupdN_intro; [done|]. iIntros "!>!>!>!>". iExact "H". }
    iIntros "!>". iDestruct "Hctx" as (p) "(Hctx & Hp &HP)".
    iExists p. iFrame "#∗". iApply (steps_lb_le with "Hlbr")=>/=. lia.
  Qed.

  Lemma iProto_step_recv_r E χ m vl vsr vsl :
    ▷ iProto_step_ctx χ (vl :: vsl) vsr -∗
    ▷ iProto_own χ Right (<?> m)%proto -∗
    |~{E}~> ∃ p, iProto_step_ctx χ vsl vsr ∗ iProto_own χ Right p ∗
                 iMsg_car m vl (Next p).
  Proof.
    iIntros "(#>Hlbl&#>Hlbr&Hctx) Hp".
    iDestruct (step_update_lb_step with "Hlbl [Hctx Hp]") as "Hctx".
    { simpl. iIntros "!>!>". iMod (iProto_recv_r with "Hctx Hp") as "H".
      iApply step_fupdN_intro; [done|]. iIntros "!>!>!>!>". iExact "H". }
    iIntros "!>". iDestruct "Hctx" as (p) "(Hctx & Hp &HP)".
    iExists p. iFrame "#∗". iApply (steps_lb_le with "Hlbl")=>/=. lia.
  Qed.

End iProto_step.
