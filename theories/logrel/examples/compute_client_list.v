(** This file contains an example of a client that uses the
compute service of [theories/logrel/examples/compute_service.v]
which has the type:

  μ rec. & { cont : ? (X:★) (() ⊸ X). ! X. rec,
             stop : end }

It does so to compute the results of an input list with type
[list (() ⊸A)], into a list with type [list A], sending the
computations in parallel with receiving the results.

The client cannot be type checked with the rules of the type system,
as (1) its behaviour depends on the length of the list, and (2)
it shares the channel endpoint which changes between concurrent accesses.
Its typing judgement can however be manually verified, after which
it is composed with the type checked service. *)
From iris.algebra Require Import frac.
From iris.heap_lang Require Import metatheory.
From actris.utils Require Import llist.
From actris.channel Require Import proofmode.
From actris.logrel Require Import session_typing_rules napp.
From actris.logrel.lib Require Import list par_start.
From actris.logrel.examples Require Import compute_service.

Local Existing Instance spin_lock.

Definition send_all_par : val :=
  rec: "go" "c" "xs" "lk" "counter" :=
    if: lisnil "xs" then
      acquire "lk";; select "c" #stop;; release "lk"
    else
      acquire "lk";;
        select "c" #cont;; send "c" (lpop "xs");;
        "counter" <- !"counter"+#1;;
      release "lk";;
      "go" "c" "xs" "lk" "counter".

Definition recv_all_par : val :=
  rec: "go" "c" "ys" "n" "lk" "counter" :=
    if: "n" = #0 then #() else
      acquire "lk";;
      if: (#0 = !"counter") then
        release "lk";; "go" "c" "ys" "n" "lk" "counter"
      else
        let: "x" := recv "c" in
        "counter" <- !"counter"-#1;;
        release "lk";;
        "go" "c" "ys" ("n"-#1) "lk" "counter";;
        lcons "x" "ys".

Definition compute_client : val :=
  λ: "xs" "c",
   let: "n" := llength "xs" in
   let: "counter" := ref #0 in
   let: "ys" := lnil #() in
   let: "lk" := newlock #() in
   (send_all_par "c" "xs" "lk" "counter" |||
    recv_all_par "c" "ys" "n" "lk" "counter");; "ys".

Section compute_example.
  Context `{heapGS Σ, chanG Σ, spin_lockG Σ, spawnG Σ}.
  Context `{!inG Σ fracR}.

  Definition compute_type_client_aux (rec : lsty Σ) : lsty Σ :=
    lty_select $ <[cont := (<!! X> TY () ⊸ X; <??> TY X ; rec)%lty]> $
                 <[stop := END%lty]>∅.
  Instance compute_type_client_contractive :
    Contractive (compute_type_client_aux).
  Proof. solve_proto_contractive. Qed.
  Definition compute_type_client : lsty Σ :=
    lty_rec (compute_type_client_aux).
  Global Instance compute_type_client_unfold :
    ProtoUnfold (lsty_car (compute_type_client))
                (lsty_car (compute_type_client_aux compute_type_client)).
  Proof. apply proto_unfold_eq, (fixpoint_unfold compute_type_client_aux). Qed.

  Definition cont_type (A : ltty Σ) : lsty Σ :=
    (lty_select (<[ cont := <!!> TY () ⊸ A ; END ]>∅))%lty.
  Definition stop_type : lsty Σ :=
    (lty_select (<[ stop := END ]>∅))%lty.
  Definition recv_type (A : ltty Σ) : lsty Σ :=
    (<??> TY A ; END)%lty.

  Definition compute_type_invariant
             γ (A : ltty Σ) (c : val) (counter : loc) : iProp Σ :=
    ∃ (n : nat) (b : bool),
      (if b then True else own γ 1%Qp) ∗
      counter ↦ #n ∗
      c ↣ (lsty_car (lty_napp (recv_type A) n <++>
             (if b then compute_type_client else END)%lty)).

  Lemma compute_type_client_unfold_app_cont A :
    compute_type_client <:
      (cont_type A <++> (recv_type A <++> compute_type_client)).
  Proof.
    rewrite {1}/compute_type_client /lty_rec fixpoint_unfold.
    replace (fixpoint (compute_type_client_aux)) with
        (compute_type_client) by eauto.
    rewrite /compute_type_client_aux.
    iApply lty_le_trans.
    { iApply lty_le_select.
      iApply (big_sepM2_insert _ _ (<[stop:=END%lty]>∅));
              [ done | done | ].
      iSplit.
      - iExists A. iApply lty_le_refl.
      - iApply big_sepM2_insert; [ done | done | ].
        iSplit; [ iApply lty_le_refl | done ]. }
    iApply lty_le_trans.
    { iApply lty_le_select_subseteq.
      apply insert_mono, insert_subseteq; done. }
    rewrite /cont_type /recv_type.
    iPoseProof (lty_le_app_select) as "[_ Hle]".
    iApply (lty_le_trans); last by iApply "Hle".
    rewrite fmap_insert fmap_empty.
    rewrite lty_app_send lty_app_end_l.
    rewrite lty_app_recv lty_app_end_l.
    iApply lty_le_refl.
  Qed.

  Lemma compute_type_client_unfold_app_stop :
    compute_type_client <: lty_select (<[stop := END%lty]>∅).
  Proof.
    rewrite {1}/compute_type_client /lty_rec fixpoint_unfold.
    replace (fixpoint (compute_type_client_aux)) with
        (compute_type_client) by eauto.
    rewrite /compute_type_client_aux.
    iApply lty_le_select_subseteq.
    rewrite insert_commute; [ | eauto ].
    apply insert_mono, insert_subseteq; done.
  Qed.

  Lemma recv_type_cont_type_swap A B :
    recv_type B <++> cont_type A <: cont_type A <++> recv_type B.
  Proof.
    iApply lty_le_trans.
    rewrite lty_app_recv lty_app_end_l.
    iApply lty_le_swap_recv_select. rewrite fmap_insert fmap_empty.
    iPoseProof (lty_le_app_select) as "[_ Hle]".
    iApply (lty_le_trans); last by iApply "Hle".
    rewrite fmap_insert fmap_empty.
    iApply lty_le_select.
    iApply big_sepM2_insert; [ done | done |  ].
    iSplit; [ | done ].
    rewrite lty_app_send lty_app_end_l.
    iApply lty_le_swap_recv_send.
  Qed.

  Lemma recv_type_stop_type_swap A :
    recv_type A <++> stop_type <: stop_type <++> recv_type A.
  Proof.
    iApply lty_le_trans.
    rewrite lty_app_recv lty_app_end_l.
    iApply lty_le_swap_recv_select. rewrite fmap_insert fmap_empty.
    iPoseProof (lty_le_app_select) as "[_ Hle]".
    iApply (lty_le_trans); last by iApply "Hle".
    rewrite fmap_insert fmap_empty.
    iApply lty_le_select.
    iApply big_sepM2_insert; [ done | done |  ].
    iSplit; [ | done ].
    rewrite lty_app_end_l. eauto.
  Qed.

  Lemma send_all_par_spec γ γf A c l xs lk counter :
    {{{ llist (llist_type_pred (() ⊸ A)) l xs ∗ own γf 1%Qp ∗
        is_lock γ lk (compute_type_invariant γf A c counter) }}}
      send_all_par c #l lk #counter
    {{{ RET #(); llist (llist_type_pred (() ⊸ A)) l [] ∗
                 is_lock γ lk (compute_type_invariant γf A c counter) }}}.
  Proof.
    iIntros (Φ) "(Hl & Hf & #Hlk) HΦ".
    iInduction xs as [|x xs] "IH".
    { wp_lam. wp_smart_apply (lisnil_spec with "Hl"); iIntros "Hl".
      rewrite /select.
      wp_smart_apply (acquire_spec with "Hlk").
      iIntros "[Hlocked HI]".
      iDestruct "HI" as (n [ | ]) "(Hf' & Hcounter & Hc)"; last first.
      { by iCombine "Hf Hf'" gives %[]. }
      iDestruct (iProto_mapsto_le with "Hc []") as "Hc".
      { iApply iProto_le_trans.
        { iApply iProto_le_app; [ iApply iProto_le_refl | ].
          iApply compute_type_client_unfold_app_stop. }
        rewrite -lsty_car_app.
        iApply lsty_car_mono.
        iApply lty_napp_swap.
        iApply recv_type_stop_type_swap. }
      wp_send with "[]"; [ eauto | ].
      wp_smart_apply (release_spec with "[-HΦ Hl]").
      { iFrame "Hlk Hlocked".
        iExists n, false.
        rewrite lookup_total_insert -lsty_car_app lty_app_end_l lty_app_end_r.
        iFrame "Hf Hcounter Hc". }
      iIntros "_". iApply "HΦ". by iFrame "Hl Hlk". }
    wp_lam. wp_smart_apply (lisnil_spec with "Hl"); iIntros "Hl".
    wp_smart_apply (acquire_spec with "Hlk").
    iIntros "[Hlocked HI]".
    iDestruct "HI" as (n [ | ]) "(Hf' & Hcounter & Hc)"; last first.
    { by iCombine "Hf Hf'" gives %[]. }
    iDestruct (iProto_mapsto_le with "Hc []") as "Hc".
    { iApply iProto_le_trans.
      { iApply iProto_le_app; [ iApply iProto_le_refl | ].
        iApply compute_type_client_unfold_app_cont. }
      rewrite assoc. rewrite assoc. rewrite assoc.
      iApply iProto_le_app; [ | iApply iProto_le_refl ].
      iApply iProto_le_app; [ | iApply iProto_le_refl ].
      rewrite -lsty_car_app.
      iApply lsty_car_mono.
      iApply lty_napp_swap.
      iApply recv_type_cont_type_swap. }
    rewrite /select.
    wp_send with "[]"; [ eauto | ].
    rewrite lookup_total_insert.
    wp_smart_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
    wp_send with "[HIx]".
    { iDestruct "HIx" as (->) "$HIx". }
    wp_load. wp_store.
    wp_smart_apply (release_spec with "[-HΦ Hf Hl]").
    { iFrame "Hlk Hlocked".
      iExists (n+1), true.
      rewrite assoc.
      rewrite left_id.
      rewrite assoc.
      repeat rewrite -lsty_car_app.
      rewrite -lty_napp_S_r.
      rewrite Nat.add_succ_r.
      rewrite -plus_n_O.
      replace (Z.of_nat n + 1)%Z with (Z.of_nat (S n)) by lia.
      iFrame "Hc Hcounter". }
    iIntros "_". wp_pures.
    iApply ("IH" with "Hl Hf").
    iApply "HΦ".
  Qed.

  Lemma recv_all_par_spec γ γf A c l n lk counter :
    {{{ llist (llist_type_pred A) l [] ∗
        is_lock γ lk (compute_type_invariant γf A c counter) }}}
      recv_all_par c #l #n lk #counter
    {{{ ys, RET #(); ⌜n = length ys⌝ ∗
                     llist (llist_type_pred A) l ys ∗
                     is_lock γ lk (compute_type_invariant γf A c counter)  }}}.
  Proof.
    iIntros (Φ) "(Hl & #Hlk) HΦ".
    iLöb as "IH" forall (n Φ).
    destruct n as [ | n ].
    { wp_lam. wp_pures. iApply "HΦ". by iFrame "Hl Hlk". }
    wp_lam.
    wp_smart_apply (acquire_spec with "Hlk").
    iIntros "[Hlocked HI]".
    iDestruct "HI" as (m b) "(Hb & Hcounter & Hc)".
    wp_load.
    destruct m as [ | m ].
    { wp_smart_apply (release_spec with "[$Hlocked $Hlk Hb Hcounter Hc]").
      { iExists 0, b. iFrame "Hb Hcounter Hc". }
      iIntros "_". wp_pures. iApply ("IH" with "Hl").
      iApply "HΦ". }
    wp_recv (w) as "Hw". wp_pures.
    rewrite Nat2Z.inj_succ.
    wp_load. wp_store.
    replace (Z.succ (Z.of_nat m) - 1)%Z with (Z.of_nat m) by lia.
    wp_smart_apply (release_spec with "[$Hlocked $Hlk Hb Hcounter Hc]").
    { replace (Z.succ (Z.of_nat m) - 1)%Z with (Z.of_nat m) by lia.
      iExists m, b. iFrame "Hb Hcounter Hc". }
    iIntros "_".
    wp_pures.
    replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat (n)) by lia.
    wp_smart_apply ("IH" with "Hl").
    iIntros (ys). iDestruct 1 as (Heq) "(Hl & Hc)".
    wp_smart_apply (lcons_spec with "[$Hl $Hw//]").
    iIntros "Hl". iApply "HΦ". iFrame.
    iPureIntro. by rewrite Heq.
  Qed.

  Lemma ltyped_compute_client Γ (A : ltty Σ) :
    Γ ⊨ compute_client : lty_list (() ⊸ A) ⊸
                         chan compute_type_client ⊸
                         lty_list A.
  Proof.
    iApply ltyped_val_ltyped.
    iApply ltyped_val_lam.
    iApply ltyped_post_nil.
    iApply (ltyped_lam [CtxItem "xs" _]).
    iIntros "!>" (vs) "HΓ". simplify_map_eq.
    iDestruct (ctx_ltyped_cons _ _ "c" with "HΓ") as (vc ->) "[Hc HΓ]".
    iDestruct (ctx_ltyped_cons _ _ "xs" with "HΓ") as (vlxs ->) "[Hlxs HΓ]".
    rewrite /lty_list /lty_rec fixpoint_unfold.
    iDestruct "Hlxs" as (l' v ->) "[Hlxs Hv]".
    wp_smart_apply (llength_spec with "[Hlxs Hv]").
    { iEval (rewrite /lty_list /lty_rec fixpoint_unfold).
      iExists l', v. eauto with iFrame. }
    iIntros (xs n) "[<- Hlxs]".
    wp_alloc counter as "Hcounter".
    wp_smart_apply (lnil_spec); [ done | ].
    iIntros (lys) "Hlys".
    iMod (own_alloc 1%Qp) as (γf) "Hf"; [ done | ].
    wp_smart_apply (newlock_spec (compute_type_invariant γf A vc counter)
                with "[Hcounter Hc]").
    { iExists 0, true. repeat rewrite left_id. iFrame "Hcounter Hc". }
    iIntros (lk γ) "#Hlk".
    wp_smart_apply (par_spec
                (λ v, ⌜v = #()⌝)%I
                (λ v, ∃ ys, ⌜v = #()⌝ ∗ llist (llist_type_pred A) lys ys)%I
                with "[Hlxs Hf] [Hlys]").
    { wp_smart_apply (send_all_par_spec with "[$Hlxs $Hf $Hlk]").
      iIntros "(Hlxs & _)". eauto. }
    { wp_smart_apply (recv_all_par_spec with "[$Hlys $Hlk]").
      iIntros (ys) "(Heq & Hlys & _)".
      iExists ys. iFrame. eauto. }
    iIntros (w1 w2) "[-> Hw2]".
    iDestruct "Hw2" as (ys) "(-> & Hlys)".
    iIntros "!>".
    wp_pures. iFrame "HΓ".
    by iApply llist_lty_list.
  Qed.

  Lemma lty_le_compute_type_dual :
    lty_dual compute_type_service <: compute_type_client.
  Proof.
    rewrite /compute_type_client /compute_type_service.
    iLöb as "IH".
    iApply lty_le_r; [ | iApply lty_bi_le_sym; iApply lty_le_rec_unfold ].
    iApply lty_le_dual_l.
    iApply lty_le_r; [ | iApply lty_bi_le_sym; iApply lty_le_rec_unfold ].
    iApply lty_le_l; [ iApply lty_le_dual_select | ].
    iApply lty_le_branch. rewrite fmap_insert fmap_insert fmap_empty.
    iApply big_sepM2_insert; [ done | done | ].
    iSplit.
    - iApply lty_le_l; [ iApply lty_le_dual_send_exist | ].
      iIntros (As). iExists (As).
      iApply lty_le_recv; [ iApply lty_le_refl | ].
      iApply lty_le_l; [ iApply lty_le_dual_recv | ].
      iApply lty_le_send; [ iApply lty_le_refl | ].
      iIntros "!>!>!>". iApply lty_le_dual_l. iApply "IH".
    - iApply big_sepM2_insert; [ done | done | ]. iSplit; [ | done ].
      iApply lty_le_l; [ iApply lty_le_dual_end | iApply lty_le_refl ].
  Qed.

  Lemma ltyped_compute_list_par A e Γ Γ' :
    (Γ ⊨ e : lty_list (() ⊸ A) ⫤ Γ') -∗
    (Γ ⊨ par_start (compute_service) (compute_client e) :
       (() * (lty_list A)) ⫤ Γ').
  Proof.
    iIntros "He".
    iApply (ltyped_app with "[He]").
    { iApply (ltyped_app with "He").
      iApply ltyped_compute_client. }
    iApply ltyped_app.
    { iApply ltyped_compute_service. }
    iApply ltyped_subsumption; [ iApply ctx_le_refl | | iApply ctx_le_refl | ].
    { iApply lty_le_arr; [ iApply lty_le_refl | ].
      iApply lty_le_arr; [ | iApply lty_le_refl ].
      iApply lty_le_arr; [ | iApply lty_le_refl ].
      iApply lty_le_chan.
      iApply lty_le_compute_type_dual. }
    iApply ltyped_par_start.
  Qed.

End compute_example.
