From iris.algebra Require Import frac.
From iris.heap_lang Require Import metatheory.
From actris.utils Require Import llist.
From actris.channel Require Import proofmode proto channel.
From actris.logrel Require Import term_typing_rules session_typing_rules
     subtyping_rules napp.
From actris.logrel.lib Require Import par_start.

Definition cont : Z := 1.
Definition stop : Z := 2.

Definition compute_service : val :=
  rec: "go" "c":=
    branch [cont;stop] "c"
    (λ: "c", let: "v" := recv "c" in
             send "c" ("v" #());; "go" "c")
    (λ: "c", #()).

Definition send_all_par : val :=
  rec: "go" "c" "xs" "lk" "counter" :=
    if: lisnil "xs" then
      acquire "lk";; select "c" #stop;; release "lk";; #()
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

Definition lty_list_aux `{!heapG Σ} (A : ltty Σ) (X : ltty Σ) : ltty Σ :=
  (() + (A * ref_uniq X))%lty.
Instance lty_list_aux_contractive `{!heapG Σ} A :
  Contractive (@lty_list_aux Σ _ A).
Proof. solve_proto_contractive. Qed.
Definition lty_list `{!heapG Σ} (A : ltty Σ) : ltty Σ := lty_rec (lty_list_aux A).

Notation "'list' A" := (lty_list A) (at level 10) : lty_scope.

Section compute_example.
  Context `{heapG Σ, chanG Σ, lockG Σ, spawnG Σ}.
  Context `{!inG Σ fracR}.

  Definition compute_type_service_aux (rec : lsty Σ) : lsty Σ :=
    lty_branch $ <[cont := (<?? A> TY () ⊸ A; <!!> TY A ; rec)%lty]> $
                 <[stop := END%lty]> $ ∅.
  Instance mapper_type_rec_service_contractive :
    Contractive (compute_type_service_aux).
  Proof. solve_proto_contractive. Qed.
  Definition compute_type_service : lsty Σ :=
    lty_rec (compute_type_service_aux).

  (** This judgement is checked only with the typing rules of the type system *)
  Lemma ltyped_compute_service Γ :
    ⊢ Γ ⊨ compute_service : lty_chan compute_type_service ⊸ () ⫤ Γ.
  Proof.
    iApply (ltyped_subsumption _ _ _ _ _ _
              (lty_chan compute_type_service → ())%lty);
      [ iApply env_le_refl | iApply lty_le_copy_elim | iApply env_le_refl | ].
    iApply ltyped_val_ltyped.
    iApply ltyped_val_rec.
    iApply ltyped_post_nil.
    iApply ltyped_app.
    { iApply (ltyped_lam []). iApply ltyped_post_nil. iApply ltyped_unit. }
    iApply (ltyped_app _ _ _ _ _
              (chan (<?? A> TY () ⊸ A; <!!> TY A; compute_type_service) ⊸ ())%lty).
    {
      simpl.
      iApply (ltyped_lam [EnvItem "go" _]).
      iApply ltyped_post_nil.
      iApply ltyped_recv_texist; [ done | apply _ | ].
      iIntros (Ys).
      pose proof (ltys_S_inv Ys) as [A [Ys' HYs]].
      pose proof (ltys_O_inv Ys') as HYs'.
      rewrite HYs HYs' /=.
      iApply ltyped_seq.
      { iApply (ltyped_send _ [EnvItem "v" _; EnvItem "c" _; EnvItem "go" _]);
          [ done | ].
        iApply ltyped_app; [ by iApply ltyped_unit | ]=> /=.
        by iApply ltyped_var. }
      simpl.
      iApply ltyped_app; [ by iApply ltyped_var | ].
      simpl. rewrite !(Permutation_swap (EnvItem "go" _)).
      iApply ltyped_subsumption; [ | | iApply env_le_refl | ].
      { iApply env_le_cons; [ iApply lty_le_refl | iApply env_le_nil ]. }
      { iApply lty_le_copy_elim. }
      by iApply ltyped_var. }
    iApply ltyped_app; [ by iApply ltyped_var | ].
    iApply ltyped_subsumption; [ iApply env_le_nil | | iApply env_le_refl | ].
    { iApply lty_le_arr; [ | iApply lty_le_refl ]. iApply lty_le_chan.
      iApply lty_le_l; [ iApply lty_le_rec_unfold | iApply lty_le_refl ]. }
    rewrite /compute_type_service_aux.
    iApply ltyped_branch. intros x. rewrite -elem_of_dom. set_solver.
  Qed.

  Definition compute_type_client_aux (A : ltty Σ) (rec : lsty Σ) : lsty Σ :=
    lty_select $ <[cont := (<!!> TY () ⊸ A; <??> TY A ; rec)%lty]> $
                 <[stop := END%lty]>∅.
  Instance compute_type_rec_client_contractive A :
    Contractive (compute_type_client_aux A).
  Proof. solve_proto_contractive. Qed.
  Definition compute_type_client A : lsty Σ :=
    lty_rec (compute_type_client_aux A).
  Global Instance compute_type_client_unfold A :
    ProtoUnfold (lsty_car (compute_type_client A))
                (lsty_car (compute_type_client_aux A (compute_type_client A))).
  Proof. apply proto_unfold_eq, (fixpoint_unfold (compute_type_client_aux A)). Qed.

  Definition list_pred (A : ltty Σ) : val → val → iProp Σ :=
    (λ v w : val, ⌜v = w⌝ ∗ ltty_car A v)%I.

  Lemma llength_spec A (l : loc) :
    ⊢ {{{ ltty_car (ref_uniq (list A)) #l }}} llength #l
      {{{ xs (n:Z), RET #n; ⌜Z.of_nat (length xs) = n⌝ ∗
                            llist (λ v w , ⌜v = w⌝ ∗ ltty_car A v) l xs }}}.
  Proof.
    iIntros "!>" (Φ) "Hl HΦ".
    iLöb as "IH" forall (l Φ).
    iDestruct "Hl" as (ltmp l' [=<-]) "[Hl Hl']".
    wp_lam.
    rewrite {2}/lty_list /lty_rec /lty_list_aux fixpoint_unfold.
    iDestruct "Hl'" as "[Hl' | Hl']".
    - iDestruct "Hl'" as (xs ->) "Hl'".
      wp_load. wp_pures.
      iAssert (llist (list_pred A) l [])%I with "[Hl Hl']" as "Hl".
      { rewrite /llist. iDestruct "Hl'" as %->. iApply "Hl". }
      iApply "HΦ". eauto with iFrame.
    - iDestruct "Hl'" as (xs ->) "Hl'".
      wp_load. wp_pures.
      iDestruct "Hl'" as (x vl' ->) "[HA Hl']".
      iDestruct "Hl'" as (l' xs ->) "[Hl' Hl'']".
      wp_apply ("IH" with "[Hl' Hl'']").
      { iExists _, _. iFrame "Hl' Hl''". done. }
      iIntros (ys n) "[<- H]".
      iAssert (llist (list_pred A) l (x :: ys))%I with "[Hl HA H]" as "Hl".
      { iExists x, l'. eauto with iFrame. }
      wp_pures. iApply "HΦ". iFrame "Hl". by rewrite (Nat2Z.inj_add 1).
  Qed.

  Definition cont_type (A : ltty Σ) : lsty Σ :=
    (lty_select (<[ cont := <!!> TY () ⊸ A ; END ]>∅))%lty.
  Definition stop_type : lsty Σ :=
    (lty_select (<[ stop := END ]>∅))%lty.
  Definition recv_type (A : ltty Σ) : lsty Σ :=
    (<??> TY A ; END)%lty.

  Definition compute_type_invariant
             γ (A : ltty Σ) (c : val) (counter : loc) : iProp Σ :=
    (∃ (n : nat) (b : bool),
        (if b then True else own γ 1%Qp) ∗
        counter ↦ #n ∗
        c ↣ (lsty_car (lty_napp (recv_type A) n <++>
               (if b then compute_type_client A else END)%lty)))%I.

  Lemma compute_type_client_unfold_app_cont A :
    ⊢ compute_type_client A <:
        (cont_type A <++> (recv_type A <++> compute_type_client A))%lty.
  Proof.
    rewrite {1}/compute_type_client /lty_rec fixpoint_unfold.
    replace (fixpoint (compute_type_client_aux A)) with
        (compute_type_client A) by eauto.
    rewrite /compute_type_client_aux.
    iApply lty_le_trans.
    { iApply lty_le_select_subseteq.
      apply insert_mono, insert_subseteq=> //. }
    rewrite /cont_type /recv_type.
    iPoseProof (lty_le_app_select) as "[_ Hle]".
    iApply (lty_le_trans); last by iApply "Hle".
    rewrite fmap_insert fmap_empty.
    rewrite lty_app_send lty_app_end_l.
    rewrite lty_app_recv lty_app_end_l.
    iApply lty_le_refl.
  Qed.

  Lemma compute_type_client_unfold_app_stop A :
    ⊢ compute_type_client A <: lty_select (<[stop := END%lty]>∅).
  Proof.
    rewrite {1}/compute_type_client /lty_rec fixpoint_unfold.
    replace (fixpoint (compute_type_client_aux A)) with
        (compute_type_client A) by eauto.
    rewrite /compute_type_client_aux.
    iApply lty_le_select_subseteq.
    rewrite insert_commute; [ | eauto ].
    apply insert_mono, insert_subseteq=> //.
  Qed.

  Lemma recv_type_cont_type_swap A B :
    ⊢ (recv_type B <++> cont_type A <: cont_type A <++> recv_type B)%lty.
  Proof.
    iApply lty_le_trans.
    rewrite lty_app_recv lty_app_end_l.
    iApply lty_le_swap_recv_select. rewrite fmap_insert fmap_empty.
    iPoseProof (lty_le_app_select) as "[_ Hle]".
    iApply (lty_le_trans); last by iApply "Hle".
    rewrite fmap_insert fmap_empty.
    iApply lty_le_select.
    iApply big_sepM2_insert=> //.
    iSplit=> //.
    rewrite lty_app_send lty_app_end_l.
    iApply lty_le_swap_recv_send.
  Qed.

  Lemma recv_type_stop_type_swap B :
    ⊢ (recv_type B <++> stop_type <: stop_type <++> recv_type B)%lty.
  Proof.
    iApply lty_le_trans.
    rewrite lty_app_recv lty_app_end_l.
    iApply lty_le_swap_recv_select. rewrite fmap_insert fmap_empty.
    iPoseProof (lty_le_app_select) as "[_ Hle]".
    iApply (lty_le_trans); last by iApply "Hle".
    rewrite fmap_insert fmap_empty.
    iApply lty_le_select.
    iApply big_sepM2_insert=> //.
    iSplit=> //.
    rewrite lty_app_end_l. eauto.
  Qed.

  Lemma send_all_par_spec γ γf A c l xs lk counter :
    {{{ llist (list_pred (() ⊸ A)) l xs ∗ own γf 1%Qp ∗
        is_lock γ lk (compute_type_invariant γf A c counter) }}}
      send_all_par c #l lk #counter
    {{{ RET #(); llist (list_pred (() ⊸ A)) l [] ∗
                 is_lock γ lk (compute_type_invariant γf A c counter) }}}.
  Proof.
    iIntros (Φ) "(Hl & Hf & #Hlk) HΦ".
    iInduction xs as [|x xs] "IH".
    { wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl".
      rewrite /select.
      wp_apply (acquire_spec with "Hlk").
      iIntros "[Hlocked HI]".
      iDestruct "HI" as (n [ | ]) "(Hf' & Hcounter & Hc)"; last first.
      { by iDestruct (own_valid_2 with "Hf Hf'") as %[]. }
      iDestruct (iProto_mapsto_le with "Hc []") as "Hc".
      { iApply iProto_le_trans.
        { iApply iProto_le_app; [ iApply iProto_le_refl | ].
          iApply compute_type_client_unfold_app_stop. }
        rewrite -lsty_car_app.
        iApply lsty_car_mono.
        iApply lty_napp_swap.
        iApply recv_type_stop_type_swap. }
      wp_send with "[]"; [ eauto | ].
      wp_apply (release_spec with "[-HΦ Hl]").
      { iFrame "Hlk Hlocked".
        iExists n, false.
        rewrite lookup_total_insert -lsty_car_app lty_app_end_l lty_app_end_r.
        iFrame "Hf Hcounter Hc". }
      iIntros "_". wp_pures. iApply "HΦ". iFrame "Hl Hlk Hsf". }
    wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl".
    wp_apply (acquire_spec with "Hlk").
    iIntros "[Hlocked HI]".
    iDestruct "HI" as (n [ | ]) "(Hf' & Hcounter & Hc)"; last first.
    { by iDestruct (own_valid_2 with "Hf Hf'") as %[]. }
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
    wp_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
    wp_send with "[HIx]".
    { iDestruct "HIx" as (->) "$HIx". }
    wp_load. wp_store.
    wp_apply (release_spec with "[-HΦ Hf Hl]").
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
    {{{ llist (list_pred A) l [] ∗
        is_lock γ lk (compute_type_invariant γf A c counter) }}}
      recv_all_par c #l #n lk #counter
    {{{ ys, RET #(); ⌜n = length ys⌝ ∗
                     llist (list_pred A) l ys ∗
                     is_lock γ lk (compute_type_invariant γf A c counter)  }}}.
  Proof.
    iIntros (Φ) "(Hl & #Hlk) HΦ".
    iLöb as "IH" forall (n Φ).
    destruct n as [ | n ].
    { wp_lam. wp_pures. iApply "HΦ". by iFrame "Hl Hlk". }
    wp_lam.
    wp_apply (acquire_spec with "Hlk").
    iIntros "[Hlocked HI]".
    iDestruct "HI" as (m b) "(Hb & Hcounter & Hc)".
    wp_load.
    destruct m as [ | m ].
    { wp_apply (release_spec with "[$Hlocked $Hlk Hb Hcounter Hc]").
      { iExists 0, b. iFrame "Hb Hcounter Hc". }
      iIntros "_". wp_pures. iApply ("IH" with "Hl").
      iApply "HΦ". }
    wp_recv (w) as "Hw". wp_pures.
    rewrite Nat2Z.inj_succ.
    wp_load. wp_store.
    replace (Z.succ (Z.of_nat m) - 1)%Z with (Z.of_nat m) by lia.
    wp_apply (release_spec with "[$Hlocked $Hlk Hb Hcounter Hc]").
    { replace (Z.succ (Z.of_nat m) - 1)%Z with (Z.of_nat m) by lia.
      iExists m, b. iFrame "Hb Hcounter Hc". }
    iIntros "_".
    wp_pures.
    replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat (n)) by lia.
    wp_apply ("IH" with "Hl").
    iIntros (ys). iDestruct 1 as (Heq) "(Hl & Hc)".
    wp_apply (lcons_spec with "[$Hl $Hw//]").
    iIntros "Hl". iApply "HΦ". iFrame.
    iPureIntro. by rewrite Heq.
  Qed.

  Lemma llist_lty_list lys ys A :
    llist (list_pred A) lys ys -∗
    ltty_car (ref_uniq (lty_list A)) #lys.
  Proof.
    iIntros "Hlys".
    iInduction ys as [|y ys] "IH" forall (lys).
    - iExists lys, NONEV. rewrite /llist. iFrame "Hlys".
      iSplit=> //.
      rewrite /lty_list /lty_rec fixpoint_unfold.
      iLeft. eauto.
    - iDestruct "Hlys" as (vb l'') "[[-> HB] [Hl' Hrec]]".
      iExists lys, _. iFrame "Hl'".
      iSplit=> //.
      rewrite /lty_list /lty_rec. iEval (rewrite fixpoint_unfold).
      iRight. iExists _. iSplit=> //. iExists _, _. iSplit=> //.
      iFrame "HB". by iApply ("IH" with "Hrec").
  Qed.

  Lemma ltyped_compute_client Γ (A : ltty Σ) :
    ⊢ Γ ⊨ compute_client : ref_uniq (lty_list (() ⊸ A)) ⊸
                           chan (compute_type_client A) ⊸
                           ref_uniq (lty_list A).
  Proof.
    iApply ltyped_val_ltyped.
    iApply ltyped_val_lam=> //.
    iApply ltyped_post_nil.
    iApply (ltyped_lam [EnvItem "xs" _]).
    iIntros "!>" (vs) "HΓ". simplify_map_eq.
    iDestruct (env_ltyped_cons _ _ "c" with "HΓ") as (vc ->) "[Hc HΓ]".
    iDestruct (env_ltyped_cons _ _ "xs" with "HΓ") as (vlxs ->) "[Hlxs HΓ]".
    iDestruct "Hlxs" as (l' v ->) "[Hlxs Hv]".
    wp_apply (llength_spec with "[Hlxs Hv]").
    { iExists l', v. eauto with iFrame. }
    iIntros (xs n) "[<- Hlxs]".
    wp_alloc counter as "Hcounter".
    wp_apply (lnil_spec); [ done | ].
    iIntros (lys) "Hlys".
    iMod (own_alloc 1%Qp) as (γf) "Hf"; [ done | ].
    wp_apply (newlock_spec (compute_type_invariant γf A vc counter)
                with "[Hcounter Hc]").
    { iExists 0, true. repeat rewrite left_id. iFrame "Hcounter Hc". }
    iIntros (lk γ) "#Hlk".
    wp_apply (par_spec
                (λ v, ⌜v = #()⌝)%I
                (λ v, ∃ ys, ⌜v = #()⌝ ∗ llist (list_pred A) lys ys)%I
                with "[Hlxs Hf] [Hlys]").
    { wp_apply (send_all_par_spec with "[$Hlxs $Hf $Hlk]").
      iIntros "(Hlxs & _)". eauto. }
    { wp_apply (recv_all_par_spec with "[$Hlys $Hlk]").
      iIntros (ys) "(Heq & Hlys & _)".
      iExists ys. iFrame. eauto. }
    iIntros (w1 w2) "[-> Hw2]".
    iDestruct "Hw2" as (ys) "(-> & Hlys)".
    iIntros "!>".
    wp_pures. iFrame "HΓ".
    by iApply llist_lty_list.
  Qed.

  Lemma lty_le_compute_type_dual A :
    ⊢ lty_dual compute_type_service <: compute_type_client A.
  Proof.
    rewrite /compute_type_client /compute_type_service.
    iLöb as "IH".
    iApply lty_le_r; [ | iApply lty_bi_le_sym; iApply lty_le_rec_unfold ].
    iApply lty_le_dual_l.
    iApply lty_le_r; [ | iApply lty_bi_le_sym; iApply lty_le_rec_unfold ].
    iApply lty_le_l; [ iApply lty_le_dual_select | ].
    iApply lty_le_branch. rewrite fmap_insert fmap_insert fmap_empty.
    iApply big_sepM2_insert=> //.
    iSplit.
    - iApply lty_le_l; [ iApply lty_le_dual_send | ].
      iExists A.
      iApply lty_le_recv; [ iApply lty_le_refl | ].
      iApply lty_le_l; [ iApply lty_le_dual_recv | ].
      iApply lty_le_send; [ iApply lty_le_refl | ].
      iIntros "!>!>!>". iApply lty_le_dual_l. iApply "IH".
    - iApply big_sepM2_insert=> //.
      iSplit=> //. iApply lty_le_l; [ iApply lty_le_dual_end | iApply lty_le_refl ].
  Qed.

  Lemma ltyped_compute_prog A e Γ Γ' :
    (Γ ⊨ e : ref_uniq (lty_list (() ⊸ A)) ⫤ Γ') -∗
    Γ ⊨ par_start (compute_service) (compute_client e) :
      (() * (ref_uniq (lty_list A))) ⫤ Γ'.
  Proof.
    iIntros "He".
    iApply (ltyped_app with "[He]").
    { iApply (ltyped_app with "He").
      iApply ltyped_compute_client. }
    iApply ltyped_app.
    { iApply ltyped_compute_service. }
    iApply ltyped_subsumption; [ iApply env_le_refl | | iApply env_le_refl | ].
    { iApply lty_le_arr; [ iApply lty_le_refl | ].
      iApply lty_le_arr; [ | iApply lty_le_refl ].
      iApply lty_le_arr; [ | iApply lty_le_refl ].
      iApply lty_le_chan.
      iApply lty_le_compute_type_dual. }
    iApply ltyped_par_start.
  Qed.

End compute_example.
