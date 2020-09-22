(** This file contains an example of a mapper service and a client.
The service has the type:

  ? (X,Y:★) (X ⊸ Y). μ rec. & { cont : ?X. !Y. rec,
                                stop : end }

The client uses the service to map the values of an input list with type
[list A] using an input function [A → B], into a list with
type [list B], sending all of the values up front, and only then
request the results.

The client cannot be type checked with the rules of the type system,
as its behaviour depends on the length of the list.
Its typing judgement can however be manually verified, after which
it is composed with the type checked service.

The file contains two proofs of the sending phase of the client.
An ad hoc version, where the recursive type is unfolded iteratively,
and have select and sends swapped ahead of the receives.
An upfront version, where it using subtyping to unfold the recursive
type an amount of types corresponding to the size of the list, after
which all selects and seands are swapped ahead of all receives immediately. *)
From actris.channel Require Import proofmode proto channel.
From actris.logrel Require Import session_types subtyping_rules
     term_typing_judgment term_typing_rules session_typing_rules
     environments telescopes napp.
From actris.utils Require Import llist.
From actris.logrel.lib Require Import list par_start.
From iris.proofmode Require Import tactics.

Definition cont : Z := 1.
Definition stop : Z := 2.

Definition mapper_service_aux : val :=
  rec: "go" "f" "c":=
    (branch [cont;stop]) "c"
    (λ: "c", let: "v" := recv "c" in
     send "c" ("f" "v");; "go" "f" "c")
    (λ: "c", #()).

Definition mapper_service : val :=
  λ: "c",
    let: "f" := recv "c" in
    mapper_service_aux "f" "c".

Definition send_all : val :=
  rec: "go" "c" "xs" :=
    if: lisnil "xs" then #() else
      select "c" #cont;; send "c" (lpop "xs");; "go" "c" "xs".

Definition recv_all : val :=
  rec: "go" "c" "ys" "n" :=
    if: "n" = #0 then #() else
      let: "x" := recv "c" in
      "go" "c" "ys" ("n"-#1%Z);; lcons "x" "ys".

Definition mapper_client : val :=
  λ: "f" "xs" "c",
   send "c" "f";;
   let: "n" := llength "xs" in
   send_all "c" "xs";; recv_all "c" "xs" "n";; select "c" #stop;; "xs".

Definition mapper_prog : val :=
  λ: "f" "xs",
   par_start (mapper_service) (mapper_client "f" "xs").

Section mapper_example.
  Context `{heapG Σ, chanG Σ}.

  Definition mapper_type_rec_service_aux (A : ltty Σ) (B : ltty Σ) (rec : lsty Σ)
    : lsty Σ :=
    lty_branch $ <[cont := (<??> TY A; <!!> TY B ; rec)%lty]>
               $ <[stop := END%lty]> $ ∅.
  Instance mapper_type_rec_service_contractive A B :
    Contractive (mapper_type_rec_service_aux A B).
  Proof. solve_proto_contractive. Qed.
  Definition mapper_type_rec_service A B : lsty Σ :=
    lty_rec (mapper_type_rec_service_aux A B).

  Lemma ltyped_mapper_aux_service Γ A B :
    ⊢ Γ ⊨ mapper_service_aux : (A → B) ⊸ lty_chan (mapper_type_rec_service A B) ⊸
                                       () ⫤ Γ.
  Proof.
    iApply (ltyped_subsumption _ _ _ _ _ _
              ((A → B) → lty_chan (mapper_type_rec_service A B) ⊸ ())%lty);
      [ iApply env_le_refl | iApply lty_le_copy_elim | iApply env_le_refl | ].
    iApply ltyped_val_ltyped.
    iApply ltyped_val_rec.
    iApply (ltyped_lam [EnvItem "go" _; EnvItem "f" _]).
    iApply ltyped_post_nil.
    iApply ltyped_app.
    { iApply (ltyped_lam []). iApply ltyped_post_nil. iApply ltyped_unit. }
    iApply ltyped_app.
    {
      simpl. rewrite !(Permutation_swap (EnvItem "f" _))
                     !(Permutation_swap (EnvItem "go" _)).
      iApply (ltyped_lam [EnvItem "go" _; EnvItem "f" _]).
      iApply ltyped_post_nil.
      iApply ltyped_let; [ by iApply ltyped_recv | ].
      iApply ltyped_seq.
      { iApply (ltyped_send _
                  [EnvItem "f" _; EnvItem "v" _; EnvItem "c" _; EnvItem "go" _]);
          [ done | ].
        iApply ltyped_app_copy; [ by iApply ltyped_var | ]=> /=.
        rewrite !(Permutation_swap (EnvItem "f" _)).
        by iApply ltyped_var. }
      simpl. rewrite !(Permutation_swap (EnvItem "f" _)).
      iApply ltyped_subsumption; [ | iApply lty_le_refl | iApply env_le_refl | ].
      { iApply env_le_cons; [ | iApply env_le_refl ].
        iApply lty_le_copy_inv_elim_copyable. iApply lty_copyable_arr_copy. }
      iApply ltyped_app; [ by iApply ltyped_var | ].
      iApply ltyped_app; [ by iApply ltyped_var | ].
      simpl. rewrite !(Permutation_swap (EnvItem "go" _)).
      iApply ltyped_subsumption; [ iApply env_le_refl | | iApply env_le_refl | ].
      { iApply lty_le_copy_elim. }
      by iApply ltyped_var. }
    iApply ltyped_app; [ by iApply ltyped_var | ].
    iApply ltyped_subsumption; [ iApply env_le_refl | | iApply env_le_refl | ].
    { iApply lty_le_arr; [ | iApply lty_le_refl ]. iApply lty_le_chan.
      iApply lty_le_l; [ iApply lty_le_rec_unfold | iApply lty_le_refl ]. }
    iApply ltyped_branch. intros x. rewrite -elem_of_dom. set_solver.
  Qed.

  Definition mapper_type_service : lsty Σ :=
    <?? X Y> TY X → Y ; mapper_type_rec_service X Y.

  Lemma ltyped_mapper_service Γ :
    ⊢ Γ ⊨ mapper_service : lty_chan (mapper_type_service) ⊸ () ⫤ Γ.
  Proof.
    iApply ltyped_val_ltyped.
    iApply ltyped_val_lam.
    iApply ltyped_post_nil.
    iApply ltyped_recv_texist; [ done | apply _ | ].
    iIntros (Ys).
    iApply ltyped_app; [ by iApply ltyped_var | ].
    iApply ltyped_app; [ by iApply ltyped_var | ].
    pose proof (ltys_S_inv Ys) as [A [Ks HYs]].
    pose proof (ltys_S_inv Ks) as [B [Ks' HKs]].
    pose proof (ltys_O_inv Ks') as HKs'.
    rewrite HYs HKs HKs' /=.
    iApply (ltyped_subsumption _ []);
      [ iApply env_le_nil | iApply lty_le_refl | iApply env_le_refl | ].
    iApply ltyped_mapper_aux_service.
  Qed.

  Definition mapper_type_rec_client_aux
             (A : ltty Σ) (B : ltty Σ) (rec : lsty Σ) : lsty Σ :=
    lty_select $ <[cont := (<!!> TY A; <??> TY B ; rec)%lty]>
               $ <[stop := END%lty]> $ ∅.
  Instance mapper_type_rec_client_contractive A B :
    Contractive (mapper_type_rec_client_aux A B).
  Proof. solve_proto_contractive. Qed.
  Definition mapper_type_rec_client A B : lsty Σ :=
    lty_rec (mapper_type_rec_client_aux A B).
  Global Instance mapper_type_rec_client_unfold A B :
    ProtoUnfold (lsty_car (mapper_type_rec_client A B))
                (lsty_car (mapper_type_rec_client_aux A B
                           (mapper_type_rec_client A B))).
  Proof. apply proto_unfold_eq,
         (fixpoint_unfold (mapper_type_rec_client_aux A B)). Qed.
  Definition mapper_type_client : lsty Σ :=
    <!! A B> TY A → B ; mapper_type_rec_client A B.

  Definition send_type (A : ltty Σ) : lsty Σ :=
    (lty_select (<[cont := <!!> TY A ; END ]>∅))%lty.
  Definition recv_type (B : ltty Σ) : lsty Σ :=
    (<??> TY B ; END)%lty.

  Lemma recv_type_send_type_swap A B :
    ⊢ (recv_type B <++> send_type A <: send_type A <++> recv_type B)%lty.
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

  Lemma mapper_type_rec_client_unfold_app A B :
    ⊢ mapper_type_rec_client A B <:
        (send_type A <++> (recv_type B <++> mapper_type_rec_client A B))%lty.
  Proof.
    rewrite {1}/mapper_type_rec_client /lty_rec fixpoint_unfold.
    replace (fixpoint (mapper_type_rec_client_aux A B)) with
        (mapper_type_rec_client A B) by eauto.
    rewrite /mapper_type_rec_client_aux.
    iApply lty_le_trans.
    { iApply lty_le_select_subseteq.
      apply insert_mono, insert_subseteq=> //. }
    rewrite /send_type /recv_type.
    iPoseProof (lty_le_app_select) as "[_ Hle]".
    iApply (lty_le_trans); last by iApply "Hle".
    rewrite fmap_insert fmap_empty.
    rewrite lty_app_send lty_app_end_l.
    rewrite lty_app_recv lty_app_end_l.
    iApply lty_le_refl.
  Qed.

  Lemma mapper_type_rec_client_unfold_app_n A B n :
    ⊢ mapper_type_rec_client A B <:
         lty_napp (send_type A) n <++> (lty_napp (recv_type B) n <++>
                                           mapper_type_rec_client A B).
  Proof.
    iInduction n as [|n] "IH"; simpl; [ | ].
    { rewrite /send_type /recv_type /=.
      do 2 rewrite lty_app_end_l. iApply lty_le_refl. }
    rewrite -lty_napp_flip -lty_napp_flip.
    iEval (rewrite -assoc).
    iApply lty_le_trans; last first.
    { iApply lty_le_app; [ iApply lty_le_refl | ].
      iEval (rewrite -assoc assoc).
      iApply lty_le_app; [ | iApply lty_le_refl ].
      iApply lty_napp_swap. iApply recv_type_send_type_swap. }
    iEval (rewrite -assoc).
    iApply (lty_le_trans with "IH").
    iApply lty_le_app; [ iApply lty_le_refl | ].
    iApply lty_le_app; [ iApply lty_le_refl | ].
    iApply mapper_type_rec_client_unfold_app.
  Qed.

  Lemma recv_mapper_type_rec_client_unfold_app A B n :
    ⊢ (lty_napp (recv_type B) n <++> mapper_type_rec_client A B) <:
      (send_type A <++>
                 (lty_napp (recv_type B) (S n) <++> mapper_type_rec_client A B)).
  Proof.
    iApply lty_le_trans.
    { iApply lty_le_app;
        [ iApply lty_le_refl | iApply mapper_type_rec_client_unfold_app ]. }
    iEval (rewrite assoc).
    iApply lty_le_trans.
    { iApply lty_le_app; [ | iApply lty_le_refl ].
      iApply lty_napp_swap. iApply recv_type_send_type_swap. }
    iEval (rewrite -assoc (assoc _ (lty_napp _ _))).
    rewrite -lty_napp_S_r.
    iApply lty_le_refl.
  Qed.

  Lemma send_all_spec_upfront A c l xs ty :
    {{{ llist (llist_type_pred A) l xs ∗
        c ↣ lsty_car (lty_napp (send_type A) (length xs) <++> ty) }}}
      send_all c #l
    {{{ RET #(); llist (llist_type_pred A) l [] ∗ c ↣ lsty_car ty }}}.
  Proof.
    iIntros (Φ) "[Hl Hc] HΦ".
    iInduction xs as [|x xs] "IH".
    { wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl"; wp_pures.
      iApply "HΦ". iFrame. }
    wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl".
    rewrite /select.
    wp_send with "[]"; first by eauto.
    rewrite lookup_total_insert.
    wp_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
    wp_send with "[HIx]".
    { iDestruct "HIx" as (->) "$HIx". }
    wp_apply ("IH" with "Hl Hc").
    done.
  Qed.

  Lemma send_all_spec_aux A B c l xs n :
    {{{ llist (llist_type_pred A) l xs ∗
        c ↣ lsty_car (lty_napp (recv_type B) n <++> (mapper_type_rec_client A B)) }}}
      send_all c #l
    {{{ RET #(); llist (llist_type_pred A) l [] ∗
                 c ↣ lsty_car (lty_napp (recv_type B) (length xs + n) <++>
                                             (mapper_type_rec_client A B)) }}}.
  Proof.
    iIntros (Φ) "[Hl Hc] HΦ".
    iInduction xs as [|x xs] "IH" forall (n).
    { wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl"; wp_pures.
      iApply "HΦ". iFrame. }
    wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl".
    simpl.
    iDestruct (iProto_mapsto_le c with "Hc []") as "Hc".
    { iApply recv_mapper_type_rec_client_unfold_app. }
    rewrite /select.
    wp_send with "[]"; first by eauto.
    rewrite lookup_total_insert.
    wp_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
    wp_send with "[HIx]".
    { iDestruct "HIx" as (->) "$HIx". }
    wp_apply ("IH" $!(S n) with "Hl Hc").
    by rewrite Nat.add_succ_r.
  Qed.

  Lemma send_all_spec_ad_hoc A B c l xs :
    {{{ llist (llist_type_pred A) l xs ∗
        c ↣ lsty_car (mapper_type_rec_client A B) }}}
      send_all c #l
    {{{ RET #(); llist (llist_type_pred A) l [] ∗
                 c ↣ lsty_car (lty_napp (recv_type B) (length xs)
                                             <++> (mapper_type_rec_client A B)) }}}.
  Proof.
    iIntros (Φ) "[Hl Hc] HΦ".
    iApply (send_all_spec_aux _ _ _ _ _ 0 with "[$Hl Hc]").
    { simpl. by rewrite lty_app_end_l. }
    iIntros "!> [Hl Hc]". iApply "HΦ".
    rewrite -(plus_n_O (length xs)). iFrame.
  Qed.

  Lemma recv_all_spec B c ty l n :
    {{{ llist (llist_type_pred B) l [] ∗
              c ↣ lsty_car (lty_napp (recv_type B) n <++> ty) }}}
      recv_all c #l #n
    {{{ ys, RET #(); ⌜n = length ys⌝ ∗
                     llist (llist_type_pred B) l ys ∗ c ↣ lsty_car ty }}}.
  Proof.
    iIntros (Φ) "[Hl Hc] HΦ".
    iLöb as "IH" forall (n Φ).
    destruct n.
    { wp_lam. wp_pures. iApply "HΦ". by iFrame. }
    wp_lam. wp_recv (w) as "Hw". wp_pures.
    rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat (n)) - 1)%Z with (Z.of_nat (n)) by lia.
    wp_apply ("IH" with "Hl Hc").
    iIntros (ys) "(% & Hl & Hc)".
    wp_apply (lcons_spec with "[$Hl $Hw//]").
    iIntros "Hl". iApply "HΦ". iFrame.
    iPureIntro. by rewrite H1.
  Qed.

  Lemma ltyped_mapper_client_ad_hoc Γ (A B : ltty Σ) :
    ⊢ Γ ⊨ mapper_client : (A → B) ⊸
                          lty_list A ⊸
                          chan mapper_type_client ⊸
                          lty_list B.
  Proof.
    iApply ltyped_val_ltyped.
    iApply ltyped_val_lam.
    iApply (ltyped_lam [EnvItem "f" _]).
    iApply (ltyped_lam [EnvItem "xs" _; EnvItem "f" _]).
    iIntros (vs) "!> HΓ /=".
    rewrite (lookup_delete_ne _ "n" "c")=> //.
    rewrite (lookup_delete_ne _ "n" "xs")=> //.
    rewrite lookup_delete=> //.
    iDestruct (env_ltyped_cons _ _ "c" with "HΓ") as (vc ->) "[Hc HΓ]".
    iDestruct (env_ltyped_cons _ _ "xs" with "HΓ") as (vl ->) "[Hl HΓ]".
    iDestruct (env_ltyped_cons _ _ "f" with "HΓ") as (vf ->) "[Hf HΓ]".
    wp_send with "[Hf//]".
    iDestruct (list_type_loc with "Hl") as %[l ->].
    wp_apply (llength_spec A with "Hl").
    iIntros (xs n) "[<- Hl]".
    wp_pures.
    wp_apply (send_all_spec_ad_hoc with "[$Hl $Hc]").
    iIntros "[Hl Hc]".
    wp_apply (recv_all_spec with "[Hl $Hc //]").
    iIntros (ys). iDestruct 1 as (Hlen) "[Hl Hc]".
    rewrite /mapper_type_rec_client /lty_rec fixpoint_unfold.
    rewrite /select.
    wp_send with "[]"; first by eauto.
    wp_pures.
    iFrame.
    by iApply llist_lty_list.
  Qed.

  Lemma ltyped_mapper_client_upfront Γ (A B : ltty Σ) :
    ⊢ Γ ⊨ mapper_client : (A → B) ⊸
                          lty_list A ⊸
                          chan mapper_type_client ⊸
                          lty_list B.
  Proof.
    iApply ltyped_val_ltyped.
    iApply ltyped_val_lam.
    iApply (ltyped_lam [EnvItem "f" _]).
    iApply (ltyped_lam [EnvItem "xs" _; EnvItem "f" _]).
    iIntros (vs) "!> HΓ /=".
    rewrite (lookup_delete_ne _ "n" "c")=> //.
    rewrite (lookup_delete_ne _ "n" "xs")=> //.
    rewrite (lookup_delete)=> //.
    iDestruct (env_ltyped_cons _ _ "c" with "HΓ") as (vc ->) "[Hc HΓ]".
    iDestruct (env_ltyped_cons _ _ "xs" with "HΓ") as (vl ->) "[Hl HΓ]".
    iDestruct (env_ltyped_cons _ _ "f" with "HΓ") as (vf ->) "[Hf HΓ]".
    wp_send with "[Hf//]".
    iDestruct (list_type_loc with "Hl") as %[l ->].
    wp_apply (llength_spec with "Hl").
    iIntros (xs n) "[<- Hl]".
    wp_pures.
    iDestruct (iProto_mapsto_le vc with "Hc []") as "Hc".
    { iApply (mapper_type_rec_client_unfold_app_n A B (length xs)). }
    wp_apply (send_all_spec_upfront with "[$Hl $Hc]").
    iIntros "[Hl Hc]".
    wp_apply (recv_all_spec with "[Hl $Hc //]").
    iIntros (ys). iDestruct 1 as (Hlen) "[Hl Hc]".
    rewrite /mapper_type_rec_client /lty_rec fixpoint_unfold.
    rewrite /select.
    wp_send with "[]"; first by eauto.
    wp_pures.
    iFrame.
    by iApply llist_lty_list.
  Qed.

  Lemma lty_le_mapper_type_client_dual :
    ⊢ lty_dual mapper_type_service <: mapper_type_client.
  Proof.
    rewrite /mapper_type_client /mapper_type_service.
    iApply lty_le_l; [ iApply lty_le_dual_recv_exist | ]=> /=.
    iIntros (A B). iExists A,B. iModIntro.
    iLöb as "IH".
    iApply lty_le_r; [ | iApply lty_bi_le_sym; iApply lty_le_rec_unfold ].
    iApply lty_le_dual_l.
    iApply lty_le_r; [ | iApply lty_bi_le_sym; iApply lty_le_rec_unfold ].
    iApply lty_le_l; [ iApply lty_le_dual_select | ].
    iApply lty_le_branch. rewrite fmap_insert fmap_insert fmap_empty.
    iApply big_sepM2_insert=> //.
    iSplit.
    - iApply lty_le_l; [ iApply lty_le_dual_send | ].
      iApply lty_le_recv; [ iApply lty_le_refl | ].
      iApply lty_le_l; [ iApply lty_le_dual_recv | ].
      iApply lty_le_send; [ iApply lty_le_refl | ].
      iIntros "!>!>!>". iApply lty_le_dual_l. iApply "IH".
    - iApply big_sepM2_insert=> //.
      iSplit=> //. iApply lty_le_l; [ iApply lty_le_dual_end | iApply lty_le_refl ].
  Qed.

  Section with_spawn.
    Context `{!spawnG Σ}.

    Lemma ltyped_mapper_prog A B e1 e2 Γ Γ' Γ'' :
      (Γ ⊨ e2 : lty_list A ⫤ Γ') -∗
      (Γ' ⊨ e1 : (A → B) ⫤ Γ'') -∗
      Γ ⊨ par_start (mapper_service) (mapper_client e1 e2) :
        (() * lty_list B) ⫤ Γ''.
    Proof.
      iIntros "He2 He1".
      iApply (ltyped_app with "[He2 He1]").
      { iApply (ltyped_app with "He2").
        iApply (ltyped_app with "He1").
        iApply ltyped_mapper_client_ad_hoc. }
      iApply ltyped_app.
      { iApply ltyped_mapper_service. }
      iApply ltyped_subsumption;
        [ iApply env_le_refl | | iApply env_le_refl | ].
      { iApply lty_le_arr; [ iApply lty_le_refl | ].
        iApply lty_le_arr; [ | iApply lty_le_refl ].
        iApply lty_le_arr; [ | iApply lty_le_refl ].
        iApply lty_le_chan.
        iApply lty_le_mapper_type_client_dual. }
      iApply ltyped_par_start.
    Qed.

  End with_spawn.

End mapper_example.
