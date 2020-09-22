(** This file defines all of the semantic typing lemmas for term types. Most of
these lemmas are semantic versions of the syntactic typing judgments typically
found in a syntactic type system. *)
From stdpp Require Import pretty.
From iris.bi.lib Require Import core.
From iris.heap_lang Require Import metatheory.
From iris.heap_lang.lib Require Export assert.
From actris.logrel Require Export term_typing_judgment term_types session_types.
From actris.utils Require Import switch.
From actris.channel Require Import proofmode.

Section session_typing_rules.
  Context `{!heapG Σ, !chanG Σ}.
  Implicit Types A B : ltty Σ.
  Implicit Types S T : lsty Σ.
  Implicit Types Γ : ctx Σ.

  Lemma ltyped_new_chan Γ S :
    Γ ⊨ new_chan : () ⊸ (chan S * chan (lty_dual S)) ⫤ Γ.
  Proof.
    iIntros (vs) "!> HΓ /=". iApply wp_value. iFrame "HΓ".
    iIntros (u) ">->".
    iApply (new_chan_spec with "[//]"); iIntros (c1 c2) "!> [Hp1 Hp2]".
    iExists c1, c2. by iFrame "Hp1 Hp2".
  Qed.

  Lemma ltyped_send Γ Γ' (x : string) e A S :
    Γ' !! x = Some (chan (<!!> TY A; S))%lty →
    (Γ ⊨ e : A ⫤ Γ') -∗
    (Γ ⊨ send x e : () ⫤ ctx_cons x (chan S) Γ').
  Proof.
    iIntros (HΓx%ctx_lookup_perm) "#He !>". iIntros (vs) "HΓ /=".
    wp_apply (wp_wand with "(He HΓ)"); iIntros (v) "[HA HΓ']".
    rewrite {2}HΓx /=.
    iDestruct (ctx_ltyped_cons with "HΓ'") as (c Hvs) "[Hc HΓ']". rewrite Hvs.
    wp_send with "[HA //]". iSplitR; [done|].
    iDestruct (ctx_ltyped_insert _ _ x (chan _) with "[Hc //] HΓ'") as "HΓ' /=".
    by rewrite  (insert_id vs).
 Qed.

  Lemma iProto_le_lmsg_texist {kt : ktele Σ} (m : ltys Σ kt → iMsg Σ) :
    ⊢ (<?> (∃.. Xs : ltys Σ kt, m Xs)%lmsg) ⊑ (<? (Xs : ltys Σ kt)> m Xs).
  Proof.
    iInduction kt as [|k kt] "IH".
    { rewrite /lty_msg_texist /=. by iExists LTysO. }
    rewrite /lty_msg_texist /=. iIntros (X).
    iApply (iProto_le_trans with "IH"). iIntros (Xs). by iExists (LTysS _ _).
  Qed.

  Lemma ltyped_recv_texist {kt} Γ1 Γ2 M x (xc : string) (e : expr)
      (A : kt -k> ltty Σ) (S : kt -k> lsty Σ) (B : ltty Σ) :
    Γ1 !! xc = Some (chan (<??> M))%lty →
    LtyMsgTele M A S →
    (∀ Ys,
      ctx_cons x (ktele_app A Ys) (ctx_cons xc (chan (ktele_app S Ys)) Γ1) ⊨ e : B ⫤ Γ2) -∗
    Γ1 ⊨ (let: x := recv xc in e) : B ⫤
          ctx_filter_eq x (ctx_filter_ne xc Γ1) ++ ctx_filter_ne x Γ2.
  Proof.
    rewrite /LtyMsgTele.
    iIntros (HΓxc%ctx_lookup_perm HM) "#He !>". iIntros (vs) "HΓ1 /=".
    rewrite {2}HΓxc /=.
    iDestruct (ctx_ltyped_cons with "HΓ1") as (c Hvs) "[Hc HΓ1]". rewrite Hvs.
    rewrite {2}(ctx_filter_eq_perm (ctx_filter_ne xc Γ1) x).
    iDestruct (ctx_ltyped_app with "HΓ1") as "[HΓ1eq HΓ1neq]".
    iAssert (c ↣ <? (Xs : ltys Σ kt) (v : val)>
      MSG v {{ ltty_car (ktele_app A Xs) v }};
        lsty_car (ktele_app S Xs)) with "[Hc]" as "Hc".
    { iApply (iProto_mapsto_le with "Hc"); iIntros "!>". rewrite HM.
      iApply iProto_le_lmsg_texist. }
    wp_recv (Xs v) as "HA". wp_pures. rewrite -subst_map_binder_insert.
    wp_apply (wp_wand with "(He [- HΓ1eq])").
    { iApply (ctx_ltyped_insert _ _ x with "HA").
      destruct (decide (x = xc)) as [->|].
      - by rewrite ctx_filter_ne_cons.
      - rewrite ctx_filter_ne_cons_ne //.
        iApply ctx_ltyped_cons. eauto with iFrame. }
    iIntros (w) "[$ HΓ]".
    iApply ctx_ltyped_app. iFrame "HΓ1eq". by iApply ctx_ltyped_delete.
  Qed.

  Lemma ltyped_recv Γ (x : string) A S :
    Γ !! x = Some (chan (<??> TY A; S))%lty →
    Γ ⊨ recv x : A ⫤ ctx_cons x (chan S) Γ.
  Proof.
    iIntros (HΓx%ctx_lookup_perm) "!>". iIntros (vs) "HΓ /=".
    rewrite {1}HΓx /=.
    iDestruct (ctx_ltyped_cons with "HΓ") as (c Hvs) "[Hc HΓ]". rewrite Hvs.
    wp_recv (v) as "HA". iFrame "HA". iApply ctx_ltyped_cons; eauto with iFrame.
  Qed.

  Definition select : val := λ: "c" "i", send "c" "i".

  Lemma ltyped_select Γ (x : string) (i : Z) (S : lsty Σ) Ss :
    Γ !! x = Some (chan (lty_select Ss))%lty →
    Ss !! i = Some S →
    Γ ⊨ select x #i : () ⫤ ctx_cons x (chan S) Γ.
  Proof.
    iIntros (HΓx%ctx_lookup_perm Hin); iIntros "!>" (vs) "HΓ /=".
    rewrite {1}HΓx /=.
    iDestruct (ctx_ltyped_cons with "HΓ") as (c Hvs) "[Hc HΓ]". rewrite Hvs.
    rewrite /select. wp_send with "[]"; [by eauto|]. iSplit; [done|].
    iDestruct (ctx_ltyped_insert _ _ x (chan _) with "[Hc //] HΓ") as "HΓ' /=".
    by rewrite insert_id // lookup_total_alt Hin.
  Qed.

  Fixpoint lty_arr_list (As : list (ltty Σ)) (B : ltty Σ) : ltty Σ :=
    match As with
    | [] => B
    | A :: As => A ⊸ lty_arr_list As B
    end.

  Lemma lty_arr_list_spec_step A As (e : expr) B ws y i :
    (∀ v, ltty_car A v -∗
      WP subst_map (<[y+:+pretty i:=v]> ws)
        (switch_lams y (S i) (length As) e) {{ ltty_car (lty_arr_list As B) }}) -∗
    WP subst_map ws (switch_lams y i (S (length As)) e)
      {{ ltty_car (lty_arr_list (A :: As) B) }}.
  Proof.
    iIntros "H". wp_pures. iIntros (v) "HA".
    iDestruct ("H" with "HA") as "H".
    rewrite subst_map_insert.
    wp_apply "H".
  Qed.

  Lemma lty_arr_list_spec As (e : expr) B ws y i n :
    n = length As →
    (∀ vs, ([∗ list] A;v ∈ As;vs, ltty_car A v) -∗
          WP subst_map (map_string_seq y i vs ∪ ws) e {{ ltty_car B }}) -∗
    WP subst_map ws (switch_lams y i n e) {{ ltty_car (lty_arr_list As B) }}.
  Proof.
    iIntros (Hlen) "H".
    iInduction As as [|A As] "IH" forall (ws i e n Hlen); simplify_eq/=.
    - iDestruct ("H" $! [] with "[$]") as "H"=> /=.
      by rewrite left_id_L.
    - iApply lty_arr_list_spec_step. iIntros (v) "HA".
      iApply ("IH" with "[//]"). iIntros (vs) "HAs".
      iSpecialize ("H" $! (v::vs)); simpl.
      do 2 rewrite insert_union_singleton_l.
      rewrite (map_union_comm ({[y +:+ pretty i := v]})); last first.
      { apply map_disjoint_singleton_l_2.
        apply lookup_map_string_seq_None_lt. eauto. }
      rewrite assoc_L. iApply ("H" with "[$HA $HAs]").
  Qed.

  Definition branch (xs : list Z) : val := λ: "c",
    switch_lams "f" 0 (length xs) $
    let: "y" := recv "c" in
    switch_body "y" 0 xs (assert: #false) $ λ i, ("f" +:+ pretty i) "c".

  Lemma ltyped_branch Γ Ss A xs :
    (∀ x, x ∈ xs ↔ is_Some (Ss !! x)) →
    Γ ⊨ branch xs : chan (lty_branch Ss) ⊸
        lty_arr_list ((λ x, (chan (Ss !!! x) ⊸ A)%lty) <$> xs) A ⫤ Γ.
  Proof.
    iIntros (Hdom) "!>". iIntros (vs) "$". iApply wp_value.
    iIntros (c) "Hc". wp_lam.
    rewrite -subst_map_singleton.
    iApply lty_arr_list_spec; [by rewrite fmap_length|].
    iIntros (ws) "H".
    rewrite big_sepL2_fmap_l.
    iDestruct (big_sepL2_length with "H") as %Heq.
    rewrite -insert_union_singleton_r; last by apply lookup_map_string_seq_None.
    rewrite /= lookup_insert.
    wp_recv (x) as "HPsx". iDestruct "HPsx" as %HPs_Some.
    wp_pures. rewrite -subst_map_insert.
    assert (x ∈ xs) as Hin by naive_solver.
    pose proof (list_find_elem_of (x =.) xs x) as [[n z] Hfind_Some]; [done..|].
    iApply switch_body_spec.
    { apply fmap_Some_2, Hfind_Some. }
    { by rewrite lookup_insert. }
    simplify_map_eq. rewrite lookup_map_string_seq_Some.
    assert (xs !! n = Some x) as Hxs_Some.
    { by apply list_find_Some in Hfind_Some as [? [-> _]]. }
    assert (is_Some (ws !! n)) as [w Hws_Some].
    { apply lookup_lt_is_Some_2. rewrite -Heq. eauto using lookup_lt_Some. }
    iDestruct (big_sepL2_lookup _ xs ws n with "H") as "HA"; [done..|].
    rewrite Hws_Some. by iApply "HA".
  Qed.
End session_typing_rules.
