From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From osiris.utils Require Import list compare spin_lock contribution.
From iris.algebra Require Import gmultiset.

Definition mapper : val :=
  rec: "go" "f" "l" "c" :=
    acquire "l";;
      send "c" #true;;
      if: ~recv "c" then release "l" else
      let: "x" := recv "c" in
    release "l";;
      let: "y" := "f" "x" in
    acquire "l";;
      send "c" #false;;
      send "c" "y";;
    release "l";;
    "go" "f" "l" "c".

Definition start_mappers : val :=
  rec: "go" "n" "f" "l" "c" :=
    if: "n" = #0 then #() else
    Fork (mapper "f" "l" "c");;
    "go" ("n" - #1) "f" "l" "c".

Definition mapper_service_loop : val :=
  rec: "go" "n" "c" "xs" "ys" :=
    if: "n" = #0 then "ys" else
    if: recv "c" then
      if: lisnil "xs" then
        send "c" #false;;
        "go" ("n" - #1) "c" "xs" "ys"
      else
        send "c" #true;;
        send "c" (lhead "xs");;
        "go" "n" "c" (ltail "xs") "ys"
    else
      let: "y" := recv "c" in
      "go" "n" "c" "xs" (lcons "y" "ys").

Definition mapper_service : val := λ: "n" "f" "xs",
  let: "l" := new_lock #() in
  let: "c" := start_chan (λ: "c",
    start_mappers "n" "f" "l" "c") in
  mapper_service_loop "n" "c" "xs" (lnil #()).

Class mapperG Σ A `{Countable A} := {
  mapper_contributionG :> contributionG Σ (gmultisetUR A);
  mapper_lockG :> lockG Σ;
}.

Section mapper.
  Context `{Countable A, Countable B}.
  Context `{!heapG Σ, !proto_chanG Σ, mapperG Σ A} (N : namespace).
  Context (IA : A → val → iProp Σ) (IB : B → val → iProp Σ) (f : A → B).
  Local Open Scope nat_scope.

  Definition mapper_protocol_aux (rec : nat -d> gmultiset A -d> iProto Σ) :
      nat -d> gmultiset A -d> iProto Σ := λ i X,
    let rec : nat → gmultiset A → iProto Σ := rec in
    (if i is 0 then END else
     ((<!> x v, MSG v {{ IA x v }}; rec i (X ⊎ {[ x ]}))
        <+>
      rec (pred i) X
     ) <{⌜ i ≠ 1 ∨ X = ∅ ⌝}&>
         <?> x w, MSG w {{ ⌜ x ∈ X ⌝ ∧ IB (f x) w }}; rec i (X ∖ {[ x ]}))%proto.
  Instance mapper_protocol_aux_contractive : Contractive mapper_protocol_aux.
  Proof. solve_proper_prepare. f_equiv. solve_proto_contractive. Qed.
  Definition mapper_protocol := fixpoint mapper_protocol_aux.
  Global Instance mapper_protocol_unfold n X :
    ProtoUnfold (mapper_protocol n X) (mapper_protocol_aux mapper_protocol n X).
  Proof. apply proto_unfold_eq, (fixpoint_unfold mapper_protocol_aux). Qed.

  Definition mapper_lock_inv (γ : gname) (c : val) : iProp Σ :=
    (∃ i X, server γ i X ∗ c ↣ iProto_dual (mapper_protocol i X) @ N)%I.

  Lemma mapper_spec γ (ff : val) lk c q :
    (∀ x v, {{{ IA x v }}} ff v {{{ w, RET w; IB (f x) w }}}) -∗
    {{{ is_lock N lk (mapper_lock_inv γ c) ∗
        unlocked N lk q ∗ client γ (∅ : gmultiset A) }}}
      mapper ff #lk c
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hf !>" (Φ) "(#Hlk & Hu & Hγ) HΦ". iLöb as "IH".
    wp_rec; wp_pures.
    wp_apply (acquire_spec with "[$Hlk $Hu]"); iIntros "[Hl H]".
    iDestruct "H" as (i X) "[Hs Hc]".
    iDestruct (@server_agree with "Hs Hγ") as %[??]; destruct i as [|i]=>//=.
    iAssert ⌜ S i ≠ 1 ∨ X = ∅ ⌝%I as %?.
    { destruct i as [|i]; last auto with lia.
      iDestruct (@server_1_agree with "Hs Hγ") as %?%leibniz_equiv; auto. }
    wp_select. wp_branch; wp_pures; last first.
    { iMod (@dealloc_client with "Hs Hγ") as "Hs /=".
      wp_apply (release_spec with "[$Hlk $Hl Hc Hs]").
      { iExists i, _. iFrame. }
      iIntros "_". by iApply "HΦ". }
    wp_recv (x v) as "HI".
    iMod (@update_client with "Hs Hγ") as "[Hs Hγ]".
    { apply (gmultiset_local_update_alloc _ _ {[ x ]}). }
    rewrite left_id_L.
    wp_apply (release_spec with "[$Hlk $Hl Hc Hs]").
    { iExists (S i), _. iFrame. }
    clear dependent i X. iIntros "Hu". wp_apply ("Hf" with "HI"); iIntros (w) "HI".
    wp_apply (acquire_spec with "[$Hlk $Hu]"); iIntros "[Hl H]".
    iDestruct "H" as (i X) "[Hs Hc]".
    iDestruct (@server_agree with "Hs Hγ")
      as %[??%gmultiset_included]; destruct i as [|i]=>//=.
    wp_select. wp_send with "[$HI]".
    { by rewrite gmultiset_elem_of_singleton_subseteq. }
    iMod (@update_client with "Hs Hγ") as "[Hs Hγ]".
    { by apply (gmultiset_local_update_dealloc _ _ {[ x ]}). }
    rewrite gmultiset_difference_diag.
    wp_apply (release_spec with "[$Hlk $Hl Hc Hs]").
    { iExists (S i), _. iFrame. }
    iIntros "Hu". by wp_apply ("IH" with "[$] [$]").
  Qed.

  Lemma start_mappers_spec γ (n : nat) (ff : val) lk c q :
    (∀ x v, {{{ IA x v }}} ff v {{{ w, RET w; IB (f x) w }}}) -∗
    {{{ is_lock N lk (mapper_lock_inv γ c) ∗ unlocked N lk q ∗
        n * client γ (∅:gmultiset A) }}}
      start_mappers #n ff #lk c
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hf !>" (Φ) "(#Hlk & Hu & Hγs) HΦ".
    iInduction n as [|n] "IH" forall (q); wp_rec; wp_pures; simpl.
    { by iApply "HΦ". }
    iDestruct "Hγs" as "[Hγ Hγs]"; iDestruct "Hu" as "[Hu Hu']".
    wp_apply (wp_fork with "[Hγ Hu]").
    { iNext. wp_apply (mapper_spec with "Hf [$]"); auto. }
    wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply ("IH" with "[$] [$] [$]").
  Qed.

  Lemma mapper_service_loop_spec (n : nat) c vs xs ws X_send xs_recv :
    (n = 0 → X_send = ∅ ∧ xs = []) →
    {{{
      c ↣ mapper_protocol n (X_send : gmultiset A) @ N ∗
      ([∗ list] x;v ∈ xs;vs, IA x v) ∗ ([∗ list] x;w ∈ xs_recv;ws, IB (f x) w)
    }}}
      mapper_service_loop #n c (val_encode vs) (val_encode ws)
    {{{ ys ws, RET (val_encode ws);
       ⌜ys ≡ₚ f <$> elements X_send ++ xs⌝ ∗
       [∗ list] y;w ∈ ys ++ (f <$> xs_recv);ws, IB y w
    }}}.
  Proof.
    iIntros (Hn Φ) "(Hc & HIA & HIB) HΦ".
    iLöb as "IH" forall (n vs xs ws X_send xs_recv Hn Φ); wp_rec; wp_pures; simpl.
    case_bool_decide; wp_pures; simplify_eq/=.
    { destruct Hn as [-> ->]; first lia.
      iApply ("HΦ" $! []); simpl. rewrite big_sepL2_fmap_l. auto. }
    destruct n as [|n]=> //=. wp_branch as %?|%_; wp_pures.
    - wp_apply (lisnil_spec (A:=val) with "[//]"); iIntros (_).
      destruct vs as [|v vs], xs as [|x xs]; csimpl; try done; wp_pures.
      + wp_select. wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
        iApply ("IH" with "[] Hc [//] [$] HΦ"). iPureIntro; naive_solver.
      + iDestruct "HIA" as "[HIAx HIA]". wp_select.
        wp_apply (lhead_spec (A:=val) with "[//]"); iIntros (_).
        wp_send with "[$HIAx]".
        wp_apply (ltail_spec (A:=val) with "[//]"); iIntros (_).
        wp_apply ("IH" with "[] Hc HIA HIB"); first done.
        iIntros (ys ws').
        rewrite gmultiset_elements_disj_union gmultiset_elements_singleton -!assoc_L.
        iApply "HΦ".
    - wp_recv (x w) as (HH) "HIBfx".
      wp_apply (lcons_spec (A:=val) with "[//]"); iIntros (_).
      wp_apply ("IH" $! _ _ _ _ _ (_ :: _) with "[] Hc HIA [HIBfx HIB]"); first done.
      { simpl; iFrame. }
      iIntros (ys ws'); iDestruct 1 as (Hys) "HIB"; simplify_eq/=.
      iApply ("HΦ" $! (ys ++ [f x])). iSplit.
      + iPureIntro. rewrite (gmultiset_disj_union_difference {[ x ]} X_send)
          -?gmultiset_elem_of_singleton_subseteq //.
        rewrite (comm disj_union) gmultiset_elements_disj_union.
        rewrite gmultiset_elements_singleton -assoc_L (comm _ [x]) assoc_L.
        by rewrite fmap_app -Hys.
      + by rewrite -assoc_L.
  Qed.

  Lemma mapper_service_spec (n : nat) (ff : val) vs xs :
    0 < n →
    (∀ x v, {{{ IA x v }}} ff v {{{ w, RET w; IB (f x) w }}}) -∗
    {{{ [∗ list] x;v ∈ xs;vs, IA x v }}}
      mapper_service #n ff (val_encode vs)
    {{{ ys ws, RET (val_encode ws); ⌜ys ≡ₚ f <$> xs⌝ ∗
                                    [∗ list] y;w ∈ ys;ws, IB y w }}}.
  Proof.
    iIntros (?) "#Hf !>"; iIntros (Φ) "HI HΦ". wp_lam; wp_pures.
    wp_apply (new_lock_spec N with "[//]"); iIntros (lk) "[Hu Hlk]".
    wp_apply (start_chan_proto_spec N (mapper_protocol n ∅) with "[Hu Hlk]");
      try iNext; iIntros (c) "Hc".
    { wp_lam.
      iMod (contribution_initN (A:=gmultisetUR A) n) as (γ) "[Hs Hγs]".
      iMod ("Hlk" $! (mapper_lock_inv γ c) with "[Hc Hs]") as "#Hlk".
      { iExists n, ∅. iFrame. }
      wp_apply (start_mappers_spec with "Hf [$Hlk $Hu $Hγs]"); auto. }
    wp_pures. wp_apply (lnil_spec with "[//]"); iIntros (_).
    wp_apply (mapper_service_loop_spec _ _ _ _ [] ∅ [] with "[$Hc $HI //]"); first lia.
    iIntros (ys ws). rewrite /= !right_id_L gmultiset_elements_empty. iApply "HΦ".
  Qed.
End mapper.
