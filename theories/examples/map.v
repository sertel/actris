From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation lib.spin_lock.
From actris.utils Require Import llist contribution.
From iris.algebra Require Import gmultiset.

Definition map_worker : val :=
  rec: "go" "map" "l" "c" :=
    acquire "l";;
      send "c" #true;;
      if: ~recv "c" then release "l" else
      let: "x" := recv "c" in
    release "l";;
      let: "y" := "map" "x" in
    acquire "l";;
      send "c" #false;;
      send "c" "y";;
    release "l";;
    "go" "map" "l" "c".

Definition start_map_workers : val :=
  rec: "go" "n" "map" "l" "c" :=
    if: "n" = #0 then #() else
    Fork (map_worker "map" "l" "c");;
    "go" ("n" - #1) "map" "l" "c".

Definition start_map_service : val := λ: "n" "map",
  start_chan (λ: "c",
    let: "l" := newlock #() in
    start_map_workers "n" "map" "l" "c").

Definition par_map_server : val :=
  rec: "go" "n" "c" "xs" "ys" :=
    if: "n" = #0 then #() else
    if: recv "c" then (* send item to map_worker *)
      if: lisnil "xs" then
        send "c" #false;;
        "go" ("n" - #1) "c" "xs" "ys"
      else
        send "c" #true;;
        send "c" (lpop "xs");;
        "go" "n" "c" "xs" "ys"
    else (* receive item from map_worker *)
      let: "zs" := recv "c" in
      lprep "ys" "zs";;
      "go" "n" "c" "xs" "ys".

Definition par_map : val := λ: "n" "map" "xs",
  let: "c" := start_map_service "n" "map" in
  let: "ys" := lnil #() in
  par_map_server "n" "c" "xs" "ys";;
  "ys".

Class mapG Σ A `{Countable A} := {
  map_contributionG :> contributionG Σ (gmultisetUR A);
  map_lockG :> lockG Σ;
}.

Section map.
  Context `{Countable A} {B : Type}.
  Context `{!heapG Σ, !proto_chanG Σ, !mapG Σ A} (N : namespace).
  Context (IA : A → val → iProp Σ) (IB : B → val → iProp Σ) (map : A → list B).
  Local Open Scope nat_scope.
  Implicit Types n : nat.

  Definition map_spec (vmap : val) : iProp Σ := (∀ x v,
    {{{ IA x v }}}
      vmap v
    {{{ l ws, RET #l; llist l ws ∗ [∗ list] y;w ∈ map x;ws, IB y w }}})%I.

  Definition map_worker_protocol_aux (rec : nat -d> gmultiset A -d> iProto Σ) :
      nat -d> gmultiset A -d> iProto Σ := λ i X,
    let rec : nat → gmultiset A → iProto Σ := rec in
    (if i is 0 then END else
     ((<!> x v, MSG v {{ IA x v }}; rec i (X ⊎ {[ x ]}))
        <+>
      rec (pred i) X
     ) <{⌜ i ≠ 1 ∨ X = ∅ ⌝}&>
         <?> x (l : loc) ws, MSG #l {{ ⌜ x ∈ X ⌝ ∗ llist l ws ∗ [∗ list] y;w ∈ map x;ws, IB y w }};
         rec i (X ∖ {[ x ]}))%proto.
  Instance map_worker_protocol_aux_contractive : Contractive map_worker_protocol_aux.
  Proof. solve_proper_prepare. f_equiv. solve_proto_contractive. Qed.
  Definition map_worker_protocol := fixpoint map_worker_protocol_aux.
  Global Instance map_worker_protocol_unfold n X :
    ProtoUnfold (map_worker_protocol n X) (map_worker_protocol_aux map_worker_protocol n X).
  Proof. apply proto_unfold_eq, (fixpoint_unfold map_worker_protocol_aux). Qed.

  Definition map_worker_lock_inv (γ : gname) (c : val) : iProp Σ :=
    (∃ i X, server γ i X ∗ c ↣ iProto_dual (map_worker_protocol i X) @ N)%I.

  Lemma map_worker_spec γl γ vmap lk c :
    map_spec vmap -∗
    {{{ is_lock N γl lk (map_worker_lock_inv γ c) ∗ client γ (∅ : gmultiset A) }}}
      map_worker vmap lk c
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hmap !>" (Φ) "[#Hlk Hγ] HΦ". iLöb as "IH".
    wp_rec; wp_pures.
    wp_apply (acquire_spec with "Hlk"); iIntros "[Hl H]".
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
    clear dependent i X. iIntros "Hu". wp_apply ("Hmap" with "HI"); iIntros (l ws) "HI".
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

  Lemma start_map_workers_spec γl γ n vmap lk c :
    map_spec vmap -∗
    {{{ is_lock N γl lk (map_worker_lock_inv γ c) ∗ client γ (∅:gmultiset A) ^ n }}}
      start_map_workers #n vmap lk c
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hmap !>" (Φ) "[#Hlk Hγs] HΦ".
    iInduction n as [|n] "IH"; wp_rec; wp_pures; simpl.
    { by iApply "HΦ". }
    iDestruct "Hγs" as "[Hγ Hγs]".
    wp_apply (wp_fork with "[Hγ]").
    { iNext. wp_apply (map_worker_spec with "Hmap [$]"); auto. }
    wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply ("IH" with "[$] [$]").
  Qed.

  Lemma start_map_service_spec n vmap :
    map_spec vmap -∗
    {{{ True }}}
      start_map_service #n vmap
    {{{ c, RET c; c ↣ map_worker_protocol n ∅ @ N }}}.
  Proof.
    iIntros "#Hf !>"; iIntros (Φ _) "HΦ". wp_lam; wp_pures.
    wp_apply (start_chan_proto_spec N (map_worker_protocol n ∅)); iIntros (c) "// Hc".
    wp_lam.
    iMod (contribution_init_pow (A:=gmultisetUR A) n) as (γ) "[Hs Hγs]".
    wp_apply (newlock_spec N (map_worker_lock_inv γ c) with "[Hc Hs]").
    { iExists n, ∅. iFrame. }
    iIntros (lk γl) "#Hlk".
    wp_apply (start_map_workers_spec with "Hf [$Hlk $Hγs]"); auto.
  Qed.

  Lemma par_map_server_spec n c l k vs xs ws X ys :
    (n = 0 → X = ∅ ∧ xs = []) →
    {{{
      llist l vs ∗ llist k ws ∗
      c ↣ map_worker_protocol n X @ N ∗
      ([∗ list] x;v ∈ xs;vs, IA x v) ∗ ([∗ list] y;w ∈ ys;ws, IB y w)
    }}}
      par_map_server #n c #l #k
    {{{ ys' ws', RET #();
       ⌜ys' ≡ₚ (xs ++ elements X) ≫= map⌝ ∗
       llist k ws' ∗ [∗ list] y;w ∈ ys' ++ ys;ws', IB y w
    }}}.
  Proof.
    iIntros (Hn Φ) "(Hl & Hk & Hc & HIA & HIB) HΦ".
    iLöb as "IH" forall (n l vs xs ws X ys Hn Φ); wp_rec; wp_pures; simpl.
    case_bool_decide; wp_pures; simplify_eq/=.
    { destruct Hn as [-> ->]; first lia.
      iApply ("HΦ" $! []); simpl; auto with iFrame. }
    destruct n as [|n]=> //=. wp_branch as %?|%_; wp_pures.
    - wp_apply (lisnil_spec with "Hl"); iIntros "Hl".
      destruct vs as [|v vs], xs as [|x xs]; csimpl; try done; wp_pures.
      + wp_select. wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
        iApply ("IH" with "[%] Hl Hk Hc [//] [$] HΦ"); naive_solver.
      + iDestruct "HIA" as "[HIAx HIA]". wp_select.
        wp_apply (lpop_spec with "Hl"); iIntros "Hl".
        wp_send with "[$HIAx]".
        wp_apply ("IH" with "[] Hl Hk Hc HIA HIB"); first done.
        iIntros (ys' ws').
        rewrite gmultiset_elements_disj_union gmultiset_elements_singleton.
        rewrite assoc_L -(comm _ [x]). iApply "HΦ".
    - wp_recv (x l' w) as (Hx) "[Hl' HIBx]".
      wp_apply (lprep_spec with "[$Hk $Hl']"); iIntros "[Hk _]".
      wp_apply ("IH" $! _ _ _ _ _ _ (_ ++ _) with "[] Hl Hk Hc HIA [HIBx HIB]"); first done.
      { simpl; iFrame. }
      iIntros (ys' ws'); iDestruct 1 as (Hys) "HIB"; simplify_eq/=.
      iApply ("HΦ" $! (ys' ++ map x)). iSplit.
      + iPureIntro. rewrite (gmultiset_disj_union_difference {[ x ]} X)
          -?gmultiset_elem_of_singleton_subseteq //.
        rewrite (comm disj_union) gmultiset_elements_disj_union.
        by rewrite gmultiset_elements_singleton assoc_L bind_app -Hys /= right_id_L.
      + by rewrite -assoc_L.
  Qed.

  Lemma par_map_spec n vmap l vs xs :
    0 < n →
    map_spec vmap -∗
    {{{ llist l vs ∗ [∗ list] x;v ∈ xs;vs, IA x v }}}
      par_map #n vmap #l
    {{{ k ys ws, RET #k; ⌜ys ≡ₚ xs ≫= map⌝ ∗ llist k ws ∗ [∗ list] y;w ∈ ys;ws, IB y w }}}.
  Proof.
    iIntros (?) "#Hmap !>"; iIntros (Φ) "[Hl HI] HΦ". wp_lam; wp_pures.
    wp_apply (start_map_service_spec with "Hmap [//]"); iIntros (c) "Hc".
    wp_pures. wp_apply (lnil_spec with "[//]"); iIntros (k) "Hk".
    wp_apply (par_map_server_spec _ _ _ _ _ _ [] ∅ [] with "[$Hl $Hk $Hc $HI //]"); first lia.
    iIntros (ys ws) "H". rewrite /= gmultiset_elements_empty !right_id_L .
    wp_pures. by iApply "HΦ".
  Qed.
End map.
