From actris.channel Require Import proofmode proto channel.
From iris.proofmode Require Import tactics.
From actris.utils Require Import llist.
From iris.heap_lang Require Import notation.
From actris.examples Require Import sort_fg.

Definition cont := true.
Definition stop := false.

Definition swap_mapper_service : val :=
  rec: "go" "f" "c" :=
    if: ~recv "c" then #()
    else send "c" ("f" (recv "c"));; "go" "f" "c".

Definition send_all : val :=
  rec: "go" "c" "xs" :=
    if: lisnil "xs" then #() else
    send "c" #cont;; send "c" (lpop "xs");; "go" "c" "xs".

Definition recv_all : val :=
  rec: "go" "c" "ys" "n" :=
    if: "n" = #0 then #() else
    let: "x" := recv "c" in
    "go" "c" "ys" ("n"-#1);; lcons "x" "ys".

Definition swap_mapper_client : val :=
  λ: "f" "xs",
    let: "c" := start_chan (λ: "c", swap_mapper_service "f" "c") in
    let: "n" := llength "xs" in
    send_all "c" "xs";; recv_all "c" "xs" "n";; send "c" #false.

Section with_Σ.
  Context `{heapG Σ, chanG Σ}.
  Context {T U : Type}.
  Context (IT : T → val → iProp Σ).
  Context (IU : U → val → iProp Σ).
  Context (f : T → U).

  Definition mapper_prot_aux (rec : iProto Σ) : iProto Σ :=
    ((<! (x : T) (v : val)> MSG v {{ IT x v }};
     <? (w : val)> MSG w {{ IU (f x) w }}; rec) <+> END)%proto.

  Instance mapper_prot_aux_contractive : Contractive mapper_prot_aux.
  Proof. solve_proto_contractive. Qed.

  Definition mapper_prot := fixpoint mapper_prot_aux.

  Global Instance mapper_prot_unfold :
    ProtoUnfold (mapper_prot) (mapper_prot_aux mapper_prot).
  Proof. apply proto_unfold_eq, (fixpoint_unfold mapper_prot_aux). Qed.

  Definition send_once prot :=
    (<!> MSG (LitV $ true);
     <! (x : T) (v : val)> MSG v {{ IT x v }};
     prot x)%proto.

  Definition recv_once prot x :=
    (<? (w : val)> MSG w {{ IU (f x) w }};
     prot)%proto.

  Definition map_once prot :=
    (send_once $ recv_once $ prot).

  Lemma send_once_mono prot1 prot2 :
    ▷ (∀ x, prot1 x ⊑ prot2 x) -∗ send_once prot1 ⊑ send_once prot2.
  Proof.
    iIntros "Hsub".
    iModIntro.
    iIntros (x v) "Hv". iExists x, v. iFrame "Hv". iModIntro.
    iApply "Hsub".
  Qed.

  Global Instance send_once_from_modal p1 p2 :
    FromModal (modality_instances.modality_laterN 1) (∀ x, p1 x ⊑ p2 x)
              ((send_once p1) ⊑ (send_once p2)) (∀ x, p1 x ⊑ p2 x).
  Proof. apply send_once_mono. Qed.

  Lemma recv_once_mono prot1 prot2 x :
    ▷ (prot1 ⊑ prot2) -∗ recv_once prot1 x ⊑ recv_once prot2 x.
  Proof.
    iIntros "Hsub".
    iIntros (w) "Hw". iExists w. iFrame "Hw". iModIntro.
    iApply "Hsub".
  Qed.

  Global Instance recv_once_from_modal p1 p2 x :
    FromModal (modality_instances.modality_laterN 1) (p1 ⊑ p2)
              ((recv_once p1 x) ⊑ (recv_once p2 x)) (p1 ⊑ p2).
  Proof. apply recv_once_mono. Qed.

  Lemma map_once_mono prot1 prot2 :
    ▷ (prot1 ⊑ prot2) -∗ map_once prot1 ⊑ map_once prot2.
  Proof. iIntros "Hsub". iModIntro. iIntros (x). iModIntro. eauto. Qed.

  Global Instance map_once_from_modal p1 p2 :
    FromModal (modality_instances.modality_laterN 1) (p1 ⊑ p2)
              ((map_once p1) ⊑ (map_once p2)) (p1 ⊑ p2).
  Proof. apply map_once_mono. Qed.

  Definition mapper_prot_once :=
    (map_once mapper_prot)%proto.

  Lemma subprot_once :
    ⊢ mapper_prot ⊑ mapper_prot_once.
  Proof.
    rewrite /mapper_prot /mapper_prot_once.
    rewrite fixpoint_unfold /mapper_prot_aux.
    rewrite /iProto_choice.
    iExists true.
    iModIntro.
    iApply iProto_le_refl.
  Qed.

  Definition mapper_prot_twice :=
    map_once $ map_once $ mapper_prot.

  Lemma subprot_twice :
    ⊢ mapper_prot ⊑ mapper_prot_twice.
  Proof.
    iApply iProto_le_trans.
    { iApply subprot_once. }
    iModIntro.
    iApply subprot_once.
  Qed.

  Definition mapper_prot_twice_swap :=
    (<!> MSG (LitV $ true);
     <! (x1 : T) (v1 : val)> MSG v1 {{ IT x1 v1 }};
     <!> MSG (LitV $ true);
     <! (x2 : T) (v2 : val)> MSG v2 {{ IT x2 v2 }};
     <? (w1 : val)> MSG w1 {{ IU (f x1) w1 }};
     <? (w2 : val)> MSG w2 {{ IU (f x2) w2 }};
     mapper_prot)%proto.

  Lemma subprot_twice_swap :
    ⊢ mapper_prot ⊑ mapper_prot_twice_swap.
  Proof.
    iApply iProto_le_trans.
    { iApply subprot_twice. }
    iModIntro. iIntros (x1).
    iIntros (w1) "Hw1".
    iApply iProto_le_trans.
    { iApply iProto_le_base_swap. }
    iModIntro.
    iIntros (x2 v2) "Hv2".
    iApply (iProto_le_trans with "[Hv2]").
    { iModIntro. iExists x2, v2. iFrame "Hv2". iApply iProto_le_refl. }
    iApply iProto_le_trans.
    { iApply iProto_le_base_swap. }
    iModIntro.
    iExists (w1). iFrame "Hw1". iModIntro.
    iApply iProto_le_refl.
  Qed.

  Definition mapper_prot_twice_swap_end :=
    (<!> MSG (LitV $ true);
     <! (x1 : T) (v1 : val)> MSG v1 {{ IT x1 v1 }};
     <!> MSG (LitV $ true);
     <! (x2 : T) (v2 : val)> MSG v2 {{ IT x2 v2 }};
     <!> MSG (LitV $ false);
     <? (w1 : val)> MSG w1 {{ IU (f x1) w1 }};
     <? (w2 : val)> MSG w2 {{ IU (f x2) w2 }};
     END)%proto.

  Lemma subprot_twice_swap_end :
    ⊢ mapper_prot ⊑ mapper_prot_twice_swap_end.
  Proof.
    iApply iProto_le_trans.
    { iApply subprot_twice_swap. }
    rewrite /mapper_prot_twice_swap /mapper_prot_twice_swap_end.
    iIntros "!>" (x1).
    iIntros "!>" (x2).
    iApply iProto_le_trans.
    { iModIntro. iModIntro.
      rewrite /mapper_prot fixpoint_unfold /mapper_prot_aux /iProto_choice.
      iExists false. iApply iProto_le_refl. }
    iApply iProto_le_trans.
    { iModIntro.
      iIntros (w2) "Hw2".
      iApply iProto_le_trans.
      { iApply iProto_le_base_swap. }
      iModIntro. iExists w2. iSplitL. iExact "Hw2". iApply iProto_le_refl. }
    iIntros (w1) "Hw1".
    iApply iProto_le_trans.
    { iApply iProto_le_base_swap. }
    iModIntro. iExists w1. iSplitL. iExact "Hw1". iApply iProto_le_refl.
  Qed.

  Fixpoint mapper_prot_n n prot : iProto Σ :=
    match n with
    | O   => prot
    | S n => (<!> MSG (LitV $ true);
              <! (x : T) (v : val)> MSG v {{ IT x v }};
              <? (w : val)> MSG w {{ IU (f x) w }}; mapper_prot_n n prot)%proto
    end.

  Lemma subprot_n n :
    ⊢ mapper_prot ⊑ mapper_prot_n n mapper_prot.
  Proof.
    iInduction n as [|n] "IH"=> //.
    simpl.
    iApply (iProto_le_trans).
    { iApply subprot_once. }
    rewrite /mapper_prot_once.
    iModIntro. iApply "IH".
  Qed.

  Fixpoint send_all_prot n xs prot :=
    match n with
    | O   => prot (rev xs)
    | S n => (<!> MSG (LitV $ true);
              <! (x : T) (v : val)> MSG v {{ IT x v }};
              send_all_prot n (x::xs) prot)%proto
    end.

  Lemma send_all_spec c l xs xs' prot :
    {{{ llist IT l xs ∗ c ↣ send_all_prot (length xs) xs' prot }}}
      send_all c #l
    {{{ RET #(); llist IT l [] ∗ c ↣ prot (rev (rev xs ++ xs')) }}}.
  Proof.
    iIntros (Φ) "[Hl Hc] HΦ".
    iInduction xs as [|x xs] "IH" forall (xs').
    { wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl"; wp_pures.
      iApply "HΦ". by iFrame. }
    wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl".
    wp_send with "[//]".
    wp_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
    wp_send with "[$HIx]". wp_apply ("IH" with "Hl Hc"). simpl.
    by rewrite -assoc_L.
  Qed.

  Fixpoint recv_all_prot xs prot :=
    match xs with
    | [] => prot
    | x::xs => (<? (w : val)> MSG w {{ IU (f x) w }};
               recv_all_prot xs prot)%proto
  end.

  Lemma recv_all_spec c p l xs :
    {{{ llist IU l [] ∗ c ↣ recv_all_prot xs p }}}
      swap_mapper.recv_all c #l #(length xs)
    {{{ ys, RET #(); ⌜ys = (map f xs)⌝ ∗ llist IU l ys ∗ c ↣ p }}}.
  Proof.
    iIntros (Φ) "[Hl Hc] HΦ".
    iLöb as "IH" forall (xs Φ).
    destruct xs.
    { wp_lam. wp_pures. iApply ("HΦ" $![]). simpl. by iFrame. }
    wp_lam. wp_recv (w) as "Hw". wp_pures.
    rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat (length xs)) - 1)%Z with (Z.of_nat (length xs)) by lia.
    wp_apply ("IH" with "Hl Hc").
    iIntros (ys) "(% & Hl & Hc)".
    wp_apply (lcons_spec with "[$Hl $Hw]").
    iIntros "Hl". iApply "HΦ". iFrame. iPureIntro. by f_equiv.
  Qed.

  Lemma recv_all_prot_mono prot1 prot2 xs :
    prot1 ⊑ prot2 -∗ recv_all_prot xs prot1 ⊑ recv_all_prot xs prot2.
  Proof.
    iIntros "Hsub".
    iInduction xs as [|xs] "IHxs"=> //.
    iIntros (w) "Hw". iExists w. iFrame "Hw". iModIntro.
    by iApply "IHxs".
  Qed.

  Lemma recv_all_prot_fwd xs v prot :
    ⊢ recv_all_prot xs (<!> MSG v ; prot)%proto ⊑
      (<!> MSG v ; recv_all_prot xs prot)%proto.
  Proof.
    iInduction xs as [|x xs] "IH"=> //=.
    iIntros (w) "Hw".
    iApply (iProto_le_trans _ (<!> MSG v; <?> MSG w ;_)%proto); last first.
    { iModIntro. iExists w. iFrame "Hw". eauto. }
    iApply iProto_le_trans; last first.
    { iApply iProto_le_base_swap. }
    iModIntro. iApply "IH".
  Qed.

  Definition mapper_prot_n_swap n xs prot :=
    send_all_prot n xs (λ xs, recv_all_prot xs prot).

  Lemma subprot_n_n_swap n xs prot :
    ⊢ (recv_all_prot xs (mapper_prot_n n prot)) ⊑ mapper_prot_n_swap n (rev xs) prot.
  Proof.
    iInduction n as [|n] "IHn" forall (xs) => //=.
    - iInduction xs as [|x xs] "IHxs"=> //=.
      rewrite /mapper_prot_n_swap /send_all_prot.
      rewrite rev_unit /= rev_involutive.
      iIntros (w1) "Hw1". iExists w1. iFrame "Hw1". iModIntro. iApply "IHxs".
    - iApply iProto_le_trans.
      { iApply recv_all_prot_fwd. }
      iApply (iProto_le_trans _
              (<!> MSG LitV $ true ; <! (x : T) (v : val)> MSG v {{ IT x v }};
               recv_all_prot xs (<? (w : val)> MSG w {{
     IU (f x) w }}; mapper_prot_n n prot))%proto).
      { iModIntro.
        iInduction xs as [|x xs] "IHxs"=> //.
        iIntros (w) "Hw".
        iApply iProto_le_trans.
        { iModIntro. iApply "IHxs". }
        iIntros (y v) "Hv".
        iApply (iProto_le_trans with "[Hv]").
        { iModIntro. iExists y,v. iFrame "Hv". eauto. }
        iApply (iProto_le_trans).
        { iApply iProto_le_base_swap. }
        iModIntro. iExists w. iFrame "Hw". eauto. }
      iIntros "!>" (x).
      rewrite -(rev_unit xs x).
      iApply (iProto_le_trans); last first.
      { iApply "IHn". }
      iInduction xs as [|y xs] "IHxs"=> //=.
      iIntros (w) "Hw". iExists w. iFrame "Hw". iModIntro.
      iApply "IHxs".
  Qed.

  Lemma subprot_n_swap n :
    ⊢ mapper_prot ⊑ mapper_prot_n_swap n [] mapper_prot.
  Proof.
    iApply iProto_le_trans.
    { iApply (subprot_n n). }
    iInduction n as [|n] "IHn"=> //=.
    iIntros "!>" (x).
    iApply (subprot_n_n_swap n [x]).
  Qed.

  Definition mapper_prot_n_swap_fwd n xs prot :=
    send_all_prot n xs
                  (λ xs, (<!> MSG LitV $ false; recv_all_prot xs prot))%proto.

  Lemma subprot_n_swap_n_swap_end n xs :
    ⊢ mapper_prot_n_swap n xs mapper_prot ⊑ mapper_prot_n_swap_fwd n xs END%proto.
  Proof.
    iInduction n as [|n] "IHn" forall (xs)=> /=.
    - iApply iProto_le_trans.
      { iApply recv_all_prot_mono.
        rewrite /mapper_prot fixpoint_unfold /mapper_prot_aux /iProto_choice.
        iExists false. iApply iProto_le_refl. }
      iApply recv_all_prot_fwd.
    - iIntros "!>" (x). iApply "IHn".
  Qed.

  Lemma subprot_n_swap_end n :
    ⊢ mapper_prot ⊑ mapper_prot_n_swap_fwd n [] END%proto.
  Proof.
    iApply iProto_le_trans.
    { iApply (subprot_n_swap n). }
    iApply subprot_n_swap_n_swap_end.
  Qed.

  Definition fspec (fv : val) : iProp Σ := (∀ x v,
    {{{ IT x v }}} fv v {{{ u, RET u; IU (f x) u }}})%I.

  Lemma swap_mapper_service_spec c fv p :
    fspec fv -∗
    {{{ c ↣ ((iProto_dual mapper_prot) <++> p)%proto }}}
      swap_mapper_service fv c
    {{{ RET #(); c ↣ p }}}.
  Proof.
    iIntros "#Hfspec !>" (Φ) "Hc HΦ".
    iLöb as "IH".
    wp_rec. wp_branch.
    - wp_recv (x v) as "HT". wp_apply ("Hfspec" with "HT").
      iIntros (w) "HU".
      wp_send with "[$HU]". wp_pures. iApply ("IH" with "Hc HΦ").
    - wp_pures. by iApply "HΦ".
  Qed.

  Lemma swap_mapper_client_spec fv l xs :
    fspec fv -∗
    {{{ llist IT l xs }}}
      swap_mapper_client fv #l
    {{{ ys, RET #(); ⌜ys = map f xs⌝ ∗ llist IU l ys }}}.
  Proof.
    iIntros "#Hfspec !>" (Φ) "HIT HΦ".
    wp_lam.
    wp_apply (start_chan_spec mapper_prot); iIntros (c) "// Hc".
    { wp_lam. rewrite -(iProto_app_end_r (iProto_dual mapper_prot)).
      iApply (swap_mapper_service_spec _ _ END%proto with "Hfspec Hc").
      auto. }
    wp_apply (llength_spec with "HIT"); iIntros "HIT".
    wp_apply (send_all_spec with "[$HIT Hc]").
    { iApply (iProto_mapsto_le with "Hc").
      iApply subprot_n_swap. }
    iIntros "[HIT Hc]".
    rewrite right_id rev_involutive.
    wp_apply (recv_all_spec with "[$HIT $Hc]").
    iIntros (ys) "(% & HIT & Hc)".
    wp_select.
    iApply "HΦ".
    by iFrame.
  Qed.

End with_Σ.
