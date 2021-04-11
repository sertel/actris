(** This file provides three wrappers around the distributed version of merge
sort, demonstrating Actris's support for delegation and branching:

- [sort_service_br]: a service that allows one to sort a series of lists in
  sequence.
- [sort_service_del]: a service that allows one to sort a series of lists in
  parallel by delegating a sort service for a single list to a new channel.
- [sort_service_br_del]: a service that allows one to sort a series of list by
  forking itself. *)
From stdpp Require Import sorting.
From actris.channel Require Import proofmode.
From actris.examples Require Import sort.

Definition sort_service_br : val :=
  rec: "go" "cmp" "c" :=
    if: ~recv "c" then #() else
    sort_service "cmp" "c";;
    "go" "cmp" "c".

Definition sort_client_br : val :=
  λ: "cmp" "l",
    let: "c" := start_chan (λ: "c", sort_service_br "cmp" "c") in
    liter (λ: "l'", send "c" #true;; send "c" "l'";; recv "c") "l";;
    send "c" #false.

Definition sort_service_del : val :=
  rec: "go" "cmp" "c" :=
    if: ~recv "c" then #() else
    send "c" (start_chan (λ: "c", sort_service "cmp" "c"));;
    "go" "cmp" "c".

Definition sort_client_del : val :=
  λ: "cmp" "l",
    let: "c" := start_chan (λ: "c", sort_service_del "cmp" "c") in
    let: "k" := lnil #() in
    liter (λ: "l'", send "c" #true;;
                    let: "c'" := recv "c" in
                    send "c'" "l'";;
                    lcons "c'" "k") "l";;
    send "c" #false;;
    liter (λ: "c", #();; recv "c") "k".

Definition sort_service_br_del : val :=
  rec: "go" "cmp" "c" :=
    if: recv "c" then
      sort_service "cmp" "c";;
      "go" "cmp" "c"
    else if: recv "c" then
      send "c" (start_chan (λ: "c", "go" "cmp" "c"));;
      "go" "cmp" "c"
    else #().

Section sort_service_br_del.
  Context `{!heapGS Σ, !chanG Σ}.
  Context {A} (I : A → val → iProp Σ) (R : A → A → Prop) `{!RelDecision R, !Total R}.

  Definition sort_protocol_br_aux (rec : iProto Σ) : iProto Σ :=
    ((sort_protocol I R <++> rec) <+> END)%proto.
  Instance sort_protocol_br_aux_contractive : Contractive sort_protocol_br_aux.
  Proof. solve_proto_contractive. Qed.
  Definition sort_protocol_br : iProto Σ := fixpoint sort_protocol_br_aux.
  Global Instance sort_protocol_br_unfold :
    ProtoUnfold sort_protocol_br (sort_protocol_br_aux sort_protocol_br).
  Proof. apply proto_unfold_eq, (fixpoint_unfold sort_protocol_br_aux). Qed.

  Lemma sort_service_br_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ iProto_dual sort_protocol_br }}}
      sort_service_br cmp c
    {{{ RET #(); c ↣ END }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec. wp_branch; wp_pures.
    { wp_smart_apply (sort_service_spec with "Hcmp Hc"); iIntros "Hc".
      by wp_smart_apply ("IH" with "Hc"). }
    by iApply "HΨ".
  Qed.

  Definition lllist (I : A → val → iProp Σ)
             (l : loc) (yys : list (list A)) : iProp Σ :=
    llist (λ ys l, ∃ (l' : loc), ⌜#l' = l⌝ ∗ llist I l' ys)%I l yys.

  Lemma sort_client_br_spec cmp l xxs :
    cmp_spec I R cmp -∗
    {{{ lllist I l xxs }}}
      sort_client_br cmp #l
    {{{ yys, RET #(); lllist I l yys ∗
                       ([∗list] k↦xs;ys ∈ xxs; yys, ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝) }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ". wp_lam.
    wp_smart_apply (start_chan_spec sort_protocol_br); iIntros (c) "Hc".
    - wp_lam. iApply (sort_service_br_spec with "[$] Hc"). by iIntros "!> Hc".
    - wp_smart_apply (liter_spec _ l xxs
        (λ xs l, ∃ (l' : loc), ⌜#l' = l⌝ ∗ llist I l' xs)%I
        (λ xs l, ∃ (ys : list A) (l' : loc), ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗
                      ⌜#l' = l⌝ ∗ llist I l' ys)%I
        (λ _, c ↣ sort_protocol_br)
                        with "[] [$Hl $Hc]").
      { iIntros (_ x v) "!>".
        iIntros (Ψ) "[Hl' Hc] HΨ".
        iDestruct "Hl'" as (l' <-) "Hl'". wp_lam. wp_select.
        wp_send with "[Hl'//]".
        wp_recv (ys) as "[Hsorted [Hperm Hys]]".
        iIntros "!>".
        rewrite iProto_app_end_l.
        iApply "HΨ".
        iFrame "Hc".
        iExists ys, l'. by iFrame. }
      iIntros "[Hl Hc]". wp_pures. wp_select.
      iDestruct (llist_out with "Hl") as (vs) "[Hvs Hxxs]".
      iAssert (∃ yys : list (list A),
                  ([∗ list] x;ys ∈ xxs;yys,
                            ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ x⌝) ∗
                   [∗ list] ys;v ∈ yys;vs, ∃ (l' : loc),
                                           ⌜#l' = v⌝ ∗ llist I l' ys)%I
              with "[Hxxs]" as (yys) "[Hyys Hvs']".
      { iInduction xxs as [|xs xxs] "IH" forall (vs).
        - iDestruct (big_sepL2_nil_inv_l with "Hxxs") as %->. eauto.
        - iDestruct (big_sepL2_cons_inv_l with "Hxxs") as (v vs' ->) "[Hv Hxxs]".
          iDestruct "Hv" as (ys l' Hsorted Hperm <-) "Hv".
          iDestruct ("IH" with "Hxxs") as (yys) "[Hyys Hvs]".
          iExists (ys::yys).
          iFrame "Hyys Hvs".
          eauto with iFrame. }
      iApply "HΦ".
      iIntros "!>". iFrame "Hyys".
      iApply (llist_in with "[$Hvs $Hvs']").
  Qed.

  Definition sort_protocol_del_aux (rec : iProto Σ) : iProto Σ :=
    ((<? c> MSG c {{ c ↣ sort_protocol I R }}; rec) <+> END)%proto.
  Instance sort_protocol_del_aux_contractive : Contractive sort_protocol_del_aux.
  Proof. solve_proto_contractive. Qed.
  Definition sort_protocol_del : iProto Σ := fixpoint sort_protocol_del_aux.
  Global Instance sort_protocol_del_unfold :
    ProtoUnfold sort_protocol_del (sort_protocol_del_aux sort_protocol_del).
  Proof. apply proto_unfold_eq, (fixpoint_unfold sort_protocol_del_aux). Qed.

  Lemma sort_service_del_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ iProto_dual sort_protocol_del }}}
      sort_service_del cmp c
    {{{ RET #(); c ↣ END }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (Ψ).
    wp_rec. wp_branch; wp_pures.
    { wp_smart_apply (start_chan_spec (sort_protocol I R <++> END)%proto); iIntros (c') "Hc'".
      { wp_pures. wp_smart_apply (sort_service_spec with "Hcmp Hc'"); auto. }
      wp_send with "[$Hc']". by wp_smart_apply ("IH" with "Hc"). }
    by iApply "HΨ".
  Qed.

  Lemma sort_client_del_spec cmp l xxs :
    cmp_spec I R cmp -∗
    {{{ lllist I l xxs }}}
      sort_client_del cmp #l
    {{{ yys, RET #(); lllist I l yys ∗
                       ([∗list] k↦xs;ys ∈ xxs; yys, ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝) }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ". wp_lam.
    wp_smart_apply (start_chan_spec sort_protocol_del); iIntros (c) "Hc".
    - wp_lam. iApply (sort_service_del_spec with "[$] Hc"). eauto.
    - wp_smart_apply (lnil_spec with "[//]").
      iIntros (k) "Hk".
      iDestruct (llist_unfold_vals with "Hl") as (vs Hlen) "Hl".
      wp_smart_apply (liter_spec _ l (zip vs xxs)
        (λ xs l, ⌜xs.1 = l⌝ ∗ ∃ (l' : loc), ⌜#l' = l⌝ ∗ llist I l' xs.2)%I
        (λ xs l, ⌜xs.1 = l⌝)%I
        (λ xxs, c ↣ sort_protocol_del ∗
                  llist (λ xs c,
                         ∃ (l' : loc), ⌜#l' = xs.1⌝ ∗
                                       c ↣ <? (xs' : list A)> MSG #()
                                            {{ ⌜ Sorted R xs' ⌝ ∗ ⌜ xs' ≡ₚ xs.2 ⌝ ∗
                                               llist I l' xs' }};
                                       END) k (reverse xxs))%I
        with "[] [$Hl $Hk $Hc]").
      { iIntros (xs x v) "!>".
        iIntros (Ψ) "[H [Hc Hxs]] HΨ".
        iDestruct "H" as (Heq l' <-) "Hl'". wp_lam. wp_select.
        wp_recv (c') as "Hc'".
        wp_send with "[Hl'//]".
        wp_smart_apply (lcons_spec with "[$Hxs Hc']").
        { iExists l'. eauto with iFrame. }
        iIntros "Hxs".
        iApply "HΨ".
        rewrite reverse_app.
        by iFrame. }
      iIntros "[Hl [Hc Hk]]".
      iDestruct (llist_fmap (λ (xs : val * list A) (v : val), ⌜xs.1 = v⌝)%I
                            (λ (xs : val) (v : val), ⌜xs = v⌝)%I fst
                   with "[] Hl") as "Hl"; [ eauto | ].
      rewrite fst_zip; [ | lia ].
      wp_select. iClear "Hc".
      wp_smart_apply (liter_spec _ k (reverse (zip vs xxs))
          (λ (xs : val * list A) (c : val),
              ∃ l' : loc,
                ⌜#l' = xs.1⌝
                ∗ c ↣ (<? (xs' : list A)> MSG #() {{ ⌜Sorted R xs'⌝
                                                     ∗ ⌜xs' ≡ₚ xs.2⌝ ∗
                                                       llist I l' xs' }}; END))%I
          (λ (xs : val * list A) (v : val),
           ∃ (l' : loc) xs',
             ⌜#l' = xs.1⌝ ∗ ⌜Sorted R xs'⌝ ∗ ⌜xs' ≡ₚ xs.2⌝ ∗ llist I l' xs')%I
          (λ _, True)%I with "[] [$Hk]").
      { iIntros (_ x v) "!>".
        iIntros (Ψ) "[Hc _] HΨ".
        iDestruct "Hc" as (l' Heq) "Hc".
        wp_pures. wp_recv (xs') as "[Hsorted [Hperm Hl']]". iClear "Hc".
        iIntros "!>".
        iApply "HΨ".
        eauto with iFrame. }
      iIntros "[Hk _]".
      iDestruct (llist_out with "Hk") as (vs') "[_ Hxxs]".
      iDestruct (big_sepL2_reverse_2 with "Hxxs") as "Hxxs".
      rewrite reverse_involutive.
      iAssert ([∗ list] xs;v ∈ xxs;vs,
                                   ∃ (l' : loc) (xs' : list A),
                                     ⌜#l' = v⌝ ∗ ⌜Sorted R xs'⌝ ∗
                                     ⌜xs' ≡ₚ xs⌝ ∗ llist I l' xs')%I
        with "[Hxxs]" as "Hxxs".
      {
        iRevert (Hlen).
        generalize (reverse vs'); clear vs'; intros vs'.
        iInduction xxs as [|xs xxs] "IH" forall (vs vs'); iIntros (Hlen).
        - by rewrite (nil_length_inv vs); [ | eauto ].
        - assert (∃ v' vs', vs = v' :: vs') as [v' [vs'' ->]].
          { destruct vs; eauto.
            inversion Hlen. }
          iDestruct (big_sepL2_cons_inv_l with "Hxxs") as (tmp1 tmp2 ->) "Hxxs".
          iDestruct "Hxxs" as "[Hxs Hxxs]".
          iDestruct "Hxs" as (l' xs' Heq) "[Hsorted [Hperm Hl']]".
          iSplitR "Hxxs".
          { eauto with iFrame. }
          iApply ("IH" with "Hxxs").
          eauto.
      }
      iAssert (∃ yys : list (list A),
                    ([∗ list] x;ys ∈ xxs;yys,
                   ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ x⌝) ∗
                    [∗ list] ys;v ∈ yys;vs, ∃ (l' : loc),
                    ⌜#l' = v⌝ ∗ llist I l' ys)%I
                with "[Hxxs]" as (yys) "[Hyys Hvs']".
      {
        clear Hlen vs'.
        iInduction xxs as [|xs xxs] "IH" forall (vs).
        - iDestruct (big_sepL2_nil_inv_l with "Hxxs") as %->. eauto.
        - iDestruct (big_sepL2_cons_inv_l with "Hxxs") as (v vs' ->) "[Hv Hxxs]".
          iDestruct "Hv" as (l' ys <- Hsorted Hperm) "Hl".
          iDestruct ("IH" with "Hxxs") as (yys) "[Hyys Hvs]".
          iExists (ys::yys).
          simpl. iFrame "Hyys Hvs".
          eauto with iFrame.
      }
      iApply "HΦ".
      iFrame.
      iApply llist_in. iFrame.
  Qed.

  Definition sort_protocol_br_del_aux (rec : iProto Σ) : iProto Σ :=
    ((sort_protocol I R <++> rec) <+> ((<? c> MSG c {{ c ↣ rec }}; rec) <+> END))%proto.
  Instance sort_protocol_br_del_aux_contractive : Contractive sort_protocol_br_del_aux.
  Proof. solve_proto_contractive. Qed.
  Definition sort_protocol_br_del : iProto Σ := fixpoint sort_protocol_br_del_aux.
  Global Instance sort_protocol_br_del_unfold :
    ProtoUnfold sort_protocol_br_del (sort_protocol_br_del_aux sort_protocol_br_del).
  Proof. apply proto_unfold_eq, (fixpoint_unfold sort_protocol_br_del_aux). Qed.

  Lemma sort_service_br_del_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ iProto_dual sort_protocol_br_del }}}
      sort_service_br_del cmp c
    {{{ RET #(); c ↣ END }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec. wp_branch; wp_pures.
    { wp_smart_apply (sort_service_spec with "Hcmp Hc"); iIntros "Hc".
      by wp_smart_apply ("IH" with "Hc"). }
    wp_branch; wp_pures.
    { wp_smart_apply (start_chan_spec sort_protocol_br_del); iIntros (c') "Hc'".
      { wp_smart_apply ("IH" with "Hc'"); auto. }
      wp_send with "[$Hc']".
      by wp_smart_apply ("IH" with "Hc"). }
    by iApply "HΨ".
  Qed.

End sort_service_br_del.
