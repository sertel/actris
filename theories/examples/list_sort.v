From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel.
From iris.heap_lang Require Import proofmode notation.
From osiris.utils Require Import list.

Definition compare_vals : val :=
    λ: "x" "y", "x" ≤ "y".

Definition lmerge : val :=
  rec: "go" "cmp" "hys" "hzs" :=
    match: "hys" with
      NONE => "hzs"
    | SOME "_" =>
      match: "hzs" with
        NONE => "hys"
      | SOME "_" =>
        let: "y" := lhead "hys" in
        let: "z" := lhead "hzs" in
        if: ("cmp" "y" "z")
        then lcons "y" ("go" "cmp" (ltail "hys") "hzs")
        else lcons "z" ("go" "cmp" "hys" (ltail "hzs"))
      end
    end.

Definition list_sort_service : val :=
  rec: "go" "c" :=
    let: "cmp" := recv "c" in
    let: "xs" := recv "c" in
    if: llength !"xs" ≤ #1 then
      send "c" #() else
    let: "ys_zs" := lsplit !"xs" in
    let: "ys" := ref (Fst "ys_zs") in
    let: "zs" := ref (Snd "ys_zs") in
    let: "cy" := new_chan #() in Fork("go" (Snd "cy"));;
    let: "cz" := new_chan #() in Fork("go" (Snd "cz"));;
    send (Fst "cy") "cmp";;
    send (Fst "cy") "ys";;
    send (Fst "cz") "cmp";;
    send (Fst "cz") "zs";;
    recv (Fst "cy");;
    recv (Fst "cz");;
    "xs" <- lmerge "cmp" !"ys" !"zs";;
    send "c" #().

Definition loop_sort_service_go : val :=
  rec: "go" "c" :=
    if: recv "c" then list_sort_service "c";; "go" "c"
    else if: recv "c" then
      let: "d" := new_chan #() in
      Fork ("go" (Snd "d"));;
      send "c" (Fst "d");;
      "go" "c"
    else #().
Definition loop_sort_service : val := λ: <>,
  let: "c" := new_chan #() in
  Fork (loop_sort_service_go (Snd "c"));;
  Fst "c".

Definition list_sort_client : val := λ: "cmp" "xs",
  let: "c" := new_chan #() in
  Fork (list_sort_service (Snd "c"));;
  send (Fst "c") "cmp";;
  send (Fst "c") "xs";;
  recv (Fst "c");;
  #().

Section list_sort.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  Definition cmp_spec {A} (I : A → val → iProp Σ)
      (R : A → A → Prop) `{!RelDecision R} (cmp : val) : iProp Σ :=
    (∀ x x' v v',
      {{{ I x v ∗ I x' v' }}}
        cmp v v'
      {{{ RET #(bool_decide (R x x')); I x v ∗ I x' v' }}})%I.

  Definition sort_protocol : iProto Σ :=
    (<!> A (I : A → val → iProp Σ) (R : A → A → Prop)
         `{!RelDecision R, !Total R} (cmp : val),
       MSG cmp {{ cmp_spec I R cmp }};
     <!> (xs : list A) (l : loc) (vs : list val),
       MSG #l {{ l ↦ val_encode vs ∗ [∗ list] x;v ∈ xs;vs, I x v }};
     <?> (xs' : list A) (vs' : list val),
       MSG #() {{ ⌜ Sorted R xs' ⌝ ∗ ⌜ xs' ≡ₚ xs ⌝ ∗
                  l ↦ val_encode vs' ∗ [∗ list] x;v ∈ xs';vs', I x v }};
     END)%proto.

  Lemma lmerge_spec {A} (I : A → val → iProp Σ) (R : A → A → Prop)
      `{!RelDecision R, !Total R} (cmp : val) xs1 xs2 vs1 vs2 :
    cmp_spec I R cmp -∗
    {{{ ([∗ list] x;v ∈ xs1;vs1, I x v) ∗ ([∗ list] x;v ∈ xs2;vs2, I x v) }}}
      lmerge cmp (val_encode vs1) (val_encode vs2)
    {{{ ws, RET val_encode ws; [∗ list] x;v ∈ list_merge R xs1 xs2;ws, I x v }}}.
  Proof.
    iIntros "#Hcmp" (Ψ) "!> [HI1 HI2] HΨ". iLöb as "IH" forall (xs1 xs2 vs1 vs2 Ψ).
    destruct xs1 as [|x1 xs1], vs1 as [|v1 vs1]; simpl; try done.
    { wp_lam. wp_pures. iApply "HΨ". by rewrite list_merge_nil_l. }
    wp_lam; wp_pures.
    destruct xs2 as [|x2 xs2], vs2 as [|v2 vs2]; simpl; try done.
    { wp_pures. iApply "HΨ". iFrame. }
    wp_pures.
    wp_apply (lhead_spec (A:=val) with "[//]"); iIntros (_).
    wp_apply (lhead_spec (A:=val) with "[//]"); iIntros (_).
    iDestruct "HI1" as "[HI1 HI1']"; iDestruct "HI2" as "[HI2 HI2']".
    wp_apply ("Hcmp" with "[$HI1 $HI2]"); iIntros "[HI1 HI2]".
    case_bool_decide; wp_pures.
    - rewrite decide_True //.
      wp_apply (ltail_spec (A:=val) with "[//]"); iIntros (_).
      wp_apply ("IH" $! _ (x2 :: _) with "HI1'[HI2 HI2']"); [simpl; iFrame|].
      iIntros (ws) "HI".
      wp_apply (lcons_spec (A:=val) with "[//]"); iIntros (_).
      iApply "HΨ". iFrame.
    - rewrite decide_False //.
      wp_apply (ltail_spec (A:=val) with "[//]"); iIntros (_).
      wp_apply ("IH" $! (x1 :: _) with "[HI1 HI1'] HI2'"); [simpl; iFrame|].
      iIntros (ws) "HI".
      wp_apply (lcons_spec (A:=val) with "[//]"); iIntros (_).
      iApply "HΨ". iFrame.
  Qed.

  Lemma list_sort_service_spec p c :
    {{{ c ↣ iProto_dual sort_protocol <++> p @ N }}}
      list_sort_service c
    {{{ RET #(); c ↣ p @ N }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". iLöb as "IH" forall (p c Ψ).
    wp_lam.
    wp_apply (recv_proto_spec with "Hc"); simpl.
    iIntros (A I R ?? cmp) "/= Hc #Hcmp".
    wp_apply (recv_proto_spec with "Hc"); simpl.
    iIntros (xs l vs) "/= Hc [Hl HI]".
    wp_load. wp_apply (llength_spec (A:=val) with "[//]"); iIntros (_).
    iDestruct (big_sepL2_length with "HI") as %<-.
    wp_op; case_bool_decide as Hlen; wp_if.
    { assert (Sorted R xs).
      { destruct xs as [|x1 [|x2 xs]]; simpl in *; eauto with lia. }
      wp_apply (send_proto_spec with "Hc"); simpl.
      iExists xs, vs; iSplit; first done. eauto 10 with iFrame. }
    wp_load. wp_apply (lsplit_spec (A:=val) with "[//]"); iIntros (vs1 vs2 <-).
    wp_alloc l1 as "Hl1"; wp_alloc l2 as "Hl2".
    iDestruct (big_sepL2_app_inv_r with "HI") as (xs1 xs2 ->) "[HI1 HI2]".
    wp_apply (new_chan_proto_spec N sort_protocol)=> //.
    iIntros (cy1 cy2) "[Hcy1 Hcy2]".
    wp_apply (wp_fork with "[Hcy2]").
    { iNext. rewrite -{2}(right_id END%proto _ (iProto_dual _)).
      wp_apply ("IH" with "Hcy2"); auto. }
    wp_apply (new_chan_proto_spec N sort_protocol)=> //.
    iIntros (cz1 cz2) "[Hcz1 Hcz2]".
    wp_apply (wp_fork with "[Hcz2]").
    { iNext. rewrite -{2}(right_id END%proto _ (iProto_dual _)).
      wp_apply ("IH" with "Hcz2"); auto. }
    wp_apply (send_proto_spec with "Hcy1"); simpl.
    iExists _, I, R, _, _, cmp. iSplit; first done. iIntros "{$Hcmp} !> Hcy1".
    wp_apply (send_proto_spec with "Hcy1"); simpl.
    iExists xs1, l1, vs1. iSplit; first done. iIntros "{$Hl1 $HI1} !> Hcy1".
    wp_apply (send_proto_spec with "Hcz1"); simpl.
    iExists _, I, R, _, _, cmp. iSplit; first done. iIntros "{$Hcmp} !> Hcz1".
    wp_apply (send_proto_spec with "Hcz1"); simpl.
    iExists xs2, l2, vs2. iSplit; first done. iIntros "{$Hl2 $HI2} !> Hcz1".
    wp_apply (recv_proto_spec with "Hcy1"); simpl.
    iIntros (ys1 ws1) "_". iDestruct 1 as (??) "[Hl1 HI1]".
    wp_apply (recv_proto_spec with "Hcz1"); simpl.
    iIntros (ys2 ws2) "_". iDestruct 1 as (??) "[Hl2 HI2]".
    do 2 wp_load.
    wp_apply (lmerge_spec with "Hcmp [$HI1 $HI2]"). iIntros (ws) "HI".
    wp_store.
    wp_apply (send_proto_spec with "Hc"); simpl.
    iExists (list_merge R ys1 ys2), ws.
    iSplit; first done. iFrame. iSplit; iPureIntro.
    - by apply (Sorted_list_merge _).
    - rewrite (merge_Permutation R). by f_equiv.
  Qed.

  Definition loop_sort_protocol_aux (rec : iProto Σ) : iProto Σ :=
    ((sort_protocol <++> rec) <+> ((<?> c, MSG c {{ c ↣ rec @ N }}; rec) <+> END))%proto.

  Instance loop_sort_protocol_aux_contractive : Contractive loop_sort_protocol_aux.
  Proof.
    intros n p p' Hp. rewrite /loop_sort_protocol_aux.
    f_contractive; f_equiv=> //. apply iProto_message_ne=> c /=; by repeat f_equiv.
  Qed.
  Definition loop_sort_protocol : iProto Σ := fixpoint loop_sort_protocol_aux.
  Lemma loop_sort_protocol_unfold :
    loop_sort_protocol ≡ loop_sort_protocol_aux loop_sort_protocol.
  Proof. apply (fixpoint_unfold loop_sort_protocol_aux). Qed.

  Lemma loop_sort_service_go_spec c :
    {{{ c ↣ iProto_dual loop_sort_protocol @ N }}}
      loop_sort_service_go c
    {{{ RET #(); c ↣ END @ N }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec. rewrite {2}loop_sort_protocol_unfold.
    wp_apply (branch_spec with "Hc"); iIntros ([]) "/= Hc"; wp_if.
    { wp_apply (list_sort_service_spec with "Hc"); iIntros "Hc".
      by wp_apply ("IH" with "Hc"). }
    wp_apply (branch_spec with "Hc"); iIntros ([]) "/= Hc"; wp_if.
    - wp_apply (new_chan_proto_spec N loop_sort_protocol with "[//]");
        iIntros (d1 d2) "[Hd1 Hd2]".
      wp_apply (wp_fork with "[Hd2]").
      { iNext. wp_apply ("IH" with "Hd2"); auto. }
      wp_apply (send_proto_spec with "Hc"); simpl.
      iExists d1; iSplit; first done. iIntros "{$Hd1} !> Hc".
      by wp_apply ("IH" with "Hc").
    - by iApply "HΨ".
  Qed.

  Lemma list_sort_client_spec {A} (I : A → val → iProp Σ) R
       `{!RelDecision R, !Total R} cmp l (vs : list val) (xs : list A) :
    cmp_spec I R cmp -∗
    {{{ l ↦ val_encode vs ∗ [∗ list] x;v ∈ xs;vs, I x v }}}
      list_sort_client cmp #l
    {{{ ys ws, RET #(); ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗
               l ↦ val_encode ws ∗ [∗ list] y;w ∈ ys;ws, I y w }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ".
    wp_lam.
    wp_apply (new_chan_proto_spec N (sort_protocol <++> END)%proto with "[//]")=> /=.
    iIntros (c c') "[Hstl Hstr]".
    wp_apply (wp_fork with "[Hstr]").
    { iNext.
      rewrite (iProto_dual_app sort_protocol (END%proto)).
      wp_apply (list_sort_service_spec (END%proto) c' with "Hstr"); auto. }
    wp_apply (send_proto_spec with "Hstl"); simpl.
    iExists _, I, R, _, _, cmp.
    iSplitR=> //.
    iSplitR=> //.
    iIntros "!> Hstl".
    wp_apply (send_proto_spec with "Hstl"); simpl.
    iExists xs, l, vs.
    iSplitR=> //.
    iIntros "{$Hl} !> Hstl".
    wp_apply (recv_proto_spec with "Hstl"); simpl.
    iIntros (ys ws) "Hstl (Hsorted & Hperm & Hl & HI)".
    wp_pures. iApply "HΦ". iFrame.
  Qed.

  (* Example: Sort of integers *)
  Definition IZ (x : Z) (v : val) : iProp Σ :=
    ⌜∃ w, v = LitV $ LitInt w ∧ x = w⌝%I.

  Lemma compare_vals_spec : cmp_spec IZ (≤) compare_vals.
  Proof.
    iIntros (x x' v v' Φ) "!>".
    iIntros ([[w [-> ->]] [w' [-> ->]]]) "HΦ".
    wp_lam. wp_pures. iApply "HΦ". eauto 10 with iFrame.
  Qed.

  Lemma list_sort_client_le_spec l (xs : list Z) :
    {{{ l ↦ val_encode xs }}}
      list_sort_client compare_vals #l
    {{{ ys, RET #(); ⌜Sorted (≤) ys⌝ ∗ ⌜ ys ≡ₚ xs⌝ ∗ l ↦ val_encode ys }}}.
  Proof.
    assert (val_encode xs = val_encode (LitV ∘ LitInt <$> xs)) as Hxs.
    { admit. }
    iIntros (Φ) "Hl HΦ".
    iApply (list_sort_client_spec IZ (≤) _ _ (LitV ∘ LitInt <$> xs) xs with "[] [Hl] [HΦ]").
    { iApply compare_vals_spec. }
    { rewrite -Hxs {Hxs}. iFrame "Hl".
      iInduction xs as [|x xs] "IH"; csimpl; first by iFrame.
      iFrame "IH". by iExists x. }
    { admit. }
  Admitted.
End list_sort.
