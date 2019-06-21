From stdpp Require Import sorting.
From iris.heap_lang Require Import proofmode notation.
From osiris.utils Require Import list.
From osiris.channel Require Import proto_channel.

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
    let: "cy" := new_chan #() in Fork("go" (Fst "cy"));;
    let: "cz" := new_chan #() in Fork("go" (Fst "cz"));;
    send (Snd "cy") "cmp";;
    send (Snd "cy") "ys";;
    send (Snd "cz") "cmp";;
    send (Snd "cz") "zs";;
    recv (Snd "cy");;
    recv (Snd "cz");;
    "xs" <- lmerge "cmp" !"ys" !"zs";;
    send "c" #().

Section list_sort.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  Definition cmp_spec {A} (I : A → val → iProp Σ)
      (R : A → A → Prop) `{!RelDecision R} (cmp : val) : iProp Σ :=
    (∀ x x' v v',
      {{{ I x v ∗ I x' v' }}}
        cmp v v'
      {{{ RET #(bool_decide (R x x')); I x v ∗ I x' v' }}})%I.

  Definition sort_protocol : iProto Σ :=
    (<?> ∃ A (I : A → val → iProp Σ) (R : A → A → Prop)
         `{!RelDecision R, !TotalOrder R} (cmp : val),
       MSG cmp {{ cmp_spec I R cmp }};
     <?> ∃ (xs : list A) (l : loc) (vs : list val),
       MSG #l {{ l ↦ val_encode vs ∗ [∗ list] x;v ∈ xs;vs, I x v }};
     <!> ∃ (xs' : list A) (vs' : list val),
       MSG #() {{ ⌜ Sorted R xs' ⌝ ∗ ⌜ xs' ≡ₚ xs ⌝ ∗
                  l ↦ val_encode vs' ∗ [∗ list] x;v ∈ xs';vs', I x v }};
     iProto_end)%proto.

  Lemma lmerge_spec {A} (I : A → val → iProp Σ) (R : A → A → Prop)
      `{!RelDecision R, !TotalOrder R} (cmp : val) xs1 xs2 vs1 vs2 :
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

  Lemma list_sort_service_spec c :
    {{{ c ↣ sort_protocol @ N }}}
      list_sort_service c
    {{{ RET #(); c ↣ iProto_end @ N }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
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
    wp_apply (wp_fork with "[Hcy1]").
    { iNext. wp_apply ("IH" with "Hcy1"); auto. }
    wp_apply (new_chan_proto_spec N sort_protocol)=> //.
    iIntros (cz1 cz2) "[Hcz1 Hcz2]".
    wp_apply (wp_fork with "[Hcz1]").
    { iNext. wp_apply ("IH" with "Hcz1"); auto. }
    wp_apply (send_proto_spec with "Hcy2"); simpl.
    iExists _, I, R, _, _, cmp. iSplit; first done. iIntros "{$Hcmp} !> Hcy2".
    wp_apply (send_proto_spec with "Hcy2"); simpl.
    iExists xs1, l1, vs1. iSplit; first done. iIntros "{$Hl1 $HI1} !> Hcy2".
    wp_apply (send_proto_spec with "Hcz2"); simpl.
    iExists _, I, R, _, _, cmp. iSplit; first done. iIntros "{$Hcmp} !> Hcz2".
    wp_apply (send_proto_spec with "Hcz2"); simpl.
    iExists xs2, l2, vs2. iSplit; first done. iIntros "{$Hl2 $HI2} !> Hcz2".
    wp_apply (recv_proto_spec with "Hcy2"); simpl.
    iIntros (ys1 ws1) "_". iDestruct 1 as (??) "[Hl1 HI1]".
    wp_apply (recv_proto_spec with "Hcz2"); simpl.
    iIntros (ys2 ws2) "_". iDestruct 1 as (??) "[Hl2 HI2]".
    do 2 wp_load.
    wp_apply (lmerge_spec with "Hcmp [$HI1 $HI2]"); iIntros (ws) "HI".
    wp_store.
    wp_apply (send_proto_spec with "Hc"); simpl.
    iExists (list_merge R ys1 ys2), ws.
    iSplit; first done. iFrame. iSplit; iPureIntro.
    - by apply (Sorted_list_merge _).
    - rewrite (merge_Permutation R). by f_equiv.
  Qed.
End list_sort.

(*
  Definition compare_vals : val :=
    λ: "x" "y", "x" ≤ "y".

  Lemma compare_vals_spec (x y : Z) :
    {{{ True }}}
      compare_vals (val_encode x) (val_encode y)
    {{{ RET val_encode (bool_decide (x ≤ y)); True }}}.
  Proof. iIntros (Φ) "_ HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

  Definition list_sort : val :=
    λ: "xs",
    let: "c" := new_chan #() in
    Fork(list_sort_service "c");;
        send "c" #Left compare_vals;;
        send "c" #Left "xs";;
        recv "c" #Left.

  Lemma list_sort_spec l xs :
    {{{ l ↦ val_encode xs }}}
      list_sort #l
    {{{ ys, RET #l; l ↦ val_encode ys ∗ ⌜Sorted (≤) ys⌝ ∗ ⌜Permutation ys xs⌝ }}}.
  Proof.
     iIntros (Φ) "Hc HΦ".
     wp_lam.
     wp_apply (new_chan_st_spec N _ (sort_protocol (≤) xs))=> //.
     iIntros (c γ) "[Hstl Hstr]".
     wp_apply (wp_fork with "[Hstr]").
     {
       iApply (list_sort_service_spec (≤) γ c xs with "Hstr").
       iNext. iNext. iIntros "Hstr". done.
     }
     wp_apply (send_st_spec (A:=val) with "[$Hstl]").
     {
       iIntros (x y Φ').
       iApply compare_vals_spec=> //.
     }
     iIntros "Hstl".
     wp_apply (send_st_spec (A:=loc) with "[Hc $Hstl]"). iFrame.
     iIntros "Hstl".
     wp_apply (recv_st_spec (A:=loc) with "Hstl").
     iIntros (v) "[Hstl HP]".
     iDestruct "HP" as (<- ys) "[Hys Hys_sorted_of]".
     iApply "HΦ". iFrame.
  Qed.
*)
