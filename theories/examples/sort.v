From stdpp Require Import sorting.
From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From actris.utils Require Export llist compare.

Definition lmerge : val :=
  rec: "go" "cmp" "ys" "zs" :=
    if: lisnil "ys" then lapp "ys" "zs" else
    if: lisnil "zs" then #() else
    let: "y" := lhead "ys" in
    let: "z" := lhead "zs" in
    if: "cmp" "y" "z"
    then lpop "ys";; "go" "cmp" "ys" "zs";; lcons "y" "ys"
    else lpop "zs";; "go" "cmp" "ys" "zs";; lcons "z" "ys".

Definition sort_service : val :=
  rec: "go" "c" :=
    let: "cmp" := recv "c" in
    let: "xs" := recv "c" in
    if: llength "xs" ≤ #1 then send "c" #() else
    let: "zs" := lsplit "xs" in
    let: "cy" := start_chan "go" in
    let: "cz" := start_chan "go" in
    send "cy" "cmp";; send "cy" "xs";;
    send "cz" "cmp";; send "cz" "zs";;
    recv "cy";; recv "cz";;
    lmerge "cmp" "xs" "zs";;
    send "c" #().

Section sort.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  Definition sort_protocol : iProto Σ :=
    (<!> A (I : A → val → iProp Σ) (R : A → A → Prop)
         `{!RelDecision R, !Total R} (cmp : val),
       MSG cmp {{ cmp_spec I R cmp }};
     <!> (xs : list A) (l : loc) (vs : list val),
       MSG #l {{ llist l vs ∗ [∗ list] x;v ∈ xs;vs, I x v }};
     <?> (xs' : list A) (vs' : list val),
       MSG #() {{ ⌜ Sorted R xs' ⌝ ∗ ⌜ xs' ≡ₚ xs ⌝ ∗
                  llist l vs' ∗ [∗ list] x;v ∈ xs';vs', I x v }};
     END)%proto.

  Lemma lmerge_spec {A} (I : A → val → iProp Σ) (R : A → A → Prop)
      `{!RelDecision R, !Total R} (cmp : val) l1 l2 xs1 xs2 vs1 vs2 :
    cmp_spec I R cmp -∗
    {{{
      llist l1 vs1 ∗ llist l2 vs2 ∗
      ([∗ list] x;v ∈ xs1;vs1, I x v) ∗ ([∗ list] x;v ∈ xs2;vs2, I x v)
    }}}
      lmerge cmp #l1 #l2
    {{{ ws, RET #(); llist l1 ws ∗ [∗ list] x;v ∈ list_merge R xs1 xs2;ws, I x v }}}.
  Proof.
    iIntros "#Hcmp" (Ψ) "!> (Hl1 & Hl2 & HI1 & HI2) HΨ".
    iLöb as "IH" forall (l2 xs1 xs2 vs1 vs2 Ψ).
    wp_lam. wp_apply (lisnil_spec with "Hl1"); iIntros "Hl1".
    destruct xs1 as [|x1 xs1], vs1 as [|v1 vs1]; simpl; done || wp_pures.
    { wp_apply (lapp_spec with "[$Hl1 $Hl2]"); iIntros "[Hl1 _] /=".
      iApply "HΨ". iFrame. by rewrite list_merge_nil_l. }
    wp_apply (lisnil_spec with "Hl2"); iIntros "Hl2".
    destruct xs2 as [|x2 xs2], vs2 as [|v2 vs2]; simpl; done || wp_pures.
    { iApply "HΨ". iFrame. }
    wp_apply (lhead_spec with "Hl1"); iIntros "Hl1".
    wp_apply (lhead_spec with "Hl2"); iIntros "Hl2".
    iDestruct "HI1" as "[HI1 HI1']"; iDestruct "HI2" as "[HI2 HI2']".
    wp_apply ("Hcmp" with "[$HI1 $HI2]"); iIntros "[HI1 HI2]".
    case_bool_decide; wp_pures.
    - rewrite decide_True //.
      wp_apply (lpop_spec with "Hl1"); iIntros "Hl1".
      wp_apply ("IH" $! _ _ (x2 :: _) with "Hl1 Hl2 HI1' [$HI2 $HI2']").
      iIntros (ws) "[Hl1 HI]".
      wp_apply (lcons_spec with "Hl1"); iIntros "Hl1". iApply "HΨ". iFrame.
    - rewrite decide_False //.
      wp_apply (lpop_spec with "Hl2"); iIntros "Hl2".
      wp_apply ("IH" $! _ (x1 :: _) with "Hl1 Hl2 [$HI1 $HI1'] HI2'").
      iIntros (ws) "[Hl1 HI]".
      wp_apply (lcons_spec with "Hl1"); iIntros "Hl1". iApply "HΨ". iFrame.
  Qed.

  Lemma sort_service_spec p c :
    {{{ c ↣ iProto_dual sort_protocol <++> p @ N }}}
      sort_service c
    {{{ RET #(); c ↣ p @ N }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". iLöb as "IH" forall (p c Ψ). wp_lam.
    wp_recv (A I R ?? cmp) as "#Hcmp".
    wp_recv (xs l vs) as "[Hl HI]".
    wp_apply (llength_spec with "Hl"); iIntros "Hl".
    iDestruct (big_sepL2_length with "HI") as %<-.
    wp_op; case_bool_decide as Hlen; wp_if.
    { assert (Sorted R xs).
      { destruct xs as [|x1 [|x2 xs]]; simpl in *; eauto with lia. }
      wp_send with "[$Hl $HI]"; first by auto. by iApply "HΨ". }
    wp_apply (lsplit_spec with "Hl"); iIntros (l2 vs1 vs2);
      iDestruct 1 as (->) "[Hl1 Hl2]".
    iDestruct (big_sepL2_app_inv_r with "HI") as (xs1 xs2 ->) "[HI1 HI2]".
    wp_apply (start_chan_proto_spec N sort_protocol); iIntros (cy) "Hcy".
    { rewrite -{2}(right_id END%proto _ (iProto_dual _)).
      wp_apply ("IH" with "Hcy"); auto. }
    wp_apply (start_chan_proto_spec N sort_protocol); iIntros (cz) "Hcz".
    { rewrite -{2}(right_id END%proto _ (iProto_dual _)).
      wp_apply ("IH" with "Hcz"); auto. }
    wp_send with "[$Hcmp]".
    wp_send with "[$Hl1 $HI1]".
    wp_send with "[$Hcmp]".
    wp_send with "[$Hl2 $HI2]".
    wp_recv (ys1 ws1) as (??) "[Hl1 HI1]".
    wp_recv (ys2 ws2) as (??) "[Hl2 HI2]".
    wp_apply (lmerge_spec with "Hcmp [$Hl1 $Hl2 $HI1 $HI2]"); iIntros (ws) "[Hl HI]".
    wp_send ((list_merge R ys1 ys2) ws) with "[$Hl $HI]".
    - iSplit; iPureIntro.
      + by apply (Sorted_list_merge _).
      + rewrite (merge_Permutation R). by f_equiv.
    - by iApply "HΨ".
  Qed.
End sort.
