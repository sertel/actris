From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From osiris.typing Require Import side stype.
From osiris.encodings Require Import list channel stype_enc.
From iris.base_logic Require Import invariants.
From stdpp Require Import sorting.
Require Import Coq.Lists.List.
Require Import Omega.

Section ListSortExample.
  Context `{!heapG Σ} `{logrelG val Σ} (N : namespace).

  Definition lsplit_ref : val :=
    λ: "xs", let: "ys_zs" := lsplit !"xs" in
             (ref (Fst "ys_zs"), ref (Snd ("ys_zs"))).

  Lemma lsplit_ref_spec lxs (x : Z) (xs : list Z) :
    {{{ lxs ↦ encode (x::xs) }}}
      lsplit_ref #lxs
    {{{ lys lzs ys zs, RET (#lys,#lzs);
        ⌜(x::xs) = ys++zs⌝ ∗
        lxs ↦ encode (x::xs) ∗
        lys ↦ encode ys ∗
        lzs ↦ encode zs }}}.
  Proof.
    iIntros (Φ) "Hhd HΦ".
    wp_lam. wp_load. wp_apply (lsplit_spec (T:=Z))=> //; iIntros (_).
    wp_alloc lzs as "Hlzs".
    wp_alloc lys as "Hlys".
    wp_pures.
    iApply "HΦ".
    eauto 10 with iFrame.
  Qed.

  Definition compare_vals : val :=
    λ: "x" "y", "x" ≤ "y".

  Lemma compare_vals_spec (x y : Z) :
    {{{ True }}}
      compare_vals (encode x) (encode y)
    {{{ RET (encode (bool_decide (x ≤ y))); True }}}.
  Proof. iIntros (Φ) "_ HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

  Definition lmerge : val :=
    rec: "go" "hys" "hzs" :=
      if: llength "hys" = #0
      then "hzs"
      else if: llength "hzs" = #0
           then "hys"
           else let: "y" := lhead "hys" in
                let: "z" := lhead "hzs" in
                if: (compare_vals "y" "z")
                then lcons "y" ("go" (ltail "hys") "hzs")
                else lcons "z" ("go" "hys" (ltail "hzs")).

  Lemma list_merge_emp1 (ys : list Z) : list_merge (≤) [] ys = ys.
  Proof. induction ys; eauto. Qed.

  Lemma list_merge_emp2 (xs : list Z) : list_merge (≤) xs [] = xs.
  Proof. induction xs; eauto. Qed.

  Lemma lmerge_spec (ys zs : list Z) :
    {{{ True }}}
      lmerge (encode ys) (encode zs)
    {{{ RET (encode (list_merge (≤) ys zs)); True }}}.
  Proof.
    revert ys zs.
    iLöb as "IH".
    iIntros (ys zs Φ _) "HΦ".
    wp_lam.
    wp_apply (llength_spec (T:=Z))=> //; iIntros "_".
    destruct ys as [|y ys].
    { wp_pures. rewrite list_merge_emp1. by iApply ("HΦ"). }
    wp_apply (llength_spec (T:=Z))=> //; iIntros "_".
    destruct zs as [|z zs].
    { wp_pures. by iApply ("HΦ"). }
    wp_apply (lhead_spec (T:=Z))=> //; iIntros "_".
    wp_apply (lhead_spec (T:=Z))=> //; iIntros "_".
    wp_apply (compare_vals_spec)=> //; iIntros "_".
    rewrite list_merge_cons.
    destruct (decide (y ≤ z)).
    - rewrite bool_decide_true=> //.
      wp_apply (ltail_spec (T:=Z))=> //; iIntros (_).
      wp_apply ("IH")=> //; iIntros (_).
      wp_apply (lcons_spec (T:=Z))=> //.
    - rewrite bool_decide_false=> //.
      wp_apply (ltail_spec (T:=Z))=> //; iIntros (_).
      wp_apply ("IH")=> //; iIntros (_).
      wp_apply (lcons_spec (T:=Z))=> //.
  Qed.

  Definition lmerge_ref : val :=
    λ: "lxs" "hys" "hzs",
      "lxs" <- lmerge "hys" "hzs".

  Lemma lmerge_ref_spec ldx tmp ys zs :
    {{{ ldx ↦ tmp }}}
      lmerge_ref #ldx (encode ys) (encode zs)
    {{{ RET #(); ldx ↦ encode (list_merge (≤) ys zs) }}}.
  Proof.
    iIntros (Φ) "Hldx HΦ".
    wp_lam.
    wp_apply (lmerge_spec ys zs)=> //.
    iIntros (_).
    wp_store.
    by iApply ("HΦ").
  Qed.

  Definition list_sort_service : val :=
    rec: "go" "c" :=
      let: "xs" := recv "c" #Right in
      if: llength (!"xs") ≤ #1
      then send "c" #Right "xs"
      else let: "ys_zs" := lsplit_ref "xs" in
           let: "ys" := Fst "ys_zs" in
           let: "zs" := Snd "ys_zs" in
           let: "cy" := new_chan #() in Fork("go" "cy");;
           let: "cz" := new_chan #() in Fork("go" "cz");;
           send "cy" #Left "ys";;
           send "cz" #Left "zs";;
           let: "ys" := recv "cy" #Left in
           let: "zs" := recv "cz" #Left in
           lmerge_ref "xs" !"ys" !"zs";;
           send "c" #Right "xs".

  Lemma list_sort_service_spec γ c xs :
    {{{ ⟦ c @ Right : (<?> l @ l ↦ encode xs,
                          <!> l' @
                          ⌜l = l'⌝ ∗ (∃ ys : list Z,
                                      l' ↦ encode ys ∗
                                      ⌜Sorted (≤) ys⌝ ∗
                                      ⌜Permutation ys xs⌝),
                          TEnd) ⟧{N,γ} }}}
      list_sort_service c
    {{{ RET #(); ⟦ c @ Right : TEnd ⟧{N,γ} }}}.
  Proof.
    revert γ c xs.
    iLöb as "IH".
    iIntros (γ c xs Φ) "Hstr HΦ".
    wp_lam.
    wp_apply (recv_st_spec N loc with "Hstr").
    iIntros (v) "Hstr".
    iDestruct "Hstr" as "[Hstr HP]".
    wp_load.
    destruct xs.
    {
      wp_apply (llength_spec (T:=Z))=> //; iIntros (_).
      wp_apply (send_st_spec N loc with "[HP Hstr]")=> //. iFrame.
      eauto 10 with iFrame.
    }
    destruct xs.
    {
      wp_apply (llength_spec (T:=Z))=> //; iIntros (_).
      wp_apply (send_st_spec N loc with "[HP Hstr]")=> //. iFrame.
      eauto 10 with iFrame.
    }
    wp_apply (llength_spec (T:=Z))=> //; iIntros (_).
    wp_pures.
    assert (bool_decide (S (S (length xs)) ≤ 1) = false) as HSS.
    { apply bool_decide_false. lia. }
    rewrite HSS.
    wp_apply (lsplit_ref_spec with "HP");
      iIntros (hdy hdz ys zs) "(Heq & Hhdx & Hhdy & Hhdz)".
    iDestruct "Heq" as %->.
    wp_apply (new_chan_st_spec N
               (<!> l @ l ↦ encode ys,
                <?> l' @ ⌜l = l'⌝ ∗
                         (∃ ys' : list Z,
                             l' ↦ encode ys' ∗
                                ⌜Sorted (≤) ys'⌝ ∗
                                ⌜Permutation ys' ys⌝),
                TEnd))=>//;
             iIntros (cy γy) "[Hstly Hstry]".
    wp_apply (wp_fork with "[Hstry]").
    { iNext. iApply ("IH" with "Hstry"). iNext. by iIntros "Hstry". }
    wp_apply (new_chan_st_spec N
               (<!> l @ l ↦ encode zs,
                <?> l' @ ⌜l = l'⌝ ∗
                         (∃ zs' : list Z,
                             l' ↦ encode zs' ∗
                                ⌜Sorted (≤) zs'⌝ ∗
                                ⌜Permutation zs' zs⌝),
                TEnd))=>//;
    iIntros (cz γz) "[Hstlz Hstrz]".
    wp_apply (wp_fork with "[Hstrz]").
    { iNext. iApply ("IH" with "Hstrz"). iNext. by iIntros "Hstrz". }
    wp_apply (send_st_spec N loc with "[Hhdy Hstly]"). iFrame.
    iIntros "Hstly".
    wp_apply (send_st_spec N loc with "[Hhdz Hstlz]"). iFrame.
    iIntros "Hstlz".
    wp_apply (recv_st_spec N loc with "Hstly").
    iIntros (ly') "[Hstly Hys']".
    iDestruct "Hys'" as (<- ys') "(Hys' & Hys'_sorted_of)".
    iDestruct "Hys'_sorted_of" as %[Hys'_sorted Hys'_perm].
    wp_apply (recv_st_spec N loc with "Hstlz").
    iIntros (lz') "[Hstlz Hzs']".
    iDestruct "Hzs'" as (<- zs') "(Hzs' & Hzs'_sorted_of)".
    iDestruct "Hzs'_sorted_of" as %[Hzs'_sorted Hzs'_perm].
    wp_load.
    wp_load.
    wp_apply (lmerge_ref_spec with "Hhdx")=> //.
    iIntros "Hhdx".
    wp_apply (send_st_spec N loc with "[Hstr Hhdx]").
    {
      iFrame.
      iSplit=> //.
      iExists (list_merge (≤) ys' zs').
      iSplit=> //.
      iPureIntro.
      split.
      - apply Sorted_list_merge=> //.
        { intros x y. lia. }    (* Why is this needed? *)
      - rewrite merge_Permutation.
        by apply Permutation_app.
    }
    iIntros "Hstr".
    by iApply "HΦ".
  Qed.

  Definition list_sort : val :=
    λ: "xs",
    let: "c" := new_chan #() in
    Fork(list_sort_service "c");;
    send "c" #Left "xs";;
    recv "c" #Left.

  Lemma list_sort_spec l xs :
    {{{ l ↦ encode xs }}}
      list_sort #l
    {{{ ys, RET #l; l ↦ encode ys ∗ ⌜Sorted (≤) ys⌝ ∗ ⌜Permutation ys xs⌝ }}}.
  Proof.
     iIntros (Φ) "Hc HΦ".
     wp_lam.
     wp_apply (new_chan_st_spec N
                 (<!> l @ l ↦ encode xs,
                  <?> l' @ ⌜l = l'⌝ ∗
                           (∃ ys : list Z,
                               l' ↦ encode ys ∗
                                  ⌜Sorted (≤) ys⌝ ∗
                                  ⌜Permutation ys xs⌝), TEnd))=>//.
     iIntros (c γ) "[Hstl Hstr]".
     wp_apply (wp_fork with "[Hstr]").
     {
       iApply (list_sort_service_spec γ c xs with "[Hstr]"). iFrame.
       iNext. iNext. iIntros "Hstr". done.
     }
     wp_apply (send_st_spec N loc with "[Hc $Hstl]"). iFrame.
     iIntros "Hstl".
     wp_apply (recv_st_spec N loc with "Hstl").
     iIntros (v) "[Hstl HP]".
     iDestruct "HP" as (<- ys) "[Hys Hys_sorted_of]".
     iApply "HΦ". iFrame.
  Qed.

End ListSortExample.
