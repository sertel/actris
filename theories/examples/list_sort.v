From stdpp Require Import sorting.
Require Import Coq.Lists.List.
Require Import Omega.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Import proofmode notation.
From osiris.proto Require Import list channel stype_enc.
From iris.base_logic Require Import invariants.

Section ListSortExample.
  Context `{!heapG Σ} `{logrelG val Σ} (N : namespace).

  Section SortService.
    Context `{EncDec T}.
    Context (R : relation T) `{!Total R} `{∀ x y, Decision (R x y)}.

    Definition lsplit_ref : val :=
      λ: "xs", let: "ys_zs" := lsplit !"xs" in
               (ref (Fst "ys_zs"), ref (Snd ("ys_zs"))).

    Lemma lsplit_ref_spec lxs (x : T) (xs : list T) :
      {{{ lxs ↦ encode (x::xs) }}}
        lsplit_ref #lxs
      {{{ lys lzs ys zs, RET (#lys,#lzs);
          ⌜(x::xs) = ys++zs⌝ ∗
                       lxs ↦ encode (x::xs) ∗
                       lys ↦ encode ys ∗
                       lzs ↦ encode zs }}}.
    Proof.
      iIntros (Φ) "Hhd HΦ".
      wp_lam. wp_load. wp_apply (lsplit_spec)=> //. iIntros (ys zs <-).
      wp_alloc lzs as "Hlzs".
      wp_alloc lys as "Hlys".
      wp_pures.
      iApply "HΦ".
      eauto 10 with iFrame.
    Qed.

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

    Lemma list_merge_emp1 (ys : list T) : list_merge (R) [] ys = ys.
    Proof. induction ys; eauto. Qed.

    Lemma list_merge_emp2 (xs : list T) : list_merge (R) xs [] = xs.
    Proof. induction xs; eauto. Qed.

    Definition cmp_spec (cmp : val) : iProp Σ :=
      (∀ x y, {{{ True }}}
                cmp (encode x) (encode y)
              {{{ RET encode (bool_decide (R x y)); True}}})%I.

    Lemma lmerge_spec  (cmp : val) (ys zs : list T) :
      cmp_spec cmp -∗
      {{{ True }}}
        lmerge cmp (encode ys) (encode zs)
      {{{ RET (encode (list_merge (R) ys zs)); True }}}.
    Proof.
      revert ys zs.
      iLöb as "IH".
      iIntros (ys zs).
      iIntros "#Hcmp_spec".
      iIntros (Φ).
      iModIntro.
      iIntros (_) "HΦ".
      wp_lam.
      destruct ys as [|y ys].
      { wp_pures. rewrite list_merge_emp1. by iApply ("HΦ"). }
      destruct zs as [|z zs].
      { wp_pures. rewrite list_merge_emp2. by iApply ("HΦ"). }
      wp_apply (lhead_spec)=> //; iIntros "_".
      wp_apply (lhead_spec)=> //; iIntros "_".
      wp_apply ("Hcmp_spec")=> //; iIntros "_".
      rewrite list_merge_cons.
      destruct (decide (R y z)).
      - rewrite bool_decide_true=> //.
        wp_apply (ltail_spec)=> //; iIntros (_).
        wp_apply ("IH")=> //; iIntros (_).
        wp_apply (lcons_spec)=> //.
      - rewrite bool_decide_false=> //.
        wp_apply (ltail_spec)=> //; iIntros (_).
        wp_apply ("IH")=> //; iIntros (_).
        wp_apply (lcons_spec)=> //.
    Qed.

    Definition lmerge_ref : val :=
      λ: "cmp" "lxs" "hys" "hzs",
      "lxs" <- lmerge "cmp" "hys" "hzs".

    Lemma lmerge_ref_spec (cmp : val) ldx tmp ys zs :
      cmp_spec cmp -∗
      {{{ ldx ↦ tmp }}}
        lmerge_ref cmp #ldx (encode ys) (encode zs)
      {{{ RET #(); ldx ↦ encode (list_merge R ys zs) }}}.
    Proof.
      iIntros "#Hcmp_spec".
      iIntros (Φ).
      iModIntro.
      iIntros "Hldx HΦ".
      wp_lam.
      wp_apply (lmerge_spec cmp ys zs with "Hcmp_spec")=> //.
      iIntros (_).
      wp_store.
      by iApply ("HΦ").
    Qed.

    Definition list_sort_service : val :=
      rec: "go" "c" :=
        let: "cmp" := recv "c" #Right in
        let: "xs" := recv "c" #Right in
        if: llength (!"xs") ≤ #1
        then send "c" #Right "xs"
        else let: "ys_zs" := lsplit_ref "xs" in
             let: "ys" := Fst "ys_zs" in
             let: "zs" := Snd "ys_zs" in
             let: "cy" := new_chan #() in Fork("go" "cy");;
             let: "cz" := new_chan #() in Fork("go" "cz");;
             send "cy" #Left "cmp";;
             send "cy" #Left "ys";;
             send "cz" #Left "cmp";;
             send "cz" #Left "zs";;
             let: "ys" := recv "cy" #Left in
             let: "zs" := recv "cz" #Left in
             lmerge_ref "cmp" "xs" !"ys" !"zs";;
             send "c" #Right "xs".

    Definition sort_protocol xs :=
      (<?> cmp @ cmp_spec cmp,
       <?> l @ l ↦ encode xs,
       <!> l' @ ⌜l = l'⌝ ∗
                (∃ ys : list T,
                    l' ↦ encode ys ∗
                       ⌜Sorted (R) ys⌝ ∗
                       ⌜Permutation ys xs⌝),
       TEnd)%stype.

    Lemma list_sort_service_spec γ c xs :
      {{{ ⟦ c @ Right : sort_protocol xs ⟧{N,γ} }}}
        list_sort_service c
      {{{ RET #(); ⟦ c @ Right : TEnd ⟧{N,γ} }}}.
    Proof.
      revert γ c xs.
      iLöb as "IH".
      iIntros (γ c xs Φ) "Hstr HΦ".
      wp_lam.
      wp_apply (recv_st_spec N val with "Hstr").
      iIntros (cmp) "[Hstr #Hcmp_spec]".
      wp_pures.
      wp_apply (recv_st_spec N loc with "Hstr").
      iIntros (v) "Hstr".
      iDestruct "Hstr" as "[Hstr HP]".
      wp_load.
      destruct xs.
      {
        wp_apply (llength_spec)=> //; iIntros (_).
        wp_apply (send_st_spec N loc with "[HP Hstr]")=> //. iFrame.
        eauto 10 with iFrame.
      }
      destruct xs.
      {
        wp_apply (llength_spec)=> //; iIntros (_).
        wp_apply (send_st_spec N loc with "[HP Hstr]")=> //. iFrame.
        eauto 10 with iFrame.
      }
      wp_apply (llength_spec)=> //; iIntros (_).
      wp_pures.
      assert (bool_decide (S (S (length xs)) ≤ 1) = false) as HSS.
      { apply bool_decide_false. lia. }
      rewrite HSS.
      wp_apply (lsplit_ref_spec with "HP");
        iIntros (hdy hdz ys zs) "(Heq & Hhdx & Hhdy & Hhdz)".
      iDestruct "Heq" as %->.
      wp_apply (new_chan_st_spec N _ (sort_protocol ys))=> //.
      iIntros (cy γy) "[Hstly Hstry]".
      wp_apply (wp_fork with "[Hstry]").
      { iNext. iApply ("IH" with "Hstry"). iNext. by iIntros "Hstry". }
      wp_apply (new_chan_st_spec N _ (sort_protocol zs))=> //.
      iIntros (cz γz) "[Hstlz Hstrz]".
      wp_apply (wp_fork with "[Hstrz]").
      { iNext. iApply ("IH" with "Hstrz"). iNext. by iIntros "Hstrz". }
      wp_apply (send_st_spec N val with "[Hstly]"). iFrame. done.
      iIntros "Hstly".
      wp_apply (send_st_spec N loc with "[Hhdy Hstly]"). iFrame.
      iIntros "Hstly".
      wp_apply (send_st_spec N val with "[Hstlz]"). iFrame. done.
      iIntros "Hstlz".
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
      wp_apply (lmerge_ref_spec with "Hcmp_spec Hhdx").
      iIntros "Hhdx".
      wp_apply (send_st_spec N loc with "[Hstr Hhdx]").
      {
        iFrame.
        iSplit=> //.
        iExists (list_merge R ys' zs').
        iSplit=> //.
        iPureIntro.
        split.
        - apply Sorted_list_merge=> //.
        - rewrite merge_Permutation.
            by apply Permutation_app.
      }
      iIntros "Hstr".
      by iApply "HΦ".
    Qed.
  End SortService.

  Definition compare_vals : val :=
    λ: "x" "y", "x" ≤ "y".

  Lemma compare_vals_spec (x y : Z) :
    {{{ True }}}
      compare_vals (encode x) (encode y)
    {{{ RET (encode (bool_decide (x ≤ y))); True }}}.
  Proof. iIntros (Φ) "_ HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

  Definition list_sort : val :=
    λ: "xs",
    let: "c" := new_chan #() in
    Fork(list_sort_service "c");;
        send "c" #Left compare_vals;;
        send "c" #Left "xs";;
        recv "c" #Left.

  Lemma list_sort_spec l xs :
    {{{ l ↦ encode xs }}}
      list_sort #l
    {{{ ys, RET #l; l ↦ encode ys ∗ ⌜Sorted (≤) ys⌝ ∗ ⌜Permutation ys xs⌝ }}}.
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
     wp_apply (send_st_spec N val with "[$Hstl]").
     {
       iIntros (x y Φ').
       iApply compare_vals_spec=> //.
     }
     iIntros "Hstl".
     wp_apply (send_st_spec N loc with "[Hc $Hstl]"). iFrame.
     iIntros "Hstl".
     wp_apply (recv_st_spec N loc with "Hstl").
     iIntros (v) "[Hstl HP]".
     iDestruct "HP" as (<- ys) "[Hys Hys_sorted_of]".
     iApply "HΦ". iFrame.
  Qed.
End ListSortExample.
