From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From osiris.utils Require Import list.

Definition compareZ : val :=
  λ: "x" "y", "x" ≤ "y".

Definition cont := true.
Definition stop := false.

Definition list_sort_elem_service_split : val :=
  rec: "go" "c" "c1" "c2" :=
    if: ~(recv "c")
    then send "c1" #stop;; send "c2" #stop
    else let: "x" := recv "c" in
         send "c1" #cont;; send "c1" "x";; "go" "c" "c2" "c1".

Definition list_sort_elem_service_copy : val :=
  rec: "go" "c" "cin" :=
    if: ~(recv "cin")
    then send "c" #stop
    else let: "x" := recv "cin" in send "c" #cont;; send "c" "x";; "go" "c" "cin".

Definition list_sort_elem_service_merge : val :=
  rec: "go" "c" "x1" "c1" "c2" :=
    if: ~recv "c2"
    then send "c" #cont;; send "c" "x1";; list_sort_elem_service_copy "c" "c1"
    else let: "x2" := recv "c2" in
         if: compareZ "x1" "x2"
         then send "c" #cont;; send "c" "x1";; "go" "c" "x2" "c2" "c1"
         else send "c" #cont;; send "c" "x2";; "go" "c" "x1" "c1" "c2".

Definition list_sort_elem_service : val :=
  rec: "go" "c" :=
    if: ~(recv "c")
    then send "c" #stop
    else let: "x" := recv "c" in
         if: ~(recv "c")
         then send "c" #cont;; send "c" "x";; send "c" #stop
         else let: "y" := recv "c" in
              let: "c1" := start_chan ("go") in
              let: "c2" := start_chan ("go") in
              send "c1" #cont;; send "c1" "x";;
              send "c2" #cont;; send "c2" "y";;
              list_sort_elem_service_split "c" "c1" "c2";;
              let: "x" := (if: recv "c1" then recv "c1" else assert #false) in
              list_sort_elem_service_merge "c" "x" "c1" "c2".

Section list_sort_elem.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).

  Definition tail_protocol_aux (rec : list Z -d> list Z -d> iProto Σ)
    : (list Z -d> list Z -d> iProto Σ) :=
    λ xs ys,
    (<?> (b:bool), MSG #b
        {{ if b then True else ⌜ ys ≡ₚ xs ⌝ }};
      if b
      then <?> (y:Z), MSG #y {{ ⌜ TlRel (≤) y ys ⌝ }}; (rec : _ -> _ -> iProto Σ) xs (ys++[y])
      else END)%proto.

  Instance tail_protocol_aux_contractive : Contractive (tail_protocol_aux).
  Proof.
    intros n p p' Hp. rewrite /tail_protocol_aux.
    intros xs ys.
    apply iProto_message_ne=> b //=.
    destruct b.
    - apply iProto_message_contractive=> //=.
      intros x.
      destruct n as [|n]; simpl in *; try done. apply Hp.
    - done.
  Qed.
  
  Definition tail_protocol : (list Z -d> list Z -d> iProto Σ) := fixpoint (tail_protocol_aux).
  Lemma tail_protocol_unfold xs ys:
    tail_protocol xs ys≡ tail_protocol_aux tail_protocol xs ys.
  Proof. apply (fixpoint_unfold tail_protocol_aux). Qed.
  
  Definition helper_protocol_aux (rec : list Z -d> iProto Σ)
    : (list Z -d> iProto Σ) :=
    λ xs,
    (<!> (b:bool), MSG #b;
       if b
       then <!> (x:Z), MSG #x; (rec : _ → iProto Σ) (xs++[x])
       else tail_protocol xs [])%proto.
  
  Instance helper_protocol_aux_contractive : Contractive (helper_protocol_aux).
  Proof.
    intros n p p' Hp. rewrite /helper_protocol_aux.
    intros xs.
    apply iProto_message_ne=> b //=.
    destruct b.
    - apply iProto_message_contractive=> //=.
      intros x.
      destruct n as [|n]; simpl in *; done.
    - done.
  Qed.

  Definition helper_protocol : (list Z -d> iProto Σ) := fixpoint (helper_protocol_aux).
  Lemma helper_protocol_unfold xs :
    helper_protocol xs ≡ helper_protocol_aux helper_protocol xs.
  Proof. apply (fixpoint_unfold helper_protocol_aux). Qed.

  Definition list_sort_elem_protocol := helper_protocol [].

  Lemma list_sort_elem_service_split_spec c c1 c2 (xs xs1 xs2 : list Z) :
    {{{
         c ↣ iProto_dual (helper_protocol xs) @ N ∗ 
         c1 ↣ helper_protocol xs1 @ N ∗ 
         c2 ↣ helper_protocol xs2 @ N
     }}}
      list_sort_elem_service_split c c1 c2
    {{{ xs' xs1' xs2', RET #();
        c ↣ iProto_dual (tail_protocol (xs++xs') []) @ N ∗
        c1 ↣ tail_protocol (xs1++xs1') [] @ N ∗ 
        c2 ↣ tail_protocol (xs2++xs2') [] @ N ∗
        ⌜xs' ≡ₚ  xs1' ++ xs2'⌝
      }}}.
  Proof.
    iIntros (Ψ) "(Hc & Hc1 & Hc2) HΨ". iLöb as "IH" forall (c c1 c2 xs xs1 xs2 Ψ).
    wp_rec.
    rewrite helper_protocol_unfold.
    wp_apply (recv_proto_spec N with "Hc")=> //=.
    iIntros (b) "Hc _".
    destruct b.
    - wp_apply (recv_proto_spec N with "Hc")=> //=.
      iIntros (x) "Hc _".
      wp_pures.
      rewrite (helper_protocol_unfold xs1).
      wp_apply (send_proto_spec N with "Hc1")=> //=.
      iExists cont. iSplit; first done; iSplit; first done; iIntros "!> Hc1".
      wp_apply (send_proto_spec N with "Hc1")=> //=.
      iExists x. iSplit; first done; iSplit; first done; iIntros "!> Hc1".
      wp_apply ("IH" with "[Hc] [Hc2] [Hc1]")=> //.
      iIntros (xs' xs1' xs2') "(Hc & Hc2 & Hc1 & Hperm)".
      iApply "HΨ".
      iSplitL "Hc".
      rewrite -app_assoc. rewrite -cons_middle. iApply "Hc".
      iSplitL "Hc1".
      rewrite -app_assoc. rewrite -cons_middle. iApply "Hc1".
      iFrame.
      iDestruct "Hperm" as %Hperm.
      iPureIntro.
      simpl. apply Permutation_cons.
      rewrite Hperm.
      apply Permutation_app_comm.
    - rewrite (helper_protocol_unfold xs1).
      wp_apply (send_proto_spec N with "Hc1")=> //=.
      iExists stop. iSplit; first done; iSplit; first done; iIntros "!> Hc1".
      rewrite (helper_protocol_unfold xs2).
      wp_apply (send_proto_spec N with "Hc2")=> //=.
      iExists stop. iSplit; first done; iSplit; first done; iIntros "!> Hc2".
      iSpecialize ("HΨ" $![] [] []).
      iApply "HΨ".
      repeat rewrite app_nil_r.
      iFrame.
      done.
  Qed.

  Lemma cmp_spec :
    (∀ x y,
      {{{ True }}}
        compareZ #x #y
      {{{ RET #(bool_decide (x ≤ y)); True }}})%I.
  Proof.
    iIntros (x y Φ).
    iModIntro. 
    iIntros "_ HΦ".
    wp_lam.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma list_sort_elem_service_copy_spec c cin xs ys zs xs' ys' :
    xs ≡ₚ  xs' ++ zs →
    ys ≡ₚ  ys' ++ zs →
    Sorted (≤) ys →
    (∀ x, TlRel Z.le x ys' → TlRel Z.le x ys) →
    {{{
      c ↣ iProto_dual (tail_protocol xs ys) @ N ∗
      cin ↣ tail_protocol xs' ys' @ N
    }}}
      list_sort_elem_service_copy c cin
    {{{ RET #(); c ↣ END @ N ∗ cin ↣ END @ N }}}.
  Proof.
    iIntros (H1 H2 Hsorted Hrel Ψ) "[Hc Hcin] HΨ".
    iLöb as "IH" forall (c cin xs ys xs' ys' H1 H2 Hsorted Hrel).
    wp_rec.
    rewrite (tail_protocol_unfold xs').
    wp_apply (recv_proto_spec N with "Hcin")=> //=.
    iIntros (b) "Hcin HP".
    destruct b.
    - iClear "HP".
      wp_apply (recv_proto_spec N with "Hcin")=> //=.
      iIntros (x) "Hcin".
      iIntros (HP).
      rewrite (tail_protocol_unfold xs).
      wp_apply (send_proto_spec N with "Hc")=> //=.
      iExists cont. iSplit; first done; iSplit; first done; iIntros "!> Hc".
      wp_apply (send_proto_spec N with "Hc")=> //=.
      iExists x. iSplit; first done; iSplit; first by auto. iIntros "!> Hc".
      wp_apply ("IH" with "[%] [%] [%] [%] Hc Hcin")=> //.
      { by rewrite H2 -app_assoc -app_assoc (Permutation_app_comm zs). }
      { apply Sorted_snoc; auto. }
      { intros x'. inversion 1; discriminate_list || simplify_list_eq.
          by constructor. }
    - rewrite (tail_protocol_unfold xs).
      wp_apply (send_proto_spec N with "Hc")=> //=.
      iExists stop. iSplit; first done.
      iDestruct "HP" as %HP.
      simpl.
      iSplit.
      { by rewrite H1 -HP H2. }
      iIntros "!> Hc".
      iApply "HΨ".
      iFrame.
  Qed.
    
  Lemma list_sort_elem_service_merge_spec c c1 c2 xs ys xs1 xs2 y1 ys1 ys2 :
    xs ≡ₚ xs1 ++ xs2 →
    ys ≡ₚ ys1 ++ ys2 →
    Sorted (≤) ys →
    TlRel (≤) y1 ys →
    (∀ x, TlRel Z.le x ys2 → x ≤ y1 → TlRel Z.le x ys) →
    {{{
      c ↣ iProto_dual (tail_protocol xs ys) @ N ∗ 
      c1 ↣ tail_protocol xs1 (ys1 ++ [y1]) @ N ∗ 
      c2 ↣ tail_protocol xs2 ys2 @ N
    }}}
      list_sort_elem_service_merge c #y1 c1 c2
    {{{ RET #(); c ↣ END @ N ∗ c1 ↣ END @ N ∗ c2 ↣ END @ N}}}.
  Proof.
    iIntros (Hxs Hys Hsort Htl Htl_le Ψ) "(Hc & Hc1 & Hc2) HΨ".
    iLöb as "IH" forall (c1 c2 xs1 xs2 ys y1 ys1 ys2 Hxs Hys Hsort Htl Htl_le).
    wp_rec.
    rewrite (tail_protocol_unfold xs).
    rewrite (tail_protocol_unfold xs2).
    wp_apply (recv_proto_spec N with "Hc2")=> //=.
    iIntros (b) "Hc2 HP".
    destruct b.
    - iClear "HP".
      wp_apply (recv_proto_spec N with "Hc2")=> //=.
      iIntros (x) "Hc2"; iIntros (Htl2).
      wp_pures.
      wp_apply (cmp_spec)=> //. iIntros (_).
      case_bool_decide.
      + wp_apply (send_proto_spec N with "Hc")=> //=.
        iExists cont. iSplit; first done; iSplit; first done; iIntros "!> Hc".
        wp_apply (send_proto_spec N with "Hc")=> //=.
        iExists y1. iSplit; first done. iSplit; first done.
        iIntros "!> Hc".
        wp_apply ("IH" with "[%] [%] [%] [%] [%] Hc Hc2 Hc1").
        { by rewrite comm. }
        { by rewrite assoc (comm _ ys2) Hys. }
        { by apply Sorted_snoc. }
        { by constructor. }
        { intros x'. inversion 1; discriminate_list || simplify_list_eq.
          constructor; lia. }
        iIntros "(?&?&?)". iApply "HΨ"; iFrame.
      + wp_apply (send_proto_spec N with "Hc")=> //=.
        iExists cont. iSplit; first done; iSplit; first done; iIntros "!> Hc".
        wp_apply (send_proto_spec N with "Hc")=> //=.
        iExists x. iSplit; first done. iSplit.
        { iPureIntro. auto with lia. }
        iIntros "!> Hc".
        wp_apply ("IH" with "[% //] [%] [%] [%] [%] Hc Hc1 Hc2 [$]").
        { by rewrite Hys assoc. }
        { apply Sorted_snoc; auto with lia. }
        { constructor. lia. }
        { intros x'. inversion 1; discriminate_list || simplify_list_eq.
          constructor; lia. }
    - wp_apply (send_proto_spec N with "Hc")=> //=.
      iExists cont. iSplit; first done; iSplit; first done; iIntros "!> Hc".
      wp_apply (send_proto_spec N with "Hc")=> //=.
      iDestruct "HP" as %HP.
      iExists y1. iSplit; first done; iSplit; first done; iIntros "!> Hc".
      wp_apply (list_sort_elem_service_copy_spec with "[$Hc $Hc1]")=> //.
      { by rewrite Hys -app_assoc -app_assoc (Permutation_app_comm [y1]) HP. }
      { by apply Sorted_snoc. }
      { intros x'. inversion 1; discriminate_list || simplify_list_eq.
          constructor; lia. }
      iIntros "[Hc Hc1]".
      iApply "HΨ".
      iFrame.
  Qed.

  Lemma list_sort_elem_service_spec c :
    {{{ c ↣ iProto_dual list_sort_elem_protocol @ N }}}
      list_sort_elem_service c
    {{{ RET #(); c ↣ END @ N }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec.
    rewrite /list_sort_elem_protocol.
    rewrite {2}helper_protocol_unfold.
    wp_apply (recv_proto_spec N with "Hc")=> //=.
    iIntros (b) "Hc _".
    destruct b.
    - wp_apply (recv_proto_spec N with "Hc")=> //=.
      iIntros (x1) "Hc _".
      rewrite (helper_protocol_unfold [x1]).
      wp_apply (recv_proto_spec N with "Hc")=> //=.
      iIntros (b) "Hc _".
      destruct b.
      + wp_apply (recv_proto_spec N with "[Hc]")=> //=.
        iIntros (x2) "Hc _".
        wp_apply (start_chan_proto_spec N (list_sort_elem_protocol)).
        { iIntros (cy) "Hcy".
          iApply ("IH" with "Hcy")=>//. iNext. iIntros "Hcy". done. }
        iIntros (cy) "Hcy".
        wp_apply (start_chan_proto_spec N (list_sort_elem_protocol)).
        { iIntros (cz) "Hcz".
          iApply ("IH" with "Hcz")=>//. iNext. iIntros "Hcz". done. }
        iIntros (cz) "Hcz".
        rewrite /list_sort_elem_protocol.
        rewrite {2}(helper_protocol_unfold []).
        wp_apply (send_proto_spec N with "Hcy")=> //=.
        iExists cont. iSplit; first done; iSplit; first done; iIntros "!> Hcy".
        wp_apply (send_proto_spec N with "Hcy")=> //=.
        iExists x1. iSplit; first done; iSplit; first done; iIntros "!> Hcy".
        rewrite {2}(helper_protocol_unfold []).
        wp_apply (send_proto_spec N with "Hcz")=> //=.
        iExists cont. iSplit; first done; iSplit; first done; iIntros "!> Hcz".
        wp_apply (send_proto_spec N with "Hcz")=> //=.
        iExists x2. iSplit; first done; iSplit; first done; iIntros "!> Hcz".
        wp_apply (list_sort_elem_service_split_spec with "[Hc Hcy Hcz]")=> //.
        iFrame.
        iIntros (xs' xs1' xs2') "(Hc & Hcy & Hcz & Hperm)".
        iDestruct "Hperm" as %Hperm.
        wp_pures.
        rewrite (tail_protocol_unfold ([x1] ++ xs1')).
        wp_apply (recv_proto_spec N with "[Hcy]")=> //=.
        iIntros (b) "Hcy HP".
        destruct b; last first.
        { by iDestruct "HP" as %?%Permutation_nil_cons. }
        iClear "HP".
        wp_apply (recv_proto_spec N with "[Hcy]")=> //=.
        iIntros (x) "Hcy _".
        wp_apply (list_sort_elem_service_merge_spec _ _ _ _ [] _ _ _ [] []
          with "[$Hc $Hcy $Hcz]"); auto using TlRel_nil.
        { by rewrite /= Hperm Permutation_middle. }
        iIntros "(Hc & Hcy & Hcz)".
        by iApply "HΨ".
      + rewrite (tail_protocol_unfold [x1] []).
        wp_apply (send_proto_spec N with "[Hc]")=> //=.
        iExists cont.
        iSplitR=> //.
        iSplitR=> //.
        iIntros "!> Hc".
        wp_apply (send_proto_spec N with "[Hc]")=> //=.
        iExists x1.
        iSplitR=> //.
        iSplitR; first by auto using TlRel_nil.
        iIntros "!> Hc".
        rewrite (tail_protocol_unfold [x1] [x1]).
        wp_apply (send_proto_spec N with "[Hc]")=> //=.
        iExists stop.
        iSplitR=> //.
        iSplitR=> //=.
        iIntros "!> Hc". by iApply "HΨ".
    - wp_pures.
      rewrite (tail_protocol_unfold [] []).
      wp_apply (send_proto_spec N with "[Hc]")=> //=.
      iExists false.
      iSplitR=>//.
      iSplitR=>//.
      iNext.
      iIntros "Hc".
      iApply "HΨ". iApply "Hc".
  Qed.
End list_sort_elem.
