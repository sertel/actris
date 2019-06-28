From stdpp Require Import sorting.
From osiris.channel Require Import proto_channel.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From osiris.utils Require Import list.

Definition cont := true.
Definition stop := false.

Definition list_sort_elem_service_split : val :=
  rec: "go" "c" "c1" "c2" :=
    if: ~(recv "c") then send "c1" #stop;; send "c2" #stop else
    let: "x" := recv "c" in
    send "c1" #cont;; send "c1" "x";;
    "go" "c" "c2" "c1".

Definition list_sort_elem_service_move : val :=
  rec: "go" "c" "cin" :=
    if: ~(recv "cin") then send "c" #stop else
    let: "x" := recv "cin" in
    send "c" #cont;; send "c" "x";;
    "go" "c" "cin".

Definition list_sort_elem_service_merge : val :=
  rec: "go" "cmp" "c" "x1" "c1" "c2" :=
    if: ~recv "c2" then
      send "c" #cont;; send "c" "x1";;
      list_sort_elem_service_move "c" "c1"
    else
      let: "x2" := recv "c2" in
      if: "cmp" "x1" "x2" then
        send "c" #cont;; send "c" "x1";; "go" "cmp" "c" "x2" "c2" "c1"
      else
        send "c" #cont;; send "c" "x2";; "go" "cmp" "c" "x1" "c1" "c2".

Definition list_sort_elem_service : val :=
  rec: "go" "cmp" "c" :=
    if: ~(recv "c") then send "c" #stop else
    let: "x" := recv "c" in
    if: ~(recv "c") then send "c" #cont;; send "c" "x";; send "c" #stop else
    let: "y" := recv "c" in
    let: "c1" := start_chan (λ: "c", "go" "cmp" "c") in
    let: "c2" := start_chan (λ: "c", "go" "cmp" "c") in
    send "c1" #cont;; send "c1" "x";;
    send "c2" #cont;; send "c2" "y";;
    list_sort_elem_service_split "c" "c1" "c2";;
    let: "x" := (if: recv "c1" then recv "c1" else assert #false) in
    list_sort_elem_service_merge "cmp" "c" "x" "c1" "c2".

(** This definition is also in list_sort, move elsewhere *)
Definition cmp_spec `{!heapG Σ} {A} (I : A → val → iProp Σ)
    (R : relation A) `{!RelDecision R} (cmp : val) : iProp Σ :=
  (∀ x x' v v',
    {{{ I x v ∗ I x' v' }}}
      cmp v v'
    {{{ RET #(bool_decide (R x x')); I x v ∗ I x' v' }}})%I.

Section list_sort_elem.
  Context `{!heapG Σ, !proto_chanG Σ} (N : namespace).
  Context {A} (I : A → val → iProp Σ) (R : relation A) `{!RelDecision R, !Total R}.

  Definition tail_protocol_aux (xs : list (A * val))
      (rec : list (A * val) -d> iProto Σ) : list (A * val) -d> iProto Σ := λ ys,
    ((<?> y v, MSG v {{ ⌜ TlRel R y (fst <$> ys) ⌝ ∗ I y v }}; (rec : _ → iProto Σ) (ys ++ [(y,v)]))
     <&{⌜ ys ≡ₚ xs ⌝}> END)%proto.

  Instance tail_protocol_aux_contractive xs : Contractive (tail_protocol_aux xs).
  Proof.
    intros n p p' Hp ys. apply iProto_branch_ne=> //=.
    apply iProto_message_contractive=> x //=. destruct n as [|n]=> //=.
  Qed.
  Definition tail_protocol (xs : list (A * val)) : list (A * val) → iProto Σ :=
    fixpoint (tail_protocol_aux xs).
  Lemma tail_protocol_unfold xs ys:
    tail_protocol xs ys ≡ tail_protocol_aux xs (tail_protocol xs) ys.
  Proof. apply (fixpoint_unfold (tail_protocol_aux _)). Qed.

  Definition head_protocol_aux
      (rec : list (A * val) -d> iProto Σ) : list (A * val) -d> iProto Σ := λ xs,
    ((<!> x v, MSG v {{ I x v }}; (rec : _ → iProto Σ) (xs ++ [(x,v)]))
     <+> tail_protocol xs [])%proto.

  Instance head_protocol_aux_contractive : Contractive head_protocol_aux.
  Proof.
    intros n p p' Hp xs. apply iProto_branch_ne=> //=.
    apply iProto_message_contractive=> //= x. destruct n as [|n]=> //=.
  Qed.

  Definition head_protocol : list (A * val) → iProto Σ := fixpoint head_protocol_aux.
  Lemma head_protocol_unfold xs :
    head_protocol xs ≡ head_protocol_aux head_protocol xs.
  Proof. apply (fixpoint_unfold head_protocol_aux). Qed.

  Definition list_sort_elem_protocol : iProto Σ := head_protocol [].

  Lemma list_sort_elem_service_split_spec c c1 c2 xs xs1 xs2 :
    {{{
      c ↣ iProto_dual (head_protocol xs) @ N ∗ 
      c1 ↣ head_protocol xs1 @ N ∗ c2 ↣ head_protocol xs2 @ N
    }}}
      list_sort_elem_service_split c c1 c2
    {{{ xs' xs1' xs2', RET #();
      ⌜xs' ≡ₚ xs1' ++ xs2'⌝ ∗
      c ↣ iProto_dual (tail_protocol (xs ++ xs') []) @ N ∗
     c1 ↣ tail_protocol (xs1 ++ xs1') [] @ N ∗ c2 ↣ tail_protocol (xs2 ++ xs2') [] @ N
    }}}.
  Proof.
    iIntros (Ψ) "(Hc & Hc1 & Hc2) HΨ". iLöb as "IH" forall (c c1 c2 xs xs1 xs2 Ψ).
    wp_rec.
    rewrite head_protocol_unfold.
    wp_apply (branch_spec with "Hc"); iIntros ([]) "[Hc _]"; wp_pures.
    - wp_apply (recv_proto_spec with "Hc"); iIntros (x v) "/= Hc HI".
      rewrite (head_protocol_unfold xs1).
      wp_apply (select_spec with "[$Hc1]")=> //=; iIntros "Hc1".
      wp_apply (send_proto_spec with "Hc1"); simpl.
      iExists x, v. iSplit; [done|]. iIntros "{$HI} !> Hc1".
      wp_apply ("IH" with "Hc Hc2 Hc1").
      iIntros (xs' xs1' xs2'); iDestruct 1 as (Hxs') "(Hc & Hc2 & Hc1)".
      rewrite -!(assoc_L (++)).
      iApply "HΨ". iFrame "Hc Hc1 Hc2". by rewrite Hxs' (comm (++) xs1') assoc_L.
    - rewrite (head_protocol_unfold xs1) (head_protocol_unfold xs2).
      wp_apply (select_spec with "[$Hc1]")=> //=; iIntros "Hc1".
      wp_apply (select_spec with "[$Hc2]")=> //=; iIntros "Hc2".
      iApply ("HΨ" $! [] [] []). rewrite !right_id_L. by iFrame.
  Qed.

  Lemma list_sort_elem_service_move_spec c cin xs ys zs xs' ys' :
    xs ≡ₚ xs' ++ zs →
    ys ≡ₚ ys' ++ zs →
    Sorted R (fst <$> ys) →
    (∀ x, TlRel R x (fst <$> ys') → TlRel R x (fst <$> ys)) →
    {{{
      c ↣ iProto_dual (tail_protocol xs ys) @ N ∗
      cin ↣ tail_protocol xs' ys' @ N
    }}}
      list_sort_elem_service_move c cin
    {{{ RET #(); c ↣ END @ N ∗ cin ↣ END @ N }}}.
  Proof.
    iIntros (Hxs Hys Hsorted Hrel Ψ) "[Hc Hcin] HΨ".
    iLöb as "IH" forall (c cin xs ys xs' ys' Hxs Hys Hsorted Hrel).
    wp_rec.
    rewrite (tail_protocol_unfold xs').
    wp_apply (branch_spec with "Hcin"); iIntros ([]) "[Hcin Hys']".
    - iClear "Hys'".
      wp_apply (recv_proto_spec with "Hcin"); iIntros (x v) "/= Hcin".
      iDestruct 1 as (Hx) "HI".
      rewrite (tail_protocol_unfold xs).
      wp_apply (select_spec with "[$Hc]")=> //=; iIntros "Hc".
      wp_apply (send_proto_spec with "Hc"); simpl.
      iExists x, v. iFrame "HI". do 2 (iSplit; [by auto|]); iIntros "!> Hc".
      wp_apply ("IH" with "[%] [%] [%] [%] Hc Hcin HΨ").
      { done. }
      { by rewrite Hys -!assoc_L (comm _ zs). }
      { rewrite fmap_app /=. apply Sorted_snoc; auto. }
      { intros x'. rewrite !fmap_app.
        inversion 1; discriminate_list || simplify_list_eq. by constructor. }
    - iDestruct "Hys'" as %Hys'. rewrite (tail_protocol_unfold xs).
      wp_apply (select_spec with "[$Hc]")=> //=.
      { by rewrite Hys Hxs Hys'. }
      iIntros "Hc". iApply "HΨ". iFrame.
  Qed.

  Lemma list_sort_elem_service_merge_spec cmp c c1 c2 xs ys xs1 xs2 y1 w1 ys1 ys2 :
    xs ≡ₚ xs1 ++ xs2 →
    ys ≡ₚ ys1 ++ ys2 →
    Sorted R (fst <$> ys) →
    TlRel R y1 (fst <$> ys) →
    (∀ x, TlRel R x (fst <$> ys2) → R x y1 → TlRel R x (fst <$> ys)) →
    cmp_spec I R cmp -∗
    {{{
      c ↣ iProto_dual (tail_protocol xs ys) @ N ∗ 
      c1 ↣ tail_protocol xs1 (ys1 ++ [(y1,w1)]) @ N ∗ c2 ↣ tail_protocol xs2 ys2 @ N ∗
      I y1 w1
    }}}
      list_sort_elem_service_merge cmp c w1 c1 c2
    {{{ RET #(); c ↣ END @ N ∗ c1 ↣ END @ N ∗ c2 ↣ END @ N }}}.
  Proof.
    iIntros (Hxs Hys Hsort Htl Htl_le) "#Hcmp !>".
    iIntros (Ψ) "(Hc & Hc1 & Hc2 & HIy1) HΨ".
    iLöb as "IH" forall (c1 c2 xs1 xs2 ys y1 w1 ys1 ys2 Hxs Hys Hsort Htl Htl_le).
    wp_rec.
    rewrite (tail_protocol_unfold xs) (tail_protocol_unfold xs2).
    wp_apply (branch_spec with "[$Hc2]"); iIntros ([]) "[Hc2 Hys2]".
    - iClear "Hys2".
      wp_apply (recv_proto_spec with "Hc2"); iIntros (x v) "/= Hc2".
      iDestruct 1 as (Htl2) "HIx".
      wp_pures. wp_apply ("Hcmp" with "[$HIy1 $HIx]"); iIntros "[HIy1 HIx]".
      case_bool_decide.
      + wp_apply (select_spec with "[$Hc]")=> //=; iIntros "Hc".
        wp_apply (send_proto_spec with "Hc"); simpl.
        iExists y1, w1. iFrame "HIy1". do 2 (iSplit; [done|]); iIntros "!> Hc".
        wp_apply ("IH" with "[%] [%] [%] [%] [%] Hc Hc2 Hc1 HIx").
        { by rewrite comm. }
        { by rewrite assoc (comm _ ys2) Hys. }
        { rewrite fmap_app. by apply Sorted_snoc. }
        { rewrite fmap_app. by constructor. }
        { intros x'. rewrite !fmap_app.
          inversion 1; discriminate_list || simplify_list_eq. by constructor. }
        iIntros "(?&?&?)". iApply "HΨ"; iFrame.
      + wp_apply (select_spec with "[$Hc]")=> //=; iIntros "Hc".
        wp_apply (send_proto_spec with "Hc"); simpl.
        iExists x, v. iFrame "HIx". iSplit; [done|]; iSplit.
        { iPureIntro. by apply Htl_le, total_not. }
        iIntros "!> Hc".
        wp_apply ("IH" with "[% //] [%] [%] [%] [%] Hc Hc1 Hc2 HIy1 HΨ").
        { by rewrite Hys assoc. }
        { rewrite fmap_app. by apply Sorted_snoc, Htl_le, total_not. }
        { rewrite fmap_app. constructor. by apply total_not. }
        { intros x'. rewrite !fmap_app.
          inversion 1; discriminate_list || simplify_list_eq. by constructor. }
    - iDestruct "Hys2" as %Hys2.
      wp_apply (select_spec with "[$Hc]")=> //=; iIntros "Hc".
      wp_apply (send_proto_spec with "Hc"); simpl.
      iExists y1, w1. iFrame "HIy1". do 2 (iSplit; [done|]); iIntros "!> Hc".
      wp_apply (list_sort_elem_service_move_spec with "[$Hc $Hc1]").
      { done. }
      { by rewrite Hys Hys2 -!assoc_L (comm _ xs2). }
      { rewrite fmap_app. by apply Sorted_snoc. }
      { intros x'. rewrite !fmap_app.
        inversion 1; discriminate_list || simplify_list_eq. by constructor. }
      iIntros "[Hc Hc1]". iApply "HΨ". iFrame.
  Qed.

  Lemma list_sort_elem_service_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ iProto_dual list_sort_elem_protocol @ N }}}
      list_sort_elem_service cmp c
    {{{ RET #(); c ↣ END @ N }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec; wp_pures. rewrite /list_sort_elem_protocol {2}head_protocol_unfold.
    wp_apply (branch_spec with "Hc"); iIntros ([]) "[Hc _]"; wp_pures.
    - wp_apply (recv_proto_spec with "Hc"); iIntros (x1 v1) "/= Hc HIx1".
      rewrite (head_protocol_unfold [_]).
      wp_apply (branch_spec with "Hc"); iIntros ([]) "[Hc _]"; wp_pures.
      + wp_apply (recv_proto_spec with "Hc"); iIntros (x2 v2) "/= Hc HIx2".
        wp_apply (start_chan_proto_spec N list_sort_elem_protocol).
        { iIntros (cy) "Hcy". wp_apply ("IH" with "Hcy"); auto. }
        iIntros (cy) "Hcy".
        wp_apply (start_chan_proto_spec N list_sort_elem_protocol).
        { iIntros (cz) "Hcz". wp_apply ("IH" with "Hcz"); auto. }
        iIntros (cz) "Hcz".
        rewrite /list_sort_elem_protocol {2 3}(head_protocol_unfold []).
        wp_apply (select_spec with "[$Hcy]")=> //; iIntros "Hcy".
        wp_apply (send_proto_spec with "Hcy")=> //=.
        iExists x1, v1. iFrame "HIx1". iSplit; [done|]; iIntros "!> Hcy".
        wp_apply (select_spec with "[$Hcz]")=> //; iIntros "Hcz".
        wp_apply (send_proto_spec with "Hcz")=> //=.
        iExists x2, v2. iFrame "HIx2". iSplit; [done|]; iIntros "!> Hcz".
        wp_apply (list_sort_elem_service_split_spec with "[$Hc $Hcy $Hcz]").
        iIntros (xs' xs1' xs2'); iDestruct 1 as (Hxs') "(Hc & Hcy & Hcz) /=".
        rewrite (tail_protocol_unfold (_ :: xs1')).
        wp_apply (branch_spec with "Hcy"); iIntros (b) "[Hcy Hnil]".
        destruct b; last first.
        { by iDestruct "Hnil" as %?%Permutation_nil_cons. }
        iClear "Hnil".
        wp_apply (recv_proto_spec with "Hcy"); iIntros (x v) "/= Hcy [_ HIx]".
        wp_apply (list_sort_elem_service_merge_spec _ _ _ _ _ [] _ _ _ _ [] []
          with "Hcmp [$Hc $Hcy $Hcz $HIx]"); simpl; auto using TlRel_nil, Sorted_nil.
        { by rewrite Hxs' Permutation_middle. }
        iIntros "(Hc & Hcy & Hcz)". by iApply "HΨ".
      + rewrite (tail_protocol_unfold [_]).
        wp_apply (select_spec with "[$Hc]")=> //=; iIntros "Hc".
        wp_apply (send_proto_spec with "Hc"); simpl.
        iExists x1, v1. iFrame "HIx1". do 2 (iSplit; [by auto using TlRel_nil|]).
        iIntros "!> Hc".
        rewrite (tail_protocol_unfold [_]).
        by wp_apply (select_spec with "[$Hc]").
    - rewrite (tail_protocol_unfold []).
      by wp_apply (select_spec with "[$Hc]").
  Qed.
End list_sort_elem.
