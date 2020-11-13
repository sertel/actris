From actris.channel Require Import proofmode.
From iris.heap_lang Require Import proofmode.
From actris.utils Require Import contribution.
From iris.base_logic.lib Require Import mnat.
From iris.heap_lang.lib Require Import par assert.

Definition cont := true.
Definition elected := false.

Definition abort := #() #().

(** Inspired by https://en.wikipedia.org/wiki/Chang_and_Roberts_algorithm *)

Definition process : val :=
  rec: "go" "id" "cl" "cr" :=
    if: (recv "cr") then
      let: "id'" := recv "cr" in
      if: "id" < "id'"          (** Case 1 *)
      then send "cl" #cont;; send "cl" "id'";;
           "go" "id" "cl" "cr"
      else if: "id" = "id'"     (** Case 4 *)
      then send "cl" #elected;; send "cl" "id";;
           "id" (* Do termination of leader here *)
      else send "cl" #cont;; send "cl" "id";;
           "go" "id" "cl" "cr"
    else
      let: "res" := recv "cr" in
      (* if: "id" < "res": do else ABORT *)
      send "cl" #elected;; send "cl" "res";;
      "res". (* Do termination of non-leader here *)

Definition program : val :=
  λ: <>,
     let: "c1" := new_chan #() in
     let: "c2" := new_chan #() in
     let: "c3" := new_chan #() in
     send (Fst "c1") #cont;; send (Fst "c1") #1;;
     let: "res" := ( process #1 (Fst "c1") (Snd "c3")  |||
       ( process #2 (Fst "c2") (Snd "c1") ||| process #3 (Fst "c3") (Snd "c2")) ) in
     let: "res1" := Fst "res" in
     let: "res2" := Fst (Snd "res") in
     let: "res3" := Snd (Snd "res") in
     assert: ("res1" = "res2");; assert: ("res2" = "res3");;
     "res1".

Section ring_leader_election_example.
  Context `{!heapG Σ, chanG Σ, spawnG Σ, mnatG Σ}.

  Definition rle_prot_aux (γ : gname) (ids : gset nat) (rec : nat -d> iProto Σ)
    : nat -d> iProto Σ :=
    λ (max_id : nat),
      ((<! (id:nat)> MSG #id {{ ⌜id ∈ ids⌝ ∗ mnat_own_auth γ 1 id }} ; rec id)
         <+>
       (<! (q:Qp)> MSG #max_id {{ ⌜max_id ∈ ids⌝ ∗ mnat_own_auth γ q max_id }} ; END))%proto.
  Instance rle_prot_aux_contractive γ ids : Contractive (rle_prot_aux γ ids).
  Proof. solve_proto_contractive. Qed.
  Definition rle_prot γ ids := fixpoint (rle_prot_aux γ ids).
  Instance rle_prot_unfold γ ids max_id :
    ProtoUnfold (rle_prot γ ids max_id) (rle_prot_aux γ ids (rle_prot γ ids) max_id).
  Proof. apply proto_unfold_eq, (fixpoint_unfold (rle_prot_aux γ ids)). Qed.

  Definition rle_preprot (γ : gname) (ids : gset nat) : iProto Σ :=
    (<!> MSG #true; <! (id:nat)> MSG #id
                      {{ ⌜id ∈ ids⌝ ∗ mnat_own_auth γ 1 id }};
    rle_prot γ ids id)%proto.

  Lemma process_spec γ ids id max_in max_out cl cr :
    id ∈ ids →
    {{{ ⌜max max_in id <= max_out⌝ ∗ mnat_own_lb γ max_out ∗
        cl ↣ (rle_prot γ ids max_out) ∗ cr ↣ iProto_dual (rle_prot γ ids max_in) }}}
      process #id cl cr
    {{{ res q, RET #res; ⌜id <= res⌝ ∗ ⌜res ∈ ids⌝ ∗ mnat_own_auth γ q res }}}.
  Proof.
    iIntros (Hin Φ) "(Hle & Hown & Hcl & Hcr) HΦ".
    iDestruct "Hle" as %Hle.
    iLöb as "IH" forall (max_in max_out Hle).
    wp_rec.
    wp_branch.
    - wp_recv (id') as (Hin') "Hauth".
      iDestruct (mnat_own_lb_valid with "Hauth Hown") as %[_ Hle'].
      wp_pures. case_bool_decide as Hdec;
                  wp_pures; [ | case_bool_decide as Hdec' ]; wp_pures.
      + wp_select=> /=.
        iMod (mnat_update_with_lb _ _ id' with "Hauth") as "[Hauth Hown']"=> //.
        wp_send with "[$Hauth//]".
        wp_pures.
        iApply ("IH" $!id' id' with "[] Hown' Hcl Hcr")=> //.
        iPureIntro. lia.
      + wp_select. simpl.
        assert (id = id') as Heq.
        { inversion Hdec'. lia. }
        rewrite -Heq.
        assert (max_out = id) as -> by lia.
        iDestruct "Hauth" as "[Hauth1 Hauth2]".
        wp_send with "[$Hauth1//]".
        wp_pures. iApply "HΦ". eauto.
      + assert (id ≠ id').
        { intros Heq. apply Hdec'. by rewrite Heq. }
        lia.                    (* Contradiction *)
    - wp_recv (q) as (Hin') "Hauth".
      wp_select=> /=.
      iDestruct (mnat_own_lb_valid with "Hauth Hown") as %[_ Hle'].
      assert (id < max_in) as Hle'' by admit. (* max_in always largest here *)
      assert (max_in = max_out) as -> by lia.
      iDestruct "Hauth" as "[Hauth1 Hauth2]".
      wp_send with "[$Hauth1//]".
      wp_pures. iApply "HΦ". eauto with lia.
  Admitted.

  Lemma preprocess_spec γ ids (id:nat) cl cr :
    id ∈ ids →
    {{{ cl ↣ rle_preprot γ ids ∗ cr ↣ iProto_dual (rle_preprot γ ids) }}}
      process #id cl cr
    {{{ res q, RET #res; ⌜id <= res⌝ ∗ ⌜res ∈ ids⌝ ∗ mnat_own_auth γ q res }}}.
  Proof.
    iIntros (Hin Φ) "(Hcl & Hcr) HΦ".
    wp_rec.
    wp_recv as "_".
    wp_recv (id') as (Hin') "Hauth".
    wp_pures.
    case_bool_decide as Hdec; wp_pures; [ | case_bool_decide as Hdec' ]; wp_pures.
    + wp_send with "[//]".
      iMod (mnat_update_with_lb _ _ id' with "Hauth") as "[Hauth Hown]"=> //.
      wp_send with "[$Hauth//]".
      wp_apply (process_spec with "[$Hown $Hcl $Hcr]");
        [ done | iPureIntro; lia |].
      by iApply "HΦ".
    + admit.                    (* Not possible in first iteration *)
    + wp_send with "[//]".
      iMod (mnat_update_with_lb _ _ id with "Hauth") as "[Hauth Hown]"=> //.
      { lia. }
      wp_send (id) with "[$Hauth//]".
      wp_apply (process_spec with "[$Hown $Hcl $Hcr]");
        [ done | iPureIntro; lia |].
      by iApply "HΦ".
  Admitted.

  Lemma process_start_spec γ ids (id:nat) cl cr :
    id ∈ ids →
    {{{ mnat_own_lb γ id ∗
        cl ↣ rle_prot γ ids id ∗ cr ↣ iProto_dual (rle_preprot γ ids) }}}
      process #id cl cr
    {{{ res q, RET #res; ⌜id <= res⌝ ∗ ⌜res ∈ ids⌝ ∗ mnat_own_auth γ q res }}}.
  Proof.
    iIntros (Hin Φ) "(Hown & Hcl & Hcr) HΦ".
    wp_rec.
    wp_recv as "_".
    wp_recv (id') as (Hin') "Hauth".
    wp_pures.
    case_bool_decide as Hdec; wp_pures; [ | case_bool_decide as Hdec' ]; wp_pures.
    + wp_select.
      iMod (mnat_update_with_lb _ _ id' with "Hauth") as "[Hauth Hown']"=> //.
      wp_send with "[$Hauth//]".
      wp_apply (process_spec with "[$Hown' $Hcl $Hcr]");
        [ done | iPureIntro; lia |].
      by iApply "HΦ".
    + wp_select. simpl.
      assert (id = id') as Heq.
      { inversion Hdec'. lia. }
      rewrite -Heq.
      iDestruct "Hauth" as "[Hauth1 Hauth2]".
      wp_send with "[$Hauth1//]".
      wp_pures. iApply "HΦ". eauto.
    + wp_select.
      iMod (mnat_update_with_lb _ _ id with "Hauth") as "[Hauth Hown']"=> //.
      { lia. }
      wp_send (id) with "[$Hauth//]".
      wp_apply (process_spec with "[$Hown' $Hcl $Hcr]");
        [ done | iPureIntro; lia |].
      by iApply "HΦ".
  Qed.

  Lemma program_spec :
    {{{ True }}} program #() {{{ RET #3; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    iMod (mnat_alloc 1) as (γ) "[Hauth Hown]".
    set (ids:={[1 ; 2 ; 3]}:gset nat).
    wp_apply (new_chan_spec (rle_preprot γ ids))=> //.
    iIntros (c1l c1r) "[Hc1l Hc1r]".
    wp_apply (new_chan_spec (rle_preprot γ ids))=> //.
    iIntros (c2l c2r) "[Hc2l Hc2r]".
    wp_apply (new_chan_spec (rle_preprot γ ids))=> //.
    iIntros (c3l c3r) "[Hc3l Hc3r]".
    wp_send with "[//]".
    wp_send (1) with "[$Hauth//]".
    wp_pures.
    wp_apply (par_spec
      (λ v, ∃ (res1:nat) q1, ⌜v = #res1⌝ ∗ ⌜1 ≤ res1⌝ ∗ ⌜res1 ∈ ids⌝ ∗
                             mnat_own_auth γ q1 res1)%I
      (λ v, ∃ (res2 res3:nat) q2 q3, ⌜v = PairV #res2 #res3⌝ ∗
                                     ⌜2 ≤ res2⌝ ∗ ⌜res2 ∈ ids⌝ ∗
                                     ⌜3 ≤ res3⌝ ∗ ⌜res3 ∈ ids⌝ ∗
                                     mnat_own_auth γ q2 res2 ∗
                                     mnat_own_auth γ q3 res3 )%I
                with "[Hown Hc1l Hc3r] [-HΦ]").
    { wp_apply (process_start_spec γ ids 1 with "[$Hown $Hc1l $Hc3r]");
        [ set_solver | eauto ]. }
    { wp_apply (par_spec
        (λ v, ∃ (res2:nat) q2, ⌜v = #res2⌝ ∗ ⌜2 ≤ res2⌝ ∗ ⌜res2 ∈ ids⌝ ∗
                               mnat_own_auth γ q2 res2)%I
        (λ v, ∃ (res3:nat) q3, ⌜v = #res3⌝ ∗ ⌜3 ≤ res3⌝ ∗ ⌜res3 ∈ ids⌝ ∗
                               mnat_own_auth γ q3 res3)%I
                  with "[Hc2l Hc1r] [Hc3l Hc2r]").
      { wp_apply (preprocess_spec γ ids 2 with "[$Hc2l $Hc1r]");
          [ set_solver | eauto ]. }
      { wp_apply (preprocess_spec γ ids 3 with "[$Hc3l $Hc2r]");
          [ set_solver | eauto]. }
      iIntros (v1 v2) "[H1 H2]".
      iDestruct "H1" as (res2 q2 -> Hle2 Hin2) "Hauth1".
      iDestruct "H2" as (res3 q3 -> Hle3 Hin3) "Hauth2".
      iIntros "!>". iExists res2, res3, q2, q3. eauto with iFrame. }
    iIntros (v1 v2) "[H1 H2]".
    iDestruct "H1" as (res1 q1 -> Hle1 Hin1) "Hauth1".
    iDestruct "H2" as (res2 res3 q2 q3 -> Hle2 Hin2 Hle3 Hin3) "[Hauth2 Hauth3]".
    iDestruct (mnat_own_auth_agree with "Hauth1 Hauth2") as %[_ <-].
    iDestruct (mnat_own_auth_agree with "Hauth2 Hauth3") as %[_ <-].
    iIntros "!>". wp_pures.
    wp_apply wp_assert. wp_pures. iSplitR; [ by case_bool_decide | ].
    iIntros "!>".
    wp_apply wp_assert. wp_pures. iSplitR; [ by case_bool_decide | ].
    iIntros "!>". wp_pures.
    assert (res1 = 3) as ->.
    { set_solver by auto with lia. }
    by iApply "HΦ".
  Qed.

End ring_leader_election_example.
