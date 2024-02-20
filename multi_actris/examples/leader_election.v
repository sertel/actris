From multi_actris.channel Require Import proofmode.
From iris.heap_lang.lib Require Import assert.

(** Inspired by https://en.wikipedia.org/wiki/Chang_and_Roberts_algorithm *)

Definition process : val :=
  rec: "go" "c" "idl" "id" "idr" "isp" "id_max" :=
    if: recv "c" "idr"
    then let: "id'" := recv "c" "idr" in
         if: "id_max" < "id'"          (** Case 1 *)
         then send "c" "idl" #true;; send "c" "idl" "id'";;
              "go" "c" "idl" "id" "idr" "isp" "id'"
         else if: "id_max" = "id'"     (** Case 4 *)
         then send "c" "idl" #false;; send "c" "idl" "id_max";;
              "go" "c" "idl" "id" "idr" #false "id_max"
         else if: "isp" (** Case 3 *)
         then "go" "c" "idl" "id" "idr" "isp" "id_max" (** Case 2 *)
         else send "c" "idl" #true;; send "c" "idl" "id_max";;
              "go" "c" "idl" "id" "idr" #true "id_max"
    else let: "id'" := recv "c" "idr" in
         assert: ("id_max" = "id'");;
         if: "id" = "id'" then "id'"
         else send "c" "idl" #false;; send "c" "idl" "id_max";; "id_max".

Definition init : val :=
  λ: "c" "idl" "id" "idr",
    (* Notice missing leader *)
    send "c" "idl" #true;; send "c" "idl" "id";;
    process "c" "idl" "id" "idr" #true "id".

Definition program : val :=
  λ: <>,
     let: "cs" := new_chan #4 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     let: "c3" := get_chan "cs" #3 in
     Fork (let: "id_max" := init "c1" #3 #1 #2 in send "c1" #0 "id_max");;
     Fork (let: "id_max" := process "c2" #1 #2 #3 #false #2 in
           send "c2" #0 "id_max");;
     Fork (let: "id_max" := init "c3" #2 #3 #1 in send "c3" #0 "id_max");;
     let: "res1" := recv "c0" #1 in
     let: "res2" := recv "c0" #2 in
     let: "res3" := recv "c0" #3 in
     assert: ("res1" = "res2");;
     assert: ("res2" = "res3").

Notation iProto_choice a p1 p2 :=
  (<a @ (b : bool)> MSG #b; if b then p1 else p2)%proto.

Section ring_leader_election_example.
  Context `{!heapGS Σ, chanG Σ, spawnG Σ, mono_natG Σ}.

  Definition my_recv_prot (il i ir : nat) (p : nat → iProto Σ)
             (rec : bool -d> nat -d> iProto Σ) : bool -d> nat -d> iProto Σ :=
    λ (isp:bool) (i_max:nat),
      iProto_choice (Recv,ir)
        (<(Recv,ir) @ (i':nat)> MSG #i' ;
         if bool_decide (i_max < i')
         then <(Send,il)> MSG #true ; <(Send,il)> MSG #(max i' i_max) ;
              rec isp (max i' i_max)
         else if bool_decide (i_max = i')
         then <(Send,il)> MSG #false ; <(Send, il)> MSG #i_max ; rec false i_max
         else if isp then rec isp i_max
         else <(Send,il)> MSG #true ; <(Send,il)> MSG #(max i' i_max) ;
              rec true (max i' i_max))%proto
        (<(Recv,ir)> MSG #i_max ;
         if (bool_decide (i = i_max)) then p i_max
         else <(Send,il)> MSG #false; <(Send,il)> MSG #i_max; p i_max)%proto.

  Instance rle_prot_aux_contractive il i ir p : Contractive (my_recv_prot il i ir p).
  Proof. rewrite /my_recv_prot. solve_proto_contractive. Qed.
  Definition rle_prot il i ir p := fixpoint (my_recv_prot il i ir p).
  Instance rle_prot_unfold il i ir isp max_id p :
    ProtoUnfold (rle_prot il i ir p isp max_id) (my_recv_prot il i ir p (rle_prot il i ir p) isp max_id).
  Proof. apply proto_unfold_eq, (fixpoint_unfold (my_recv_prot il i ir p)). Qed.
  Lemma rle_prot_unfold' il i ir isp max_id p :
    (rle_prot il i ir p isp max_id) ≡
    (my_recv_prot il i ir p (rle_prot il i ir p) isp max_id).
  Proof. apply (fixpoint_unfold (my_recv_prot il i ir p)). Qed.

  Definition rle_preprot (il i ir : nat) p : iProto Σ :=
    (<(Send, il)> MSG #true; <(Send, il)> MSG #i ;
    rle_prot il i ir p true i)%proto.

  Lemma process_spec il i ir p i_max c (isp:bool) :
    i <= i_max →
    {{{ c ↣ (rle_prot il i ir p isp i_max) }}}
      process c #il #i #ir #isp #i_max
    {{{ i', RET #i'; c ↣ p i' }}}.
  Proof.
    iIntros (Hle Φ) "Hc HΦ".
    iLöb as "IH" forall (Φ isp i_max Hle).    
    wp_lam. wp_recv (b) as "_".
    destruct b.
    - wp_pures. wp_recv (i') as "_".
      wp_pures.
      case_bool_decide as Hlt.
      { case_bool_decide; [|lia].
        wp_pures. wp_send with "[//]".
        iEval (replace i' with (max i' i_max) by lia).
        wp_send with "[//]". wp_pures.        
        iApply ("IH" with "[] Hc HΦ"). iPureIntro. lia. }
      case_bool_decide as Hlt2.
      { case_bool_decide; [lia|].
        wp_pures. case_bool_decide; [|simplify_eq;lia].
        wp_send with "[//]".
        iEval (replace i' with (max i' i_max) by lia).
        wp_send with "[//]". wp_pures.
        iApply ("IH" with "[] Hc HΦ"). iPureIntro. lia. }
      case_bool_decide; [lia|].
      wp_pures.
      case_bool_decide; [simplify_eq;lia|].
      wp_pures. 
      destruct isp.
      { wp_pures. iApply ("IH" with "[] Hc HΦ"). iPureIntro. lia. }
      wp_pures.
      wp_send with "[//]".
      iEval (replace i_max with (max i' i_max) by lia).
      wp_send with "[//]".
      wp_pures. iApply ("IH" with "[] Hc HΦ"). iPureIntro. lia.
    - wp_pures.
      wp_recv as "_".
      wp_smart_apply wp_assert.
      wp_pures. iModIntro.
      iSplitR.
      { iPureIntro. f_equiv. f_equiv. apply bool_decide_eq_true_2. done. }
      iNext.
      wp_pures.
      case_bool_decide.
      { wp_pures. simplify_eq.
        case_bool_decide; [|simplify_eq;lia]. wp_pures.
        iModIntro. by iApply "HΦ". }
      wp_pures. case_bool_decide; [simplify_eq;lia|]. wp_pures.
      wp_send with "[//]". wp_send with "[//]". wp_pures. by iApply "HΦ".
  Qed.

  Lemma init_spec c il i ir p :
    {{{ c ↣ rle_preprot il i ir p }}}
      init c #il #i #ir
    {{{ res, RET #res; c ↣ p res }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". wp_lam. wp_send with "[//]". wp_send with "[//]".
    wp_pures. by iApply (process_spec with "Hc HΦ").
  Qed.

  Definition prot_tail (i_max : nat) : iProto Σ :=
    (<(Send,0)> MSG #i_max; END)%proto.

  Definition pre_prot_pool id_max : gmap nat (iProto Σ) :=
     <[0 := (<(Recv,1) @ (id_max : nat)> MSG #id_max ;
             <(Recv,2)> MSG #id_max ;
             <(Recv,3)> MSG #id_max ;
             END)%proto ]>
    (<[1 := prot_tail id_max ]>
    (<[2 := prot_tail id_max ]>
    (<[3 := prot_tail id_max ]> ∅))).

  Lemma pre_prot_pool_consistent id_max :
    ⊢ iProto_consistent (pre_prot_pool id_max).
  Proof. rewrite /pre_prot_pool. iProto_consistent_take_steps. Qed.

  Definition prot_pool : gmap nat (iProto Σ) :=
     <[0 := (<(Recv,1) @ (id_max : nat)> MSG #id_max ;
             <(Recv,2)> MSG #id_max ;
             <(Recv,3)> MSG #id_max ;
             END)%proto ]>
    (<[1 := rle_preprot 3 1 2 prot_tail ]>
    (<[2 := rle_prot 1 2 3 prot_tail false 2 ]>
    (<[3 := rle_preprot 2 3 1 prot_tail ]> ∅))).

  Lemma prot_pool_consistent : ⊢ iProto_consistent prot_pool.
  Proof.
    rewrite /prot_pool /rle_preprot.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    repeat clean_map 0. repeat clean_map 1.
    repeat clean_map 2. repeat clean_map 3.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    repeat clean_map 0. repeat clean_map 1.
    repeat clean_map 2. repeat clean_map 3.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    repeat clean_map 0. repeat clean_map 1.
    repeat clean_map 2. repeat clean_map 3.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    repeat clean_map 0. repeat clean_map 1.
    repeat clean_map 2. repeat clean_map 3.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    repeat clean_map 0. repeat clean_map 1.
    repeat clean_map 2. repeat clean_map 3.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    repeat clean_map 0. repeat clean_map 1.
    repeat clean_map 2. repeat clean_map 3.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    iProto_consistent_take_step.
    iProto_consistent_resolve_step.
    repeat clean_map 0. repeat clean_map 1.
    repeat clean_map 2. repeat clean_map 3.
    repeat (rewrite (insert_commute _ _ 3); [|lia]).
    repeat (rewrite (insert_commute _ _ 2); [|lia]).
    repeat (rewrite (insert_commute _ _ 1); [|lia]).
    repeat (rewrite (insert_commute _ _ 0); [|lia]).
    iApply pre_prot_pool_consistent.
  Qed.

  Lemma program_spec :
    {{{ True }}} program #() {{{ RET #(); True }}}.
  Proof. 
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_chan_spec 4 prot_pool);
      [lia|set_solver|iApply prot_pool_consistent|].
    iIntros (cs) "Hcs".
    wp_smart_apply (get_chan_spec _ 0 with "Hcs"); [done|].
    iIntros (c0) "[Hc0 Hcs]".
    wp_smart_apply (get_chan_spec _ 1 with "Hcs"); [done|].
    iIntros (c1) "[Hc1 Hcs]".
    wp_smart_apply (get_chan_spec _ 2 with "Hcs"); [done|].
    iIntros (c2) "[Hc2 Hcs]".
    wp_smart_apply (get_chan_spec _ 3 with "Hcs"); [done|].
    iIntros (c3) "[Hc3 Hcs]".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>". wp_smart_apply (init_spec with "Hc1").
      iIntros (i') "Hc1". by wp_send with "[//]". }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>". wp_smart_apply (process_spec with "Hc2"); [lia|].
      iIntros (i') "Hc2". by wp_send with "[//]". }
    wp_smart_apply (wp_fork with "[Hc3]").
    { iIntros "!>". wp_smart_apply (init_spec with "Hc3").
      iIntros (i') "Hc3". by wp_send with "[//]". }
    wp_recv (id_max) as "_". wp_recv as "_". wp_recv as "_".
    wp_smart_apply wp_assert. wp_pures. iModIntro. iSplitR; [iPureIntro|].
    { do 2 f_equiv. by apply bool_decide_eq_true_2. }
    iIntros "!>".
    wp_smart_apply wp_assert. wp_pures. iModIntro. iSplitR; [iPureIntro|].
    { do 2 f_equiv. by apply bool_decide_eq_true_2. }
    iIntros "!>". by iApply "HΦ".
  Qed.

End ring_leader_election_example.
