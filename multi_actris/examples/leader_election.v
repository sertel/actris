From multi_actris.channel Require Import proofmode.
From iris.heap_lang.lib Require Import assert.

(** Inspired by https://en.wikipedia.org/wiki/Chang_and_Roberts_algorithm *)

Definition process : val :=
  rec: "go" "c" "idl" "id" "idr" "isp" :=
    if: recv "c" "idr"
    then let: "id'" := recv "c" "idr" in
         if: "id" < "id'"          (** Case 1 *)
         then send "c" "idl" #true;; send "c" "idl" "id'";;
              "go" "c" "idl" "id" "idr" #true
         else if: "id" = "id'"     (** Case 4 *)
         then send "c" "idl" #false;; send "c" "idl" "id";;
              "go" "c" "idl" "id" "idr" #false
         else if: "isp" (** Case 3 *)
         then "go" "c" "idl" "id" "idr" "isp" (** Case 2 *)
         else send "c" "idl" #true;; send "c" "idl" "id";;
              "go" "c" "idl" "id" "idr" #true
    else let: "id'" := recv "c" "idr" in
         if: "id" = "id'" then "id'"
         else send "c" "idl" #false;; send "c" "idl" "id'";; "id'".

Definition init : val :=
  λ: "c" "idl" "id" "idr",
    (* Notice missing leader *)
    send "c" "idl" #true;; send "c" "idl" "id";;
    process "c" "idl" "id" "idr" #true.

Definition program : val :=
  λ: <>,
     let: "cs" := new_chan #4 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     let: "c3" := get_chan "cs" #3 in
     Fork (let: "id_max" := init "c1" #3 #1 #2 in send "c1" #0 "id_max");;
     Fork (let: "id_max" := process "c2" #1 #2 #3 #false in
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
             (rec : bool -d> iProto Σ) : bool -d> iProto Σ :=
    λ (isp:bool),
      iProto_choice (Recv,ir)
        (<(Recv,ir) @ (i':nat)> MSG #i' ;
         if bool_decide (i < i')
         then <(Send,il)> MSG #true ; <(Send,il)> MSG #i' ; rec true
         else if bool_decide (i = i')
         then <(Send,il)> MSG #false ; <(Send, il)> MSG #i ; rec false
         else if isp then rec isp
         else <(Send,il)> MSG #true ; <(Send,il)> MSG #i ; rec true)%proto
        (<(Recv,ir) @ (i':nat)> MSG #i' ;
         if (bool_decide (i = i')) then p i
         else <(Send,il)> MSG #false; <(Send,il)> MSG #i'; p i')%proto.

  Instance rle_prot_aux_contractive il i ir p : Contractive (my_recv_prot il i ir p).
  Proof. rewrite /my_recv_prot. solve_proto_contractive. Qed.
  Definition rle_prot il i ir p := fixpoint (my_recv_prot il i ir p).
  Instance rle_prot_unfold il i ir isp p :
    ProtoUnfold (rle_prot il i ir p isp) (my_recv_prot il i ir p (rle_prot il i ir p) isp).
  Proof. apply proto_unfold_eq, (fixpoint_unfold (my_recv_prot il i ir p)). Qed.
  Lemma rle_prot_unfold' il i ir isp p :
    (rle_prot il i ir p isp) ≡
    (my_recv_prot il i ir p (rle_prot il i ir p) isp).
  Proof. apply (fixpoint_unfold (my_recv_prot il i ir p)). Qed.

  Definition rle_preprot (il i ir : nat) p : iProto Σ :=
    (<(Send, il)> MSG #true; <(Send, il)> MSG #i ;
    rle_prot il i ir p true)%proto.

  Lemma process_spec il i ir p c (isp:bool) :
    {{{ c ↣ (rle_prot il i ir p isp) }}}
      process c #il #i #ir #isp
    {{{ i', RET #i'; c ↣ p i' }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    iLöb as "IH" forall (Φ isp).
    wp_lam. wp_recv (b) as "_".
    destruct b.
    - wp_pures. wp_recv (i') as "_".
      wp_pures.
      case_bool_decide as Hlt.
      { case_bool_decide; [|lia].
        wp_pures. wp_send with "[//]".
        wp_send with "[//]". wp_pures.
        iApply ("IH" with "Hc HΦ"). }
      case_bool_decide as Hlt2.
      { case_bool_decide; [lia|].
        wp_pures. case_bool_decide; [|simplify_eq;lia].
        wp_send with "[//]".
        wp_send with "[//]". wp_pures.
        iApply ("IH" with "Hc HΦ"). }
      case_bool_decide; [lia|].
      wp_pures.
      case_bool_decide; [simplify_eq;lia|].
      wp_pures.
      destruct isp.
      { wp_pures. iApply ("IH" with "Hc HΦ"). }
      wp_pures.
      wp_send with "[//]".
      wp_send with "[//]".
      wp_pures. iApply ("IH" with "Hc HΦ").
    - wp_pures.
      wp_recv (id') as "_". wp_pures.
      case_bool_decide as Hlt.
      { case_bool_decide; [|simplify_eq;lia].
        wp_pures. subst. by iApply "HΦ". }
      case_bool_decide; [simplify_eq;lia|].
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

  Definition pre_prot_pool id_max : list (iProto Σ) :=
     [(<(Recv,1) @ (id_max : nat)> MSG #id_max ;
             <(Recv,2)> MSG #id_max ;
             <(Recv,3)> MSG #id_max ;
             END)%proto;
      prot_tail id_max;
      prot_tail id_max;
      prot_tail id_max].

  Lemma pre_prot_pool_consistent id_max :
    ⊢ iProto_consistent (pre_prot_pool id_max).
  Proof. rewrite /pre_prot_pool. iProto_consistent_take_steps. Qed.

  Definition prot_pool : list (iProto Σ) :=
     [(<(Recv,1) @ (id_max : nat)> MSG #id_max ;
             <(Recv,2)> MSG #id_max ;
             <(Recv,3)> MSG #id_max ;
             END)%proto;
      rle_preprot 3 1 2 prot_tail;
      rle_prot 1 2 3 prot_tail false;
      rle_preprot 2 3 1 prot_tail].

  Lemma prot_pool_consistent : ⊢ iProto_consistent prot_pool.
  Proof.
    rewrite /prot_pool /rle_preprot.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_steps.
    case_bool_decide; try lia.
    case_bool_decide; try lia.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_steps.
    case_bool_decide; try lia.
    case_bool_decide; try lia.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_steps.
  Qed.

  Lemma program_spec :
    {{{ True }}} program #() {{{ RET #(); True }}}.
  Proof. 
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_chan_spec prot_pool);
      [set_solver|iApply prot_pool_consistent|].
    iIntros (cs) "Hcs".
    wp_get_chan (c0) "[Hc0 Hcs]".
    wp_get_chan (c1) "[Hc1 Hcs]".
    wp_get_chan (c2) "[Hc2 Hcs]".
    wp_get_chan (c3) "[Hc3 Hcs]".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>". wp_smart_apply (init_spec with "Hc1").
      iIntros (i') "Hc1". by wp_send with "[//]". }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>". wp_smart_apply (process_spec with "Hc2").
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
