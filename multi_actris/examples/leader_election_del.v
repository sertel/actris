From iris.heap_lang Require Import adequacy.
From iris.heap_lang.lib Require Import assert.
From multi_actris.channel Require Import proofmode.

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

Definition forward : val :=
  λ: "c" "idl" "id" "idr" "id_max",
    if: "id" = "id_max" then
      let: "cs'" := new_chan #2 in
      let: "c0" := get_chan "cs'" #0 in
      let: "c1" := get_chan "cs'" #1 in
      send "c1" #0 "id_max";;
      send "c" "idl" "c1";;
      Fork ((rec: "f" <> :=
              let: "id'" := recv "c0" #1 in
              assert: ("id'" = "id_max");; "f" #()) #());;
      recv "c" "idr";; #()
    else
      let: "c1" := recv "c" "idr" in
      send "c1" #0 "id_max";;
      send "c" "idl" "c1".

Definition program : val :=
  λ: <>,
     let: "cs" := new_chan #4 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     let: "c3" := get_chan "cs" #3 in
     Fork (let: "id_max" := process "c1" #0 #1 #2 #false in 
           forward "c1" #0 #1 #2 "id_max");;
     Fork (let: "id_max" := process "c2" #1 #2 #3 #false in 
           forward "c2" #1 #2 #3 "id_max");;
     Fork (let: "id_max" := process "c3" #2 #3 #0 #false in 
           forward "c3" #2 #3 #0 "id_max");;
     let: "id_max" := init "c0" #3 #0 #1 in
     forward "c0" #3 #0 #1 "id_max".

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

  Definition forward_prot (p : iProto Σ) (il i ir i_max : nat) : iProto Σ :=
    if bool_decide (i = i_max) then
      (<(Send,il) @ (c:val)> MSG c {{ c ↣ p }} ; <(Recv,ir)> MSG c {{ c ↣ p }}; END)%proto
    else
      (<(Recv,ir) @ (c:val)> MSG c {{ c ↣ p }} ; <(Send,il)> MSG c {{ c ↣ p }}; END)%proto.

  Definition relay_send_aux (id : nat) (rec : iProto Σ) : iProto Σ :=
    (<(Send,0)> MSG #id ; rec)%proto.
  Instance relay_send_aux_contractive i : Contractive (relay_send_aux i).
  Proof. solve_proto_contractive. Qed.
  Definition relay_send_prot i := fixpoint (relay_send_aux i).
  Instance relay_send_prot_unfold i :
    ProtoUnfold (relay_send_prot i) (relay_send_aux i (relay_send_prot i)).
  Proof. apply proto_unfold_eq, (fixpoint_unfold (relay_send_aux i)). Qed.
  Lemma relay_send_prot_unfold' i :
    (relay_send_prot i) ≡
    (relay_send_aux i (relay_send_prot i)).
  Proof. apply (fixpoint_unfold (relay_send_aux i)). Qed.

  Definition relay_recv_aux (id : nat) (rec : iProto Σ) : iProto Σ :=
    (<(Recv,1)> MSG #id ; rec)%proto.
  Instance relay_recv_aux_contractive i : Contractive (relay_recv_aux i).
  Proof. solve_proto_contractive. Qed.
  Definition relay_recv_prot i := fixpoint (relay_recv_aux i).
  Instance relay_recv_prot_unfold i :
    ProtoUnfold (relay_recv_prot i) (relay_recv_aux i (relay_recv_prot i)).
  Proof. apply proto_unfold_eq, (fixpoint_unfold (relay_recv_aux i)). Qed.
  Lemma relay_recv_prot_unfold' i :
    (relay_recv_prot i) ≡
    (relay_recv_aux i (relay_recv_prot i)).
  Proof. apply (fixpoint_unfold (relay_recv_aux i)). Qed.

  Definition prot_pool : list (iProto Σ) :=
     [rle_preprot 3 0 1 (λ id_max, forward_prot (relay_send_prot id_max) 3 0 1 id_max);
      rle_prot 0 1 2 (λ id_max, forward_prot (relay_send_prot id_max) 0 1 2 id_max) false;
      rle_prot 1 2 3 (λ id_max, forward_prot (relay_send_prot id_max) 1 2 3 id_max) false;
      rle_prot 2 3 0 (λ id_max, forward_prot (relay_send_prot id_max) 2 3 0 id_max) false].

  Lemma prot_pool_consistent : ⊢ iProto_consistent prot_pool.
  Proof.
    rewrite /prot_pool /rle_preprot.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_steps.
    case_bool_decide; try lia.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_steps.
    case_bool_decide; try lia.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_steps.
    case_bool_decide; try lia.
    rewrite !rle_prot_unfold'.
    iProto_consistent_take_steps.
  Qed.

  Definition prot_pool' (i:nat) : list (iProto Σ) :=
     [relay_recv_prot i;
      relay_send_prot i].

  Lemma prot_pool_consistent' i : ⊢ iProto_consistent (prot_pool' i).
  Proof.
    rewrite /prot_pool'.
    iLöb as "IH".
    iEval (rewrite relay_recv_prot_unfold').
    iEval (rewrite relay_send_prot_unfold').
    iProto_consistent_take_steps.
    done.
  Qed.

  Lemma forward_spec c il i ir i_max :
    {{{ c ↣ forward_prot (relay_send_prot i_max) il i ir i_max }}}
      forward c #il #i #ir #i_max
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". wp_lam.
    rewrite /forward_prot.
    wp_pures. case_bool_decide.
    - simplify_eq. wp_pures.
      case_bool_decide; [|simplify_eq;lia].
      wp_new_chan (prot_pool' i_max) with (prot_pool_consistent' i_max)
        as (c0 c1) "Hc0" "Hc1".
      wp_send with "[//]".
      wp_send with "[Hc1//]".
      wp_smart_apply (wp_fork with "[Hc0]").
      { iIntros "!>".
        wp_pures.
        iLöb as "IH".
        wp_recv as "_".
        wp_smart_apply wp_assert.
        wp_pures. iModIntro. iSplit; [iPureIntro; f_equiv; by case_bool_decide|].
        iIntros "!>". wp_pures. by iApply "IH". }
      wp_recv as "Hc'". wp_pures. by iApply "HΦ".
    - case_bool_decide; [simplify_eq;lia|].
      wp_pures.
      wp_recv (c') as "Hc'".
      wp_send with "[//]".
      wp_send with "[Hc'//]". 
      by iApply "HΦ".
  Qed.

  Lemma program_spec :
    {{{ True }}} program #() {{{ RET #(); True }}}.
  Proof. 
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_new_chan prot_pool with prot_pool_consistent
      as (c0 c1 c2 c3) "Hc0" "Hc1" "Hc2" "Hc3".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>". wp_smart_apply (process_spec with "Hc1").
      iIntros (i') "Hc1". by wp_smart_apply (forward_spec with "Hc1"). }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>". wp_smart_apply (process_spec with "Hc2").
      iIntros (i') "Hc2". by wp_smart_apply (forward_spec with "Hc2"). }
    wp_smart_apply (wp_fork with "[Hc3]").
    { iIntros "!>". wp_smart_apply (process_spec with "Hc3").
      iIntros (i') "Hc3". by wp_smart_apply (forward_spec with "Hc3"). }
    wp_smart_apply (init_spec with "Hc0").
    iIntros (i') "Hc0". by wp_smart_apply (forward_spec with "Hc0").
  Qed.

End ring_leader_election_example.

Lemma program_spec_adequate :
  adequate NotStuck (program #()) ({|heap := ∅; used_proph_id := ∅|})
           (λ _ _, True).
Proof.
  apply (heap_adequacy #[heapΣ; chanΣ]).
  iIntros (Σ) "H". by iApply program_spec.
Qed.
