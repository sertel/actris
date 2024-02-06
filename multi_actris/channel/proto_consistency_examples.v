From iris.algebra Require Import gmap excl_auth gmap_view.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.iprop.
From iris.base_logic Require Import lib.own.
From multi_actris.channel Require Import proofmode.
Set Default Proof Using "Type".

Lemma iProto_consistent_equiv_proof {Σ} (ps : gmap nat (iProto Σ)) :
  (∀ i j, valid_target ps i j) ∗
  (∀ i j m1 m2,
     (ps !!! i ≡ (<(Send, j)> m1)%proto) -∗
     (ps !!! j ≡ (<(Recv, i)> m2)%proto) -∗
     ∃ m1' m2' (TT1:tele) (TT2:tele) tv1 tP1 tp1 tv2 tP2 tp2,
       (<(Send, j)> m1')%proto ≡ (<(Send, j)> m1)%proto ∗
       (<(Recv, i)> m2')%proto ≡ (<(Recv, i)> m2)%proto ∗
       ⌜MsgTele (TT:=TT1) m1' tv1 tP1 tp1⌝ ∗
       ⌜MsgTele (TT:=TT2) m2' tv2 tP2 tp2⌝ ∗
   ∀.. (x : TT1), tele_app tP1 x -∗
   ∃.. (y : TT2), ⌜tele_app tv1 x = tele_app tv2 y⌝ ∗
                  tele_app tP2 y ∗
                  ▷ (iProto_consistent
                       (<[i:=tele_app tp1 x]>(<[j:=tele_app tp2 y]>ps)))) -∗
  iProto_consistent ps.
Proof.
  iIntros "[H' H]".
  rewrite iProto_consistent_unfold.
  iFrame.
  iIntros (i j m1 m2) "Hm1 Hm2".
  iDestruct ("H" with "Hm1 Hm2")
    as (m1' m2' TT1 TT2 tv1 tP1 tp1 tv2 tP2 tp2)
         "(Heq1 & Heq2& %Hm1' & %Hm2' & H)".
  rewrite !iProto_message_equivI.
  iDestruct "Heq1" as "[_ Heq1]".
  iDestruct "Heq2" as "[_ Heq2]".
  iIntros (v p1) "Hm1".
  iSpecialize ("Heq1" $! v (Next p1)).
  iRewrite -"Heq1" in "Hm1".
  rewrite Hm1'.
  rewrite iMsg_base_eq. rewrite iMsg_texist_exist.
  iDestruct "Hm1" as (x Htv1) "[Hp1 HP1]".
  iDestruct ("H" with "HP1") as (y Htv2) "[HP2 H]".
  iExists (tele_app tp2 y).
  iSpecialize ("Heq2" $! v (Next (tele_app tp2 y))).
  iRewrite -"Heq2".
  rewrite Hm2'. rewrite iMsg_base_eq. rewrite iMsg_texist_exist.
  iSplitL "HP2".
  { iExists y. iFrame.
    iSplit; [|done].
    iPureIntro. subst. done. }
  iNext. iRewrite -"Hp1". done.
Qed.

(* TODO: Improve automation *)
(* Could clean up repeated inserts to save traverses *)
Tactic Notation "iProto_consistent_take_step_step" :=
  let i := fresh in
  let j := fresh in
  let m1 := fresh in
  let m2 := fresh in
  iIntros (i j m1 m2) "#Hm1 #Hm2";
  repeat (destruct i as [|i];
          [repeat (rewrite lookup_total_insert_ne; [|lia]);
           try (by rewrite lookup_total_empty iProto_end_message_equivI);
           try (rewrite lookup_total_insert;
                try (by rewrite iProto_end_message_equivI);
                iDestruct (iProto_message_equivI with "Hm1")
                  as "[%Heq1 Hm1']";simplify_eq)|
            repeat (rewrite lookup_total_insert_ne; [|lia]);
            try (by rewrite lookup_total_empty iProto_end_message_equivI)]);
  repeat (rewrite lookup_total_insert_ne; [|lia]);
  try rewrite lookup_total_empty;
  try (by iProto_end_message_equivI);
  rewrite lookup_total_insert;
  iDestruct (iProto_message_equivI with "Hm2")
    as "[%Heq2 Hm2']";simplify_eq;
  try (iClear "Hm1' Hm2'";
       iExists _,_,_,_,_,_,_,_,_,_;
       iSplitL "Hm1"; [iFrame "#"|];
       iSplitL "Hm2"; [iFrame "#"|];
       iSplit; [iPureIntro; tc_solve|];
       iSplit; [iPureIntro; tc_solve|];
       simpl; iClear "Hm1 Hm2"; clear m1 m2);
  try (repeat (rewrite (insert_commute _ _ i); [|done]);
  rewrite insert_insert;
  repeat (rewrite (insert_commute _ _ j); [|done]);
  rewrite insert_insert).

Tactic Notation "iProto_consistent_take_step_target" :=
  let i := fresh in
  iIntros (i j a m); rewrite /valid_target;
            iIntros "#Hm";
  repeat (destruct i as [|i];
          [repeat (rewrite lookup_total_insert_ne; [|lia]);
           try (by rewrite lookup_total_empty iProto_end_message_equivI);
           try (rewrite lookup_total_insert;
                try (by rewrite iProto_end_message_equivI);
                iDestruct (iProto_message_equivI with "Hm1")
                  as "[%Heq1 Hm1']";simplify_eq)|
            repeat (rewrite lookup_total_insert_ne; [|lia]);
            try (by rewrite lookup_total_empty iProto_end_message_equivI)]);
  repeat (rewrite lookup_total_insert_ne; [|lia]);
  try rewrite lookup_total_empty;
  try (by iProto_end_message_equivI);
  rewrite lookup_total_insert;
  iDestruct (iProto_message_equivI with "Hm")
    as "[%Heq Hm']";simplify_eq;
  repeat (try rewrite lookup_empty;
          try rewrite lookup_insert;
          rewrite lookup_insert_ne; [|lia]);
    try rewrite lookup_insert; try done.

Tactic Notation "iProto_consistent_take_step" :=
  try iNext;
  iApply iProto_consistent_equiv_proof;
  iSplitR; [iProto_consistent_take_step_target|
             iProto_consistent_take_step_step].

Tactic Notation "clean_map" constr(i) :=
  iEval (repeat (rewrite (insert_commute _ _ i); [|done]));
  rewrite (insert_insert _ i).

Definition iProto_empty {Σ} : gmap nat (iProto Σ) := ∅.

Lemma iProto_consistent_empty {Σ} :
  ⊢ iProto_consistent (@iProto_empty Σ).
Proof. iProto_consistent_take_step. Qed.

Definition iProto_binary `{!invGS Σ} : gmap nat (iProto Σ) :=
  <[0 := (<(Send, 1) @ (x:Z)> MSG #x ; END)%proto ]>
  (<[1 := (<(Recv, 0) @ (x:Z)> MSG #x ; END)%proto ]>
   ∅).

Lemma iProto_binary_consistent `{!invGS Σ} :
  ⊢ iProto_consistent (@iProto_binary Σ invGS0).
Proof.
  rewrite /iProto_binary.
  iProto_consistent_take_step.
  iIntros (x) "HP". iExists x. iSplit; [done|]. iFrame.
  iProto_consistent_take_step.
Qed.

Definition iProto_roundtrip `{!invGS Σ} : gmap nat (iProto Σ) :=
   <[0 := (<(Send, 1) @ (x:Z)> MSG #x ; <(Recv, 2)> MSG #x; END)%proto ]>
  (<[1 := (<(Recv, 0) @ (x:Z)> MSG #x ; <(Send, 2)> MSG #x; END)%proto ]>
  (<[2 := (<(Recv, 1) @ (x:Z)> MSG #x ; <(Send, 0)> MSG #x; END)%proto ]> ∅)).

Lemma iProto_roundtrip_consistent `{!invGS Σ} :
  ⊢ iProto_consistent (@iProto_roundtrip Σ invGS0).
Proof.
  rewrite /iProto_roundtrip.
  iProto_consistent_take_step.
  iIntros (x) "_". iExists x. iSplit; [done|]. iSplit; [done|].
  iProto_consistent_take_step.
  iIntros "_". iExists x. iSplit; [done|]. iSplit; [done|].
  iProto_consistent_take_step.
  iIntros "_". iSplit; [done|]. iSplit; [done|].
  iProto_consistent_take_step.
Qed.

Definition roundtrip_prog : val :=
  λ: <>,
     let: "cs" := new_chan #3 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     Fork (let: "x" := recv "c1" #0 in send "c1" #2 "x");;
     Fork (let: "x" := recv "c2" #1 in send "c2" #0 "x");;
     send "c0" #1 #42;; recv "c0" #2.

Section channel.
  Context `{!heapGS Σ, !chanG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  (* TODO: Fix nat/Z coercion. *)
  Lemma roundtrip_prog_spec :
    {{{ True }}} roundtrip_prog #() {{{ RET #42 ; True }}}.
  Proof using chanG0 heapGS0 Σ.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_chan_spec 3 iProto_roundtrip).
    { lia. }
    { set_solver. }
    { iApply iProto_roundtrip_consistent. }
    iIntros (cs) "Hcs".
    wp_smart_apply (get_chan_spec _ 0 with "Hcs"); [set_solver|].
    iIntros (c0) "[Hc0 Hcs]".
    wp_smart_apply (get_chan_spec _ 1 with "Hcs"); [set_solver|].
    iIntros (c1) "[Hc1 Hcs]".
    wp_smart_apply (get_chan_spec _ 2 with "Hcs"); [set_solver|].
    iIntros (c2) "[Hc2 Hcs]".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>". wp_recv (x) as "_". wp_send with "[//]". done. }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>". wp_recv (x) as "_". wp_send with "[//]". done. }
    wp_send with "[//]".
    wp_recv as "_".
    by iApply "HΦ".
  Qed.

End channel.

Section roundtrip_ref.
  Context `{!heapGS Σ}.

  Definition iProto_roundtrip_ref : gmap nat (iProto Σ) :=
    <[0 := (<(Send, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
            <(Recv, 2)> MSG #() {{ l ↦ #(x+2) }} ; END)%proto]>
   (<[1 := (<(Recv, 0) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
            <(Send, 2)> MSG #l {{ l ↦ #(x+1) }}; END)%proto]>
   (<[2 := (<(Recv, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
            <(Send, 0)> MSG #() {{ l ↦ #(x+1) }}; END)%proto]>
            ∅)).

  Lemma iProto_roundtrip_ref_consistent :
    ⊢ iProto_consistent iProto_roundtrip_ref.
  Proof.
    rewrite /iProto_roundtrip_ref.
    iProto_consistent_take_step.
    iIntros (l x) "Hloc". iExists _, _. iSplit; [done|]. iFrame.
    iProto_consistent_take_step.
    iIntros "Hloc". iExists _, _. iSplit; [done|]. iFrame.
    iProto_consistent_take_step.
    iIntros "Hloc". iSplit; [done|].
    replace (x + 1 + 1)%Z with (x+2)%Z by lia. iFrame.
    iProto_consistent_take_step.
  Qed.

End roundtrip_ref.

Definition roundtrip_ref_prog : val :=
  λ: <>,
     let: "cs" := new_chan #3 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     Fork (let: "l" := recv "c1" #0 in "l" <- !"l" + #1;; send "c1" #2 "l");;
     Fork (let: "l" := recv "c2" #1 in "l" <- !"l" + #1;; send "c2" #0 #());;
     let: "l" := ref #40 in send "c0" #1 "l";; recv "c0" #2;; !"l".

Section proof.
  Context `{!heapGS Σ, !chanG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Lemma roundtrip_ref_prog_spec :
    {{{ True }}} roundtrip_ref_prog #() {{{ RET #42 ; True }}}.
  Proof using chanG0.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_chan_spec 3 iProto_roundtrip_ref with "[]").
    { lia. }
    { set_solver. }
    { iApply iProto_roundtrip_ref_consistent. }
    iIntros (cs) "Hcs".
    wp_smart_apply (get_chan_spec _ 0 with "Hcs"); [set_solver|].
    iIntros (c0) "[Hc0 Hcs]".
    wp_smart_apply (get_chan_spec _ 1 with "Hcs"); [set_solver|].
    iIntros (c1) "[Hc1 Hcs]".
    wp_smart_apply (get_chan_spec _ 2 with "Hcs"); [set_solver|].
    iIntros (c2) "[Hc2 Hcs]".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>".
      wp_recv (l x) as "Hl". wp_load. wp_store. by wp_send with "[$Hl]". }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>".
      wp_recv (l x) as "Hl". wp_load. wp_store. by wp_send with "[$Hl]". }
    wp_alloc l as "Hl". wp_send with "[$Hl]". wp_recv as "Hl". wp_load.
    by iApply "HΦ".
  Qed.

End proof.

Section roundtrip_ref_rec.
  Context `{!heapGS Σ}.

  Definition iProto_roundtrip_ref_rec1_aux (rec : iProto Σ) : iProto Σ :=
    (<(Send, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
     <(Recv, 2)> MSG #() {{ l ↦ #(x+2) }} ; rec)%proto.

  Instance iProto_roundtrip_ref_rec1_contractive :
    Contractive iProto_roundtrip_ref_rec1_aux.
  Proof. solve_proto_contractive. Qed.

  Definition iProto_roundtrip_ref_rec1 :=
    fixpoint iProto_roundtrip_ref_rec1_aux.

  Lemma iProto_roundtrip_ref_rec1_unfold :
    iProto_roundtrip_ref_rec1 ≡
                (iProto_roundtrip_ref_rec1_aux iProto_roundtrip_ref_rec1).
  Proof. apply (fixpoint_unfold _). Qed.

  Global Instance iProto_roundtrip_ref_rec1_proto_unfold :
    ProtoUnfold iProto_roundtrip_ref_rec1
                (iProto_roundtrip_ref_rec1_aux iProto_roundtrip_ref_rec1).
  Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

  Definition iProto_roundtrip_ref_rec2_aux (rec : iProto Σ) : iProto Σ :=
    (<(Recv, 0) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
     <(Send, 2)> MSG #l {{ l ↦ #(x+1) }}; rec)%proto.

  Instance iProto_roundtrip_ref_rec2_contractive :
    Contractive iProto_roundtrip_ref_rec2_aux.
  Proof. solve_proto_contractive. Qed.

  Definition iProto_roundtrip_ref_rec2 :=
    fixpoint iProto_roundtrip_ref_rec2_aux.

  Lemma iProto_roundtrip_ref_rec2_unfold :
    iProto_roundtrip_ref_rec2 ≡
                (iProto_roundtrip_ref_rec2_aux iProto_roundtrip_ref_rec2).
  Proof. apply (fixpoint_unfold _). Qed.

  Global Instance iProto_roundtrip_ref_rec2_proto_unfold :
    ProtoUnfold iProto_roundtrip_ref_rec2
                (iProto_roundtrip_ref_rec2_aux iProto_roundtrip_ref_rec2).
  Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

  Definition iProto_roundtrip_ref_rec3_aux (rec : iProto Σ) : iProto Σ :=
    (<(Recv, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
     <(Send, 0)> MSG #() {{ l ↦ #(x+1) }}; rec)%proto.

  Instance iProto_roundtrip_ref_rec3_contractive :
    Contractive iProto_roundtrip_ref_rec3_aux.
  Proof. solve_proto_contractive. Qed.

  Definition iProto_roundtrip_ref_rec3 :=
    fixpoint iProto_roundtrip_ref_rec3_aux.

  Lemma iProto_roundtrip_ref_rec3_unfold :
    iProto_roundtrip_ref_rec3 ≡
                (iProto_roundtrip_ref_rec3_aux iProto_roundtrip_ref_rec3).
  Proof. apply (fixpoint_unfold _). Qed.

  Global Instance iProto_roundtrip_ref_rec3_proto_unfold :
    ProtoUnfold iProto_roundtrip_ref_rec3
                (iProto_roundtrip_ref_rec3_aux iProto_roundtrip_ref_rec3).
  Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

  Definition iProto_roundtrip_ref_rec : gmap nat (iProto Σ) :=
    <[0 := iProto_roundtrip_ref_rec1]>
   (<[1 := iProto_roundtrip_ref_rec2]>
   (<[2 := iProto_roundtrip_ref_rec3]> ∅)).

  Lemma iProto_roundtrip_ref_rec_consistent :
    ⊢ iProto_consistent iProto_roundtrip_ref_rec.
  Proof.
    iLöb as "IH".
    rewrite /iProto_roundtrip_ref_rec.
    iEval (rewrite iProto_roundtrip_ref_rec1_unfold).
    iEval (rewrite iProto_roundtrip_ref_rec2_unfold).
    iEval (rewrite iProto_roundtrip_ref_rec3_unfold).
    iProto_consistent_take_step.
    iIntros (l x) "Hloc". iExists _, _. iSplit; [done|]. iFrame.
    iProto_consistent_take_step.
    iIntros "Hloc". iExists _, _. iSplit; [done|]. iFrame. iNext.
    rewrite iProto_roundtrip_ref_rec2_unfold.
    iProto_consistent_take_step.
    iIntros "Hloc". iSplit; [done|].
    replace (x + 1 + 1)%Z with (x+2)%Z by lia. iFrame.
    rewrite -iProto_roundtrip_ref_rec2_unfold.
    do 2 clean_map 0. do 2 clean_map 1. do 2 clean_map 2.
    done.
  Qed.

End roundtrip_ref_rec.

Definition roundtrip_ref_rec_prog : val :=
  λ: <>,
     let: "cs" := new_chan #3 in
     let: "c0" := get_chan "cs" #0 in
     let: "c1" := get_chan "cs" #1 in
     let: "c2" := get_chan "cs" #2 in
     Fork ((rec: "go" "c1" :=
             let: "l" := recv "c1" #0 in "l" <- !"l" + #1;; send "c1" #2 "l";;
             "go" "c1") "c1");;
     Fork ((rec: "go" "c2" :=
           let: "l" := recv "c2" #1 in "l" <- !"l" + #1;; send "c2" #0 #();;
           "go" "c2") "c2");;
     let: "l" := ref #38 in
     send "c0" #1 "l";; recv "c0" #2;;
     send "c0" #1 "l";; recv "c0" #2;; !"l".

Section proof.
  Context `{!heapGS Σ, !chanG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Lemma roundtrip_ref_rec_prog_spec :
    {{{ True }}} roundtrip_ref_rec_prog #() {{{ RET #42 ; True }}}.
  Proof using chanG0.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_chan_spec 3 iProto_roundtrip_ref_rec with "[]").
    { lia. }
    { set_solver. }
    { iApply iProto_roundtrip_ref_rec_consistent. }
    iIntros (cs) "Hcs".
    wp_smart_apply (get_chan_spec _ 0 with "Hcs"); [set_solver|].
    iIntros (c0) "[Hc0 Hcs]".
    wp_smart_apply (get_chan_spec _ 1 with "Hcs"); [set_solver|].
    iIntros (c1) "[Hc1 Hcs]".
    wp_smart_apply (get_chan_spec _ 2 with "Hcs"); [set_solver|].
    iIntros (c2) "[Hc2 Hcs]".
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>". wp_pure _. iLöb as "IH".
      wp_recv (l x) as "Hl". wp_load. wp_store. wp_send with "[$Hl]".
      do 2 wp_pure _. by iApply "IH". }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>". wp_pure _. iLöb as "IH".
      wp_recv (l x) as "Hl". wp_load. wp_store. wp_send with "[$Hl]".
      do 2 wp_pure _. by iApply "IH". }
    wp_alloc l as "Hl". wp_send with "[$Hl]". wp_recv as "Hl".
    wp_send with "[$Hl]". wp_recv as "Hl". wp_load.
    by iApply "HΦ".
  Qed.

End proof.

Section parallel.
  Context `{!heapGS Σ}.

  (** 

    0 -> 1 : (x1:Z) < x1 > .
    0 -> 2 : (x2:Z) < x2 > .
    2 -> 3 : (y1:Z) < x1+y1 > ;
    3 -> 4 : (y2:Z) < x2+y2 > ;
    3 -> 0 : < x1+y1 > ;
    4 -> 0 : < x2+y2 > ;
    end

         0 
       /   \
      1     2
      |     |
      3     4
       \   /
         0
   *)

  Definition iProto_parallel : gmap nat (iProto Σ) :=
    <[0 := (<(Send, 1) @ (x1:Z)> MSG #x1 ;
            <(Send, 2) @ (x2:Z)> MSG #x2 ;
            <(Recv, 3) @ (y1:Z)> MSG #(x1+y1);
            <(Recv, 4) @ (y2:Z)> MSG #(x2+y2); END)%proto]>
   (<[1 := (<(Recv, 0) @ (x:Z)> MSG #x ;
            <(Send, 3) @ (y:Z)> MSG #(x+y); END)%proto]>
   (<[2 := (<(Recv, 0) @ (x:Z)> MSG #x ;
            <(Send, 4) @ (y:Z)> MSG #(x+y) ; END)%proto]>
   (<[3 := (<(Recv, 1) @ (x:Z)> MSG #x ;
            <(Send, 0)> MSG #x; END)%proto]>
   (<[4 := (<(Recv, 2) @ (x:Z)> MSG #x ;
            <(Send, 0)> MSG #x ; END)%proto]> ∅)))).

  Lemma iProto_parallel_consistent :
    ⊢ iProto_consistent iProto_parallel.
  Proof.
    rewrite /iProto_parallel.
    iProto_consistent_take_step.
    iIntros (x1) "_". iExists _. iSplit; [done|]. iSplit; [done|].
    clean_map 0. clean_map 1.
    iProto_consistent_take_step.
    - iIntros (x2) "_". iExists _. iSplit; [done|]. iSplit; [done|].
      clean_map 0. clean_map 2.
      iProto_consistent_take_step.
      + iIntros (y1) "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 1. clean_map 3.
        iProto_consistent_take_step.
        * iIntros (y2) "_". iExists _. iSplit; [done|]. iSplit; [done|].
          clean_map 2. clean_map 4.
          iProto_consistent_take_step.
          iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
          clean_map 0. clean_map 3.
          iProto_consistent_take_step.
          iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
          iProto_consistent_take_step.
        * iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
          clean_map 3. clean_map 0.
          iProto_consistent_take_step.
          iIntros (y2) "_". iExists _. iSplit; [done|]. iSplit; [done|].
          clean_map 2. clean_map 4.
          iProto_consistent_take_step.
          iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
          clean_map 4. clean_map 0.
          iProto_consistent_take_step.
      + iIntros (y1) "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 2. clean_map 4.
        iProto_consistent_take_step.
        iIntros (y2) "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 1. clean_map 3.
        iProto_consistent_take_step.
        iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 3. clean_map 0.
        iProto_consistent_take_step.
        iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 4. clean_map 0.
        iProto_consistent_take_step.
    - iIntros (y1) "_". iExists _. iSplit; [done|]. iSplit; [done|].
      clean_map 1. clean_map 3.
      iProto_consistent_take_step.
      iIntros (x2) "_". iExists _. iSplit; [done|]. iSplit; [done|].
      clean_map 0. clean_map 2.
      iProto_consistent_take_step.
      + iIntros (y2) "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 2. clean_map 4.
        iProto_consistent_take_step.
        iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 3. clean_map 0.
        iProto_consistent_take_step.
        iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 4. clean_map 0.
        iProto_consistent_take_step.
      + iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 3. clean_map 0.
        iProto_consistent_take_step.
        iIntros (z) "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 2. clean_map 4.
        iProto_consistent_take_step.
        iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
        clean_map 4. clean_map 0.
        iProto_consistent_take_step.
  Qed.

End parallel.

Section two_buyer.
  Context `{!heapGS Σ}.

  Definition two_buyer_prot : gmap nat (iProto Σ) :=
    <[0 := (<(Send, 1) @ (title:Z)> MSG #title ;
            <(Recv, 1) @ (quote:Z)> MSG #quote ;
            <(Send, 2) @ (contrib:Z)> MSG #contrib ; END)%proto]>
   (<[1 := (<(Recv, 0) @ (title:Z)> MSG #title ;
            <(Send, 0) @ (quote:Z)> MSG #quote ;
            <(Send, 2)> MSG #quote ;
            <(Recv, 2) @ (b:bool)> MSG #b ;
            if b then
              <(Recv, 2) @ (address:Z)> MSG #address ;
              <(Send, 2) @ (date:Z)> MSG #date ; END
            else END)%proto]>
   (<[2 := (<(Recv, 1) @ (quote:Z)> MSG #quote ;
            <(Recv, 0) @ (contrib:Z)> MSG #contrib ;
            if bool_decide (contrib >= quote/2)%Z then
              <(Send, 1)> MSG #true ;
              <(Send, 1) @ (address:Z)> MSG #address ;
              <(Recv, 1) @ (date:Z)> MSG #date ; END
            else
              <(Send, 1)> MSG #false ; END)%proto]>
      ∅)).

  Lemma two_buyer_prot_consistent :
    ⊢ iProto_consistent two_buyer_prot.
  Proof.
    rewrite /two_buyer_prot.
    iProto_consistent_take_step.
    iIntros (title) "_". iExists _. iSplit; [done|]. iSplit; [done|].
    clean_map 0. clean_map 1.
    iProto_consistent_take_step.
    iIntros (quote) "_". iExists _. iSplit; [done|]. iSplit; [done|].
    clean_map 0. clean_map 1.
    iProto_consistent_take_step.
    iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
    clean_map 1. clean_map 2.
    iProto_consistent_take_step.
    iIntros (contrib) "_". iExists _. iSplit; [done|]. iSplit; [done|].
    clean_map 0. clean_map 2.
    case_bool_decide.
    - iProto_consistent_take_step.
      iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
      clean_map 2. clean_map 1.
      iProto_consistent_take_step.
      iIntros (address) "_". iExists _. iSplit; [done|]. iSplit; [done|].
      clean_map 2. clean_map 1.
      iProto_consistent_take_step.
      iIntros (date) "_". iExists _. iSplit; [done|]. iSplit; [done|].
      clean_map 2. clean_map 1.
      iProto_consistent_take_step.
    - iProto_consistent_take_step.
      iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
      clean_map 2. clean_map 1.
      iProto_consistent_take_step.
  Qed.

End two_buyer.

Section two_buyer_ref.
  Context `{!heapGS Σ}.

  Definition two_buyer_ref_b1_prot : iProto Σ :=
    (<(Send, 1) @ (title:Z)> MSG #title ;
     <(Recv, 1) @ (quote:Z)> MSG #quote ;
     <(Send, 2) @ (l : loc) (amount:Z) (contrib:Z)>
       MSG (#l,#contrib) {{ l ↦ #amount }} ;
     <(Recv, 2) @ (b : bool)>
       MSG #b {{ l ↦ #(if b then amount - contrib else amount) }};
     END)%proto.

  Definition two_buyer_ref_s_prot : iProto Σ :=
    (<(Recv, 0) @ (title:Z)> MSG #title ;
     <(Send, 0) @ (quote:Z)> MSG #quote ;
     <(Send, 2)> MSG #quote ;
     <(Recv, 2) @ (b:bool)> MSG #b ;
     if b then
       <(Recv, 2) @ (l2 : loc) (amount2:Z) (address:Z)> 
         MSG (#l2,#address) {{ l2 ↦ #amount2 }} ;
       <(Send, 2) @ (date : Z)> MSG #date {{ l2 ↦ #(amount2-quote) }}; END
     else END)%proto.
  
  Definition two_buyer_ref_b2_prot : iProto Σ :=
    (<(Recv, 1) @ (quote:Z)> MSG #quote ;
     <(Recv, 0) @ (l1 : loc) (amount1:Z) (contrib:Z)>
       MSG (#l1,#contrib) {{ l1 ↦ #amount1 }};
     <(Send, 0) @ (b : bool)>
       MSG #b {{ l1 ↦ #(if b then amount1 - contrib else amount1) }};
     <(Send, 1)> MSG #b;
     if b then
       <(Send, 1) @ (l2 : loc) (amount2:Z) (address:Z)>
         MSG (#l2,#address) {{ l2 ↦ #amount2 }} ;
       <(Recv, 1) @ (date : Z)> MSG #date {{ l2 ↦ #(amount2-quote) }};
       END
     else END)%proto.

  Definition two_buyer_ref_prot : gmap nat (iProto Σ) :=
    <[0 := two_buyer_ref_b1_prot]>
   (<[1 := two_buyer_ref_s_prot]>
   (<[2 := two_buyer_ref_b2_prot]>
      ∅)).

  Lemma two_buyer_ref_prot_consistent :
    ⊢ iProto_consistent two_buyer_ref_prot.
  Proof.
    rewrite /two_buyer_prot.
    iProto_consistent_take_step.
    iIntros (title) "_". iExists _. iSplit; [done|]. iSplit; [done|].
    clean_map 0. clean_map 1.
    iProto_consistent_take_step.
    iIntros (quote) "_". iExists _. iSplit; [done|]. iSplit; [done|].
    clean_map 0. clean_map 1.
    iProto_consistent_take_step.
    iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
    clean_map 1. clean_map 2.
    iProto_consistent_take_step.
    iIntros (l1 amount1 contrib) "Hl1". iExists _,_,_. iSplit; [done|]. iFrame.
    clean_map 0. clean_map 2.
    iProto_consistent_take_step.
    iIntros (b) "Hl1". iExists _. iSplit; [done|]. iFrame.
    clean_map 0. clean_map 2.
    iProto_consistent_take_step.
    iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
    clean_map 1. clean_map 2.
    destruct b.
    - iProto_consistent_take_step.
      iIntros (l2 amount2 address) "Hl2". iExists _,_,_. iSplit; [done|]. iFrame.
      clean_map 2. clean_map 1.
      iProto_consistent_take_step.
      iIntros (date) "Hl2". iExists _. iSplit; [done|]. iFrame.
      iProto_consistent_take_step.
    - iProto_consistent_take_step.
  Qed.

End two_buyer_ref.


Section fwd.
  Context `{!heapGS Σ}.

  Definition iProto_fwd : gmap nat (iProto Σ) :=
    <[0 := (<(Send, 1) @ (x:Z)> MSG #x ;
            <(Send, 1) @ (b:bool)> MSG #b ;
            <(Send, if b then 2 else 3) > MSG #x ; END)%proto]>
   (<[1 := (<(Recv, 0) @ (x:Z)> MSG #x ;
            <(Recv, 0) @ (b:bool)> MSG #b;
            if b
            then <(Send,2)> MSG #x ; END
            else <(Send,3)> MSG #x ; END)%proto]>
   (<[2 := (<(Recv, 1) @ (x:Z)> MSG #x ;
            <(Send, 0)> MSG #x ; END)%proto]>
   (<[3 := (<(Recv, 1) @ (x:Z)> MSG #x ;
            <(Send, 0)> MSG #x ; END)%proto]> ∅))).

  Lemma iProto_fwd_consistent :
    ⊢ iProto_consistent iProto_fwd.
  Proof.
    rewrite /iProto_fwd.
    iProto_consistent_take_step.
    iIntros (x) "_". iExists _. iSplit; [done|]. iSplit; [done|].
    iProto_consistent_take_step.
    iIntros ([]) "_".
    - iExists _. iSplit; [done|]. iSplit; [done|].
      iProto_consistent_take_step.
      iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
      iProto_consistent_take_step.
    - iExists _. iSplit; [done|]. iSplit; [done|].
      iProto_consistent_take_step.
      iIntros "_". iExists _. iSplit; [done|]. iSplit; [done|].
      iProto_consistent_take_step.
  Qed.

End fwd.
