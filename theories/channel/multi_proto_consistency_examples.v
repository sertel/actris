From iris.algebra Require Import gmap excl_auth gmap_view.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.iprop.
From iris.base_logic Require Import lib.own.
From actris.channel Require Import multi_proto_model multi_proto multi_channel multi_proofmode.
Set Default Proof Using "Type".
Export action.

Lemma iProto_consistent_equiv_proof {Σ} (ps : gmap nat (iProto Σ)) :
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
  iIntros "H".
  rewrite iProto_consistent_unfold.
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

Tactic Notation "iProto_consistent_take_step" :=
  let i := fresh in
  let j := fresh in
  let m1 := fresh in
  let m2 := fresh in
  iApply iProto_consistent_equiv_proof;
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
  rewrite lookup_total_insert;
  iDestruct (iProto_message_equivI with "Hm2")
    as "[%Heq2 Hm2']";simplify_eq;
  try (iClear "Hm1' Hm2'";
       iExists _,_,_,_,_,_,_,_,_,_;
       iSplitL; [iFrame "#"|];
       iSplitL; [iFrame "#"|];
       iSplitL; [iPureIntro; tc_solve|];
       iSplitL; [iPureIntro; tc_solve|];
       simpl; iClear "#"; clear m1 m2).

Definition iProto_example1 {Σ} : gmap nat (iProto Σ) :=
  ∅.

Lemma iProto_example1_consistent {Σ} :
  ⊢ iProto_consistent (@iProto_example1 Σ).
Proof. iProto_consistent_take_step. Qed.

Definition iProto_example2 `{!invGS Σ} (P : iProp Σ) : gmap nat (iProto Σ) :=
  <[0 := (<(Send, 1) @ (x:Z)> MSG #x {{ P }} ; END)%proto ]>
  (<[1 := (<(Recv, 0) @ (x:Z)> MSG #x {{ P }} ; END)%proto ]>
   ∅).

Lemma iProto_example2_consistent `{!invGS Σ} (P : iProp Σ) :
  ⊢ iProto_consistent (@iProto_example2 Σ invGS0 P).
Proof.
  rewrite /iProto_example2.
  iProto_consistent_take_step.
  iIntros (x) "HP". iExists x. iSplit; [done|]. iFrame. iNext.
  iProto_consistent_take_step.
Qed.

Definition iProto_example3 `{!invGS Σ} : gmap nat (iProto Σ) :=
   <[0 := (<(Send, 1) @ (x:Z)> MSG #x ; <(Recv, 2)> MSG #x; END)%proto ]>
  (<[1 := (<(Recv, 0) @ (x:Z)> MSG #x ; <(Send, 2)> MSG #x; END)%proto ]>
  (<[2 := (<(Recv, 1) @ (x:Z)> MSG #x ; <(Send, 0)> MSG #x; END)%proto ]>
    ∅)).

Lemma iProto_example3_consistent `{!invGS Σ} :
  ⊢ iProto_consistent (@iProto_example3 Σ invGS0).
Proof.
  rewrite /iProto_example3.
  iProto_consistent_take_step.
  iIntros (x) "_". iExists x. iSplit; [done|]. iSplit; [done|]. iNext.
  iProto_consistent_take_step.
  iIntros "_". iExists x. iSplit; [done|]. iSplit; [done|]. iNext.
  iProto_consistent_take_step.
  iIntros "_". iSplit; [done|]. iSplit; [done|]. iNext.
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
    wp_smart_apply (new_chan_spec 3 iProto_example3).
    { intros i Hle. destruct i as [|[|[]]]; try set_solver. lia. }
    { set_solver. }
    { iApply iProto_example3_consistent. }
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

Section example4.
  Context `{!heapGS Σ}.

  Definition iProto_example4 : gmap nat (iProto Σ) :=
    <[0 := (<(Send, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
            <(Recv, 2)> MSG #() {{ l ↦ #(x+2) }} ; END)%proto]>
   (<[1 := (<(Recv, 0) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
            <(Send, 2)> MSG #l {{ l ↦ #(x+1) }}; END)%proto]>
   (<[2 := (<(Recv, 1) @ (l:loc) (x:Z)> MSG #l {{ (l ↦ #x)%I }} ;
            <(Send, 0)> MSG #() {{ l ↦ #(x+1) }}; END)%proto]>
            ∅)).

  Lemma iProto_example4_consistent :
    ⊢ iProto_consistent (iProto_example4).
  Proof.
    rewrite /iProto_example4.
    iProto_consistent_take_step.
    iIntros (l x) "Hloc". iExists _, _. iSplit; [done|]. iFrame. iNext.
    iProto_consistent_take_step.
    iIntros "Hloc". iExists _, _. iSplit; [done|]. iFrame. iNext.
    iProto_consistent_take_step.
    iIntros "Hloc". iSplit; [done|].
    replace (x + 1 + 1)%Z with (x+2)%Z by lia. iFrame. iNext.
    iProto_consistent_take_step.
  Qed.

End example4.

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
    wp_smart_apply (new_chan_spec 3 iProto_example4 with "[]").
    { intros i Hle. destruct i as [|[|[]]]; try set_solver. lia. }
    { set_solver. }
    { iApply iProto_example4_consistent. }
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
