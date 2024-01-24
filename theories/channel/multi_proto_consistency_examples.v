From iris.algebra Require Import gmap excl_auth gmap_view.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.iprop.
From iris.base_logic Require Import lib.own.
From actris.channel Require Import multi_proto_model multi_proto multi_channel multi_proofmode.
Set Default Proof Using "Type".
Export action.

Definition iProto_example1 {Σ} : gmap nat (iProto Σ) :=
  ∅.

Lemma iProto_example1_consistent {Σ} :
  ⊢ iProto_consistent (@iProto_example1 Σ).
Proof.
  rewrite iProto_consistent_unfold.
  iIntros (i j m1 m2) "Hi Hj".
  rewrite lookup_total_empty.
  by rewrite iProto_end_message_equivI.
Qed.

Definition iProto_example2 `{!invGS Σ} (P : iProp Σ) : gmap nat (iProto Σ) :=
  <[0 := (<(Send, 1) @ (x:Z)> MSG #x {{ P }} ; END)%proto ]>
  (<[1 := (<(Recv, 0) @ (x:Z)> MSG #x {{ P }} ; END)%proto ]>
   ∅).

Lemma iProto_example2_consistent `{!invGS Σ} (P : iProp Σ) :
  ⊢ iProto_consistent (@iProto_example2 Σ invGS0 P).
Proof.
  rewrite iProto_consistent_unfold.
  rewrite /iProto_example2.
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i, j.
  - rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    iDestruct "Hm1" as (Hieq) "#Hm1".
    iDestruct "Hm2" as (Hjeq) "#Hm2".
    done.
  - destruct j; last first.
    { rewrite !lookup_total_insert.
      rewrite !iProto_message_equivI.
      iDestruct "Hm1" as (Hieq) "#Hm1". done. }
    rewrite !lookup_total_insert.
    rewrite lookup_total_insert_ne; [|done].
    rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    iDestruct "Hm1" as (Hieq) "#Hm1".
    iDestruct "Hm2" as (Hjeq) "#Hm2".
    iIntros (v p1) "Hm1'".
    iSpecialize ("Hm1" $!v (Next p1)).
    rewrite iMsg_base_eq. simpl.
    rewrite iMsg_exist_eq. simpl.
    iRewrite -"Hm1" in "Hm1'".
    iExists END%proto.
    iSpecialize ("Hm2" $!v (Next END%proto)).
    iRewrite -"Hm2".
    simpl.
    iDestruct "Hm1'" as (x Heq) "[#Heq HP]".
    iSplitL.
    { iExists x. iSplit; [done|]. iFrame. done. }
    iNext. iRewrite -"Heq".
    rewrite insert_commute; [|done].
    rewrite insert_insert.
    rewrite insert_commute; [|done].
    rewrite insert_insert.
    rewrite iProto_consistent_unfold.
    iIntros (i' j' m1' m2') "Hm1' Hm2'".
    destruct i'.
    { rewrite lookup_total_insert.
      iDestruct (iProto_end_message_equivI with "Hm1'") as "H".
      done. }
    destruct i'.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert.
      iDestruct (iProto_end_message_equivI with "Hm1'") as "H".
      done. }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_alt. simpl.
    iDestruct (iProto_end_message_equivI with "Hm1'") as "H".
    done.
  - destruct i; last first.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_alt. simpl.
      iDestruct (iProto_end_message_equivI with "Hm1") as "H".
      done. }
    rewrite !lookup_total_insert.
    rewrite lookup_total_insert_ne; [|done].
    rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    iDestruct "Hm1" as (Hieq) "#Hm1". done.
  - destruct i.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert.
      rewrite !iProto_message_equivI.
      iDestruct "Hm1" as (Hieq) "#Hm1". done. }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_alt. simpl.
    iDestruct (iProto_end_message_equivI with "Hm1") as "H".
    done.
Qed.

Definition iProto_example3 `{!invGS Σ} : gmap nat (iProto Σ) :=
   <[0 := (<(Send, 1) @ (x:Z)> MSG #x ; <(Recv, 2)> MSG #x; END)%proto ]>
  (<[1 := (<(Recv, 0) @ (x:Z)> MSG #x ; <(Send, 2)> MSG #x; END)%proto ]>
  (<[2 := (<(Recv, 1) @ (x:Z)> MSG #x ; <(Send, 0)> MSG #x; END)%proto ]>
    ∅)).

Lemma iProto_example3_consistent `{!invGS Σ} :
  ⊢ iProto_consistent (@iProto_example3 Σ invGS0).
Proof.
  rewrite iProto_consistent_unfold.
  rewrite /iProto_example3.
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i; last first.
  { destruct i.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite !lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm1" as (Hieq) "#Hm1". }
    destruct i.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert_ne; [|done].
      rewrite !iProto_message_equivI.
      by iDestruct "Hm1" as (Hieq) "#Hm1". }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty=> /=.
    by rewrite iProto_end_message_equivI. }
  destruct j.
  { rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm2" as (Hjeq) "#Hm2". }
  destruct j; last first.
  { rewrite !lookup_total_insert.
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    destruct j.
    { rewrite !lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm2" as (Hjeq) "#Hm2". }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty=> /=.
    by rewrite iProto_end_message_equivI. }
  rewrite !lookup_total_insert.
  rewrite lookup_total_insert_ne; [|done].
  rewrite !lookup_total_insert.
  rewrite !iProto_message_equivI.
  iDestruct "Hm1" as (Hieq) "#Hm1".
  iDestruct "Hm2" as (Hjeq) "#Hm2".
  iIntros (v p1) "Hm1'".
  iSpecialize ("Hm1" $!v (Next p1)).
  rewrite !iMsg_base_eq.
  rewrite !iMsg_exist_eq.
  iRewrite -"Hm1" in "Hm1'".
  iDestruct "Hm1'" as (x Heq) "[#Hm1' _]".
  iSpecialize ("Hm2" $!v (Next (<(Send, 2)> iMsg_base_def #x True END)))%proto.
  iExists (<(Send, 2)> iMsg_base_def #x True END)%proto.
  iRewrite -"Hm2".
  simpl.
  iSplitL.
  { iExists x. iSplit; [done|]. iFrame. done. }
  iNext.
  rewrite iProto_consistent_unfold.
  rewrite insert_commute; [|done].
  rewrite insert_insert.
  rewrite insert_commute; [|done].
  rewrite insert_insert.
  iRewrite -"Hm1'".
  iClear (m1 m2 Hieq Hjeq p1 v Heq) "Hm1 Hm2 Hm1'".
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i.
  { rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm1" as (Hieq) "#Hm1". }
  rewrite lookup_total_insert_ne; [|done].
  destruct i; last first.
  { destruct i.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm1" as (Hieq) "#Hm1". }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty=> /=.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert.
  destruct j.
  { rewrite lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm2" as (Hjeq) "#Hm2". }
  rewrite lookup_total_insert_ne; [|done].
  destruct j.
  { rewrite lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm2" as (Hjeq) "#Hm2". }
  rewrite lookup_total_insert_ne; [|done].
  destruct j; last first.
  { rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert.
  rewrite !iProto_message_equivI.
  iDestruct "Hm1" as (Hieq) "#Hm1".
  iDestruct "Hm2" as (Hjeq) "#Hm2".
  iIntros (v p1) "Hm1'".
  iSpecialize ("Hm1" $!v (Next p1)).
  iRewrite -"Hm1" in "Hm1'".
  iDestruct "Hm1'" as (Heq) "[#Hm1' _]".
  iSpecialize ("Hm2" $!v (Next (<(Send, 0)> iMsg_base_def #x True END)))%proto.
  iExists (<(Send, 0)> iMsg_base_def #x True END)%proto.
  iRewrite -"Hm2".
  simpl.
  iSplitL.
  { iExists x. iSplit; [done|]. iFrame. done. }
  iNext.
  rewrite iProto_consistent_unfold.
  rewrite (insert_commute _ 1 2); [|done].
  rewrite (insert_commute _ 1 0); [|done].
  rewrite insert_insert.
  rewrite (insert_commute _ 2 0); [|done].
  rewrite (insert_commute _ 2 1); [|done].
  rewrite insert_insert.
  iRewrite -"Hm1'".
  iClear (m1 m2 Hieq Hjeq p1 v Heq) "Hm1 Hm2 Hm1'".
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i.
  { rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    by iDestruct "Hm1" as (Hieq) "#Hm1". }
  rewrite lookup_total_insert_ne; [|done].
  destruct i.
  { rewrite lookup_total_insert.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert_ne; [|done].
  destruct i; last first.
  { rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert.
  destruct j; last first.
  { rewrite lookup_total_insert_ne; [|done].
    destruct j.
    { rewrite lookup_total_insert.
      by rewrite iProto_end_message_equivI. }
    rewrite lookup_total_insert_ne; [|done].
    destruct j.
    { rewrite lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm2" as (Hjeq) "#Hm2". }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty.
    by rewrite iProto_end_message_equivI. }
  rewrite lookup_total_insert.
  rewrite !iProto_message_equivI.
  iDestruct "Hm1" as (Hieq) "#Hm1".
  iDestruct "Hm2" as (Hjeq) "#Hm2".
  iIntros (v p1) "Hm1'".
  iSpecialize ("Hm1" $!v (Next p1)).
  iRewrite -"Hm1" in "Hm1'".
  iDestruct "Hm1'" as (Heq) "[#Hm1' _]".
  iSpecialize ("Hm2" $!v (Next END))%proto.
  iExists END%proto.
  iRewrite -"Hm2".
  simpl.
  iSplitL; [done|].
  rewrite insert_insert.
  rewrite insert_commute; [|done].
  rewrite (insert_commute _ 2 1); [|done].
  rewrite insert_insert.
  iNext.
  iRewrite -"Hm1'".
  rewrite iProto_consistent_unfold.
  iClear (m1 m2 Hieq Hjeq p1 v Heq) "Hm1 Hm2 Hm1'".
  iIntros (i j m1 m2) "Hm1 Hm2".
  destruct i.
  { rewrite lookup_total_insert.
    by rewrite !iProto_end_message_equivI. }
  rewrite lookup_total_insert_ne; [|done].
  destruct i.
  { rewrite lookup_total_insert.
    by rewrite !iProto_end_message_equivI. }
  rewrite lookup_total_insert_ne; [|done].
  destruct i.
  { rewrite lookup_total_insert.
    by rewrite !iProto_end_message_equivI. }
  rewrite lookup_total_insert_ne; [|done].
  rewrite lookup_total_empty.
  by rewrite iProto_end_message_equivI.
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
    { iIntros "!>".
      (* TODO: Fix unification *)
      wp_recv (x) as "_"; [done|].
      wp_send with "[//]"; [done|].
      done. }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>".
      wp_recv (x) as "_"; [done|].
      wp_send with "[//]"; [done|].
      done. }
    wp_send with "[//]"; [done|].
    wp_recv as "_"; [done|].
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
    rewrite iProto_consistent_unfold.
    rewrite /iProto_example4.
    iIntros (i j m1 m2) "Hm1 Hm2".
    destruct i; last first.
    { destruct i.
      { rewrite lookup_total_insert_ne; [|done].
        rewrite !lookup_total_insert.
        rewrite !iProto_message_equivI.
        by iDestruct "Hm1" as (Hieq) "#Hm1". }
      destruct i.
      { rewrite lookup_total_insert_ne; [|done].
        rewrite lookup_total_insert_ne; [|done].
        rewrite !iProto_message_equivI.
        by iDestruct "Hm1" as (Hieq) "#Hm1". }
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_empty=> /=.
      by rewrite iProto_end_message_equivI. }
    destruct j.
    { rewrite !lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm2" as (Hjeq) "#Hm2". }
    destruct j; last first.
    { rewrite !lookup_total_insert.
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert_ne; [|done].
      destruct j.
      { rewrite !lookup_total_insert.
        rewrite !iProto_message_equivI.
        by iDestruct "Hm2" as (Hjeq) "#Hm2". }
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_empty=> /=.
      by rewrite iProto_end_message_equivI. }
    rewrite !lookup_total_insert.
    rewrite lookup_total_insert_ne; [|done].
    rewrite !lookup_total_insert.
    rewrite !iProto_message_equivI.
    iDestruct "Hm1" as (Hieq) "#Hm1".
    iDestruct "Hm2" as (Hjeq) "#Hm2".
    iIntros (v p1) "Hm1'".
    iSpecialize ("Hm1" $!v (Next p1)).
    rewrite !iMsg_base_eq.
    rewrite !iMsg_exist_eq.
    iRewrite -"Hm1" in "Hm1'".
    iDestruct "Hm1'" as (l x <-) "[#Hm1' Hl]". simpl.
    iSpecialize ("Hm2" $!#l (Next (<(Send, 2)> iMsg_base_def #l
                                                          (l ↦ #(x+1)) END)))%proto.
    Unshelve. 2-4: apply _.     (* Why is this needed? *)
    iExists (<(Send, 2)> iMsg_base_def #l (l ↦ #(x+1)) END)%proto.
    simpl.
    iSplitL.
    { iRewrite -"Hm2". iExists l, x. iSplit; [done|]. iFrame. done. }
    iNext.
    rewrite iProto_consistent_unfold.
    rewrite insert_commute; [|done].
    rewrite insert_insert.
    rewrite insert_commute; [|done].
    rewrite insert_insert.
    iRewrite -"Hm1'".
    iClear (m1 m2 Hieq Hjeq p1) "Hm1 Hm2 Hm1'".
    iIntros (i j m1 m2) "Hm1 Hm2".
    destruct i.
    { rewrite !lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm1" as (Hieq) "#Hm1". }
    rewrite lookup_total_insert_ne; [|done].
    destruct i; last first.
    { destruct i.
      { rewrite lookup_total_insert_ne; [|done].
        rewrite lookup_total_insert.
        rewrite !iProto_message_equivI.
        by iDestruct "Hm1" as (Hieq) "#Hm1". }
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_empty=> /=.
      by rewrite iProto_end_message_equivI. }
    rewrite lookup_total_insert.
    destruct j.
    { rewrite lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm2" as (Hjeq) "#Hm2". }
    rewrite lookup_total_insert_ne; [|done].
    destruct j.
    { rewrite lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm2" as (Hjeq) "#Hm2". }
    rewrite lookup_total_insert_ne; [|done].
    destruct j; last first.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_empty.
      by rewrite iProto_end_message_equivI. }
    rewrite lookup_total_insert.
    rewrite !iProto_message_equivI.
    iDestruct "Hm1" as (Hieq) "#Hm1".
    iDestruct "Hm2" as (Hjeq) "#Hm2".
    iIntros (v p1) "Hm1'".
    iSpecialize ("Hm1" $!v (Next p1)).
    iRewrite -"Hm1" in "Hm1'".
    iDestruct "Hm1'" as (<-) "[#Hm1' Hl]".
    simpl.
    iSpecialize ("Hm2" $!#l (Next (<(Send, 0)> iMsg_base_def #() (l ↦ #(x+1+1)) END)))%proto.
    iExists (<(Send, 0)> iMsg_base_def #() (l ↦ #(x+1+1)) END)%proto.
    Unshelve. 2-4: apply _.    
    iRewrite -"Hm2".
    simpl.
    iSplitL.
    { iExists l, (x+1)%Z. iSplit; [done|]. iFrame. done. }
    iNext.
    rewrite iProto_consistent_unfold.
    rewrite (insert_commute _ 1 2); [|done].
    rewrite (insert_commute _ 1 0); [|done].
    rewrite insert_insert.
    rewrite (insert_commute _ 2 0); [|done].
    rewrite (insert_commute _ 2 1); [|done].
    rewrite insert_insert.
    iRewrite -"Hm1'".
    iClear (m1 m2 Hieq Hjeq p1) "Hm1 Hm2 Hm1'".
    iIntros (i j m1 m2) "Hm1 Hm2".
    destruct i.
    { rewrite !lookup_total_insert.
      rewrite !iProto_message_equivI.
      by iDestruct "Hm1" as (Hieq) "#Hm1". }
    rewrite lookup_total_insert_ne; [|done].
    destruct i.
    { rewrite lookup_total_insert.
      by rewrite iProto_end_message_equivI. }
    rewrite lookup_total_insert_ne; [|done].
    destruct i; last first.
    { rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_empty.
      by rewrite iProto_end_message_equivI. }
    rewrite lookup_total_insert.
    destruct j; last first.
    { rewrite lookup_total_insert_ne; [|done].
      destruct j.
      { rewrite lookup_total_insert.
        by rewrite iProto_end_message_equivI. }
      rewrite lookup_total_insert_ne; [|done].
      destruct j.
      { rewrite lookup_total_insert.
        rewrite !iProto_message_equivI.
        by iDestruct "Hm2" as (Hjeq) "#Hm2". }
      rewrite lookup_total_insert_ne; [|done].
      rewrite lookup_total_empty.
      by rewrite iProto_end_message_equivI. }
    rewrite lookup_total_insert.
    rewrite !iProto_message_equivI.
    iDestruct "Hm1" as (Hieq) "#Hm1".
    iDestruct "Hm2" as (Hjeq) "#Hm2".
    iIntros (v p1) "Hm1'".
    iSpecialize ("Hm1" $!v (Next p1)).
    iRewrite -"Hm1" in "Hm1'".
    iDestruct "Hm1'" as (<-) "[#Hm1' Hl]".
    iSpecialize ("Hm2" $!#() (Next END))%proto.
    iExists END%proto.
    iRewrite -"Hm2".
    simpl.
    replace (x + 1 + 1)%Z with (x+2)%Z by lia.
    iSplitL; [iFrame;done|].
    rewrite insert_insert.
    rewrite insert_commute; [|done].
    rewrite (insert_commute _ 2 1); [|done].
    rewrite insert_insert.
    iNext.
    iRewrite -"Hm1'".
    rewrite iProto_consistent_unfold.
    iClear (m1 m2 Hieq Hjeq p1) "Hm1 Hm2 Hm1'".
    iIntros (i j m1 m2) "Hm1 Hm2".
    destruct i.
    { rewrite lookup_total_insert.
      by rewrite !iProto_end_message_equivI. }
    rewrite lookup_total_insert_ne; [|done].
    destruct i.
    { rewrite lookup_total_insert.
      by rewrite !iProto_end_message_equivI. }
    rewrite lookup_total_insert_ne; [|done].
    destruct i.
    { rewrite lookup_total_insert.
      by rewrite !iProto_end_message_equivI. }
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_empty.
    by rewrite iProto_end_message_equivI.
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
      wp_recv (l x) as "Hl"; [done|].
      wp_load. wp_store.
      wp_send with "[$Hl]"; [done|].
      done. }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>".
      wp_recv (l x) as "Hl"; [done|].
      wp_load. wp_store.
      wp_send with "[$Hl]"; [done|].
      done. }
    wp_alloc l as "Hl".
    wp_send with "[$Hl]"; [done|].
    wp_recv as "Hl"; [done|]. wp_load. by iApply "HΦ".
  Qed.

End proof.
