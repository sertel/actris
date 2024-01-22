From iris.algebra Require Import gmap excl_auth gmap_view.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.iprop.
From iris.base_logic Require Import lib.own.
From iris.program_logic Require Import language.
From actris.channel Require Import multi_proto_model multi_proto multi_channel.
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
  <[0 := (<(Send 1) @ (x:Z)> MSG #x {{ P }} ; END)%proto ]>
  (<[1 := (<(Recv 0) @ (x:Z)> MSG #x {{ P }} ; END)%proto ]>
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
   <[0 := (<(Send 1) @ (x:Z)> MSG #x ; <(Recv 2)> MSG #x; END)%proto ]>
  (<[1 := (<(Recv 0) @ (x:Z)> MSG #x ; <(Send 2)> MSG #x; END)%proto ]>
  (<[2 := (<(Recv 1) @ (x:Z)> MSG #x ; <(Send 0)> MSG #x; END)%proto ]>
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
  iSpecialize ("Hm2" $!v (Next (<Send 2> iMsg_base_def #x True END)))%proto.
  iExists (<Send 2> iMsg_base_def #x True END)%proto.
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
  iSpecialize ("Hm2" $!v (Next (<Send 0> iMsg_base_def #x True END)))%proto.
  iExists (<Send 0> iMsg_base_def #x True END)%proto.
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
     let: "c0" := ! ("cs" +ₗ #0) in 
     let: "c1" := ! ("cs" +ₗ #1) in 
     let: "c2" := ! ("cs" +ₗ #2) in 
     Fork (let: "x" := recv "c1" #0 in send "c1" #2 "x");;
     Fork (let: "x" := recv "c2" #1 in send "c2" #0 "x");;
     send "c0" #1 #42;;
     recv "c0" #2.

Section channel.
  Context `{!heapGS Σ, !chanG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  Lemma roundtrip_prog_spec :
    {{{ True }}} roundtrip_prog #() {{{ RET #42 ; True }}}.
  Proof using chanG0 heapGS0 Σ.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_pures.
    wp_apply (new_chan_spec 3 iProto_example3 with "[]").
    { intros i Hle. destruct i as [|[|[]]]; try set_solver. lia. }
    { iApply iProto_example3_consistent. }
    iIntros (cs ls) "[%Hlen [Hcs Hls]]".
    assert (is_Some (ls !! 0)) as [c0 HSome0].
    { apply lookup_lt_is_Some_2. lia. }
    assert (is_Some (ls !! 1)) as [c1 HSome1].
    { apply lookup_lt_is_Some_2. lia. }
    assert (is_Some (ls !! 2)) as [c2 HSome2].
    { apply lookup_lt_is_Some_2. lia. }
    wp_smart_apply (wp_load_offset _ _ _ _ 0 with "Hcs"); [done|].
    iIntros "Hcs".
    wp_smart_apply (wp_load_offset _ _ _ _ 1 with "Hcs"); [done|].
    iIntros "Hcs".
    wp_smart_apply (wp_load_offset _ _ _ _ 2 with "Hcs"); [done|].
    iIntros "Hcs".
    iDestruct (big_sepL_delete' _ _ 0 with "Hls") as "[Hc0 Hls]"; [set_solver|].
    iDestruct (big_sepL_delete' _ _ 1 with "Hls") as "[Hc1 Hls]"; [set_solver|].
    iDestruct (big_sepL_delete' _ _ 2 with "Hls") as "[Hc2 _]"; [set_solver|].
    iDestruct ("Hc1" with "[//]") as "Hc1".
    iDestruct ("Hc2" with "[//] [//]") as "Hc2".
    rewrite /iProto_example3.
    rewrite !lookup_total_insert.
    rewrite lookup_total_insert_ne; [|done].
    rewrite !lookup_total_insert.
    rewrite lookup_total_insert_ne; [|done].
    rewrite lookup_total_insert_ne; [|done].
    rewrite !lookup_total_insert.
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>".
      wp_smart_apply
        (recv_spec (TT:=[tele Z]) c1 1 0
                   (tele_app (λ (x:Z), #x)) (λ _, True)%I (tele_app (λ (x:Z), _))
          with "Hc1").
      iIntros (x') "[Hc1 _]".
      epose proof (tele_arg_S_inv x') as [x [[] ->]]. simpl.
      wp_smart_apply (send_spec c1 1 2 with "Hc1").
      by iIntros "_". }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>".
      wp_smart_apply
        (recv_spec (TT:=[tele Z]) c2 2 1
                   (tele_app (λ (x:Z), #x)) (λ _, True)%I (tele_app (λ (x:Z), _))
                   with "Hc2").
      iIntros (x') "[Hc1 _]".
      epose proof (tele_arg_S_inv x') as [x [[] ->]]. simpl.
      wp_smart_apply (send_spec c2 2 0 with "Hc1").
      by iIntros "_". }
    wp_smart_apply
      (send_spec_tele (TT:=[tele Z]) c0 1 0 ([tele_arg 42%Z])
                      (tele_app (λ (x:Z), #x)) (λ _, True)%I
                      (tele_app (λ (x:Z), _))
                   with "[Hc0]").
    { iSplitL; [|done]. simpl. iFrame "Hc0". }
    iIntros "Hc0".
    wp_smart_apply (recv_spec (TT:=[tele]) c0 0 2
                              (λ _, #42)
                              (λ _, True)%I
                              (λ _, _)
                      with "Hc0").
    iIntros (_) "Hc0".
    by iApply "HΦ".
  Qed.

End channel.
