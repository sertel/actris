(**
A mechanisation of a binary variant of the subtyping
example on page 23 of the paper:
"On the Preciseness of Subtyping in Session Types"
https://arxiv.org/pdf/1610.00328.pdf
*)
From actris.channel Require Import proofmode proto channel.
From actris.logrel Require Import subtyping_rules.
From iris.proofmode Require Import tactics.

Section choice_example.
  Context `{heapG Σ, chanG Σ}.

  Variables Sr Sm Sp Sq Ss Su : ltty Σ.
  Variables Srm Ssm Srp Ssp Sr' : ltty Σ.
  Variables Tr Ts Tu Tr' Ts' Tq : lsty Σ.

  (**
  The subtype
  ?Sr.((!Srm.Tr) <+> (!Srp.Tr') <+> (!Sq.Tq))
  <&>
  ?Ss.((!Ssm.Ts) <+> (!Ssp.Ts'))
   *)
  Definition prot_sub : lsty Σ :=
    (lty_branch
       (<[1%Z:= <??> TY Sr ;
         lty_select
           (<[1%Z:= <!!> TY Srm ; Tr]>
            (<[2%Z:= <!!> TY Srp ; Tr']>
             (<[3%Z:= <!!> TY Sq ; Tq]>∅)))]>
        (<[2%Z:= <??> TY Ss ;
          lty_select
            (<[1%Z := <!!> TY Ssm ; Ts]>
             (<[2%Z := <!!> TY Ssp ; Ts']>∅))]>∅)))%lty.


  (**
  The supertype
  !Sm.((?Sr.Tr) <&> (?Ss.Ts) <&> (?Su.Tu))
  <+>
  !Sp.((?Sr'.Tr') <&> (?Ss.Ts'))
   *)
  Definition prot_sup : lsty Σ :=
    (lty_select
       (<[1%Z:= <!!> TY Sm ; lty_branch
                              (<[1%Z:= <??> TY Sr ; Tr]>
                               (<[2%Z:= <??> TY Ss ; Ts]>
                               (<[3%Z:= <??> TY Su ; Tu]>∅)))]>
        (<[2%Z:= <!!> TY Sp ; lty_branch
                               (<[1%Z := <??> TY Sr' ; Tr']>
                                (<[2%Z := <??> TY Ss ; Ts']>∅))]>∅)))%lty.

  (**
  Weaken select
  ?Sr.((!Srm.Tr) <+> (!Srp.Tr'))
  <&>
  ?Ss.((!Ssm.Ts) <+> (!Ssp.Ts'))
  *)
  Definition prot1 : lsty Σ :=
    (lty_branch
       (<[1%Z:= <??> TY Sr ;
         lty_select
           (<[1%Z:= <!!> TY Srm ; Tr]>
            (<[2%Z:= <!!> TY Srp ; Tr']>∅))]>
        (<[2%Z:= <??> TY Ss ;
          lty_select
            (<[1%Z := <!!> TY Ssm ; Ts]>
             (<[2%Z := <!!> TY Ssp; Ts']>∅))]>∅)))%lty.

  (**
  Swap recv/select
  ((?Sr.!Srm.Tr) <+> (?Sr.!Srp.Tr'))
  <&>
  ((?Ss.!Ssm.Ts) <+> (?Ss.!Ssp.Ts'))
  *)
  Definition prot2 : lsty Σ :=
    (lty_branch
       (<[1%Z:= lty_select
                  (<[1%Z:= <??> TY Sr ; <!!> TY Srm ; Tr]>
                   (<[2%Z:= <??> TY Sr ; <!!> TY Srp ; Tr']>∅))]>
        (<[2%Z:= lty_select
                   (<[1%Z := <??> TY Ss ; <!!> TY Ssm ; Ts]>
                    (<[2%Z := <??> TY Ss ; <!!> TY Ssp; Ts']>∅))]>∅)))%lty.

  (**
  swap branch/select
  ((?Sr.!Srm.Tr) <&> (?Ss.!Ssm.Ts))
  <+>
  ((?Sr.!Srp.Tr') <&> (?Ss.!Ssp.Ts'))
  *)
  Definition prot3 : lsty Σ :=
    (lty_select
       (<[1%Z:= lty_branch
                  (<[1%Z:= <??> TY Sr ; <!!> TY Srm ; Tr]>
                   (<[2%Z:= <??> TY Ss ; <!!> TY Ssm ; Ts]>∅))]>
        (<[2%Z:= lty_branch
                   (<[1%Z := <??> TY Sr ; <!!> TY Srp ; Tr']>
                    (<[2%Z := <??> TY Ss ; <!!> TY Ssp; Ts']>∅))]>∅)))%lty.

  (**
  swap recv/send
  ((!Srm.?Sr.Tr) <&> (!Ssm.?Ss.Ts))
  <+>
  ((!Srp.?Sr.Tr') <&> (!Ssp.?Ss.Ts'))
  *)
  Definition prot4 : lsty Σ :=
    (lty_select
       (<[1%Z:= lty_branch
                  (<[1%Z:= <!!> TY Srm ; <??> TY Sr ; Tr]>
                   (<[2%Z:= <!!> TY Ssm ; <??> TY Ss ; Ts]>∅))]>
        (<[2%Z:= lty_branch
                   (<[1%Z := <!!> TY Srp ; <??> TY Sr ; Tr']>
                    (<[2%Z := <!!> TY Ssp ; <??> TY Ss ; Ts']>∅))]>∅)))%lty.

  (**
  Subtype messages
  ((!Sm.?Sr.Tr) <&> (!Sm.?Ss.Ts))
  <+>
  ((!Sp.?Sr'.Tr') <&> (!Sp.?Ss.Ts'))
  *)
  Definition prot5 : lsty Σ :=
    (lty_select
       (<[1%Z:= lty_branch
                  (<[1%Z:= <!!> TY Sm ; <??> TY Sr ; Tr]>
                   (<[2%Z:= <!!> TY Sm ; <??> TY Ss ; Ts]>∅))]>
        (<[2%Z:= lty_branch
                   (<[1%Z := <!!> TY Sp ; <??> TY Sr' ; Tr']>
                    (<[2%Z := <!!> TY Sp ; <??> TY Ss ; Ts']>∅))]>∅)))%lty.

  (**
  Swap branch/send
  (!Sm.((?Sr.Tr) <&> (?Ss.Ts)))
  <+>
  (!Sp.((?Sr'.Tr') <&> (!Sp.?Ss.Ts')))
  *)
  Definition prot6 : lsty Σ :=
    (lty_select
       (<[1%Z:= <!!> TY Sm ;
         lty_branch (<[1%Z:= <??> TY Sr ; Tr]>
                     (<[2%Z:= <??> TY Ss ; Ts]>∅))]>
        (<[2%Z:= <!!> TY Sp ;
          lty_branch
            (<[1%Z := <??> TY Sr' ; Tr']>
             (<[2%Z := <??> TY Ss ; Ts']>∅))]>∅)))%lty.

  Lemma subtype_proof :
    Sm <: Srm -∗ Sm <: Ssm -∗ Sp <: Srp -∗ Sp <: Ssp -∗ Sr <: Sr' -∗
    prot_sub <: prot_sup.
  Proof.
    iIntros "#HRM #HSM #HRP #HSP #HR".
    (** Weakening of select *)
    iApply (lty_le_trans _ prot1).
    {
      iApply lty_le_branch.
      rewrite big_sepM2_insert=> //.
      iSplit.
      - iApply lty_le_recv; [iApply lty_le_refl | ].
        iApply lty_le_select_subseteq.
        rewrite (insert_commute _ 2%Z 3%Z) //.
        rewrite (insert_commute _ 1%Z 3%Z) //.
        by apply insert_subseteq.
      - rewrite big_sepM2_insert //. eauto.
    }
    (** Swap recv/select *)
    iApply (lty_le_trans _ prot2).
    {
      iApply lty_le_branch.
      rewrite big_sepM2_insert=> //.
      iSplit.
      - iApply lty_le_swap_recv_select.
      - rewrite big_sepM2_insert=> //. iSplit=> //.
        iApply lty_le_swap_recv_select.
    }
    (** Swap branch/select *)
    iApply (lty_le_trans _ prot3).
    {
      iApply (lty_le_swap_branch_select
                (<[1%Z:=
                     <[1%Z:=(<??> TY Sr; <!!> TY Srm; Tr)%lty]>
                     (<[2%Z:= (<??> TY Sr; <!!> TY Srp; Tr')%lty]>∅)]>
                 (<[2%Z:=
                     <[1%Z:=(<??> TY Ss; <!!> TY Ssm; Ts)%lty]>
                     (<[2%Z:= (<??> TY Ss; <!!> TY Ssp; Ts')%lty]>∅)]>∅))
                (<[1%Z:=
                     <[1%Z:=(<??> TY Sr; <!!> TY Srm; Tr)%lty]>
                     (<[2%Z:= (<??> TY Ss; <!!> TY Ssm; Ts)%lty]>∅)]>
                 (<[2%Z:=
                     <[1%Z:=(<??> TY Sr; <!!> TY Srp; Tr')%lty]>
                     (<[2%Z:= (<??> TY Ss; <!!> TY Ssp; Ts')%lty]>∅)]>∅))
             ).
      intros i j Ss1' Ss2' Hin1 Hin2.
      assert (i = 1%Z ∨ i = 2%Z).
      {
        destruct (decide (i = 1)). eauto.
        destruct (decide (i = 2)). eauto.
        rewrite lookup_insert_ne in Hin1=> //.
        rewrite lookup_insert_ne in Hin1=> //.
      }
      assert (j = 1%Z ∨ j = 2%Z).
      {
        destruct (decide (j = 1)). eauto.
        destruct (decide (j = 2)). eauto.
        rewrite lookup_insert_ne in Hin2=> //.
        rewrite lookup_insert_ne in Hin2=> //.
      }
      destruct H2 as [-> | ->] ,H1 as [-> | ->].
      - rewrite lookup_insert in Hin1.
        rewrite lookup_insert in Hin2.
        inversion Hin1; inversion Hin2; eauto.
      - rewrite (insert_commute _ 1%Z 2%Z) in Hin1=> //.
        rewrite lookup_insert in Hin1.
        rewrite lookup_insert in Hin2.
        inversion Hin1; inversion Hin2; eauto.
      - rewrite (insert_commute _ 1%Z 2%Z) in Hin2=> //.
        rewrite lookup_insert in Hin1.
        rewrite lookup_insert in Hin2.
        inversion Hin1; inversion Hin2; eauto.
      - rewrite (insert_commute _ 1%Z 2%Z) in Hin1=> //.
        rewrite (insert_commute _ 1%Z 2%Z) in Hin2=> //.
        rewrite lookup_insert in Hin1.
        rewrite lookup_insert in Hin2.
        inversion Hin1; inversion Hin2; eauto.
    }
    (** Swap recv/send *)
    iApply (lty_le_trans _ prot4).
    {
      iApply lty_le_select.
      rewrite big_sepM2_insert=> //. iSplit.
      - iApply lty_le_branch. iIntros "!>".
        rewrite big_sepM2_insert=> //. iSplit.
        + iApply lty_le_swap_recv_send.
        + rewrite big_sepM2_insert=> //.
          iSplit=> //. iApply lty_le_swap_recv_send.
      - rewrite big_sepM2_insert=> //. iSplit=> //.
        iApply lty_le_branch. iIntros "!>".
        rewrite big_sepM2_insert=> //. iSplit.
        + iApply lty_le_swap_recv_send.
        + rewrite big_sepM2_insert=> //.
          iSplit=> //. iApply lty_le_swap_recv_send.
    }
    iApply (lty_le_trans _ prot5).
    {
      iApply lty_le_select.
      rewrite big_sepM2_insert=> //. iSplit.
      - iApply lty_le_branch. iIntros "!>".
        rewrite big_sepM2_insert=> //. iSplit.
        + iApply lty_le_send; eauto.
        + rewrite big_sepM2_insert=> //. iSplit=> //.
          iApply lty_le_send; eauto.
      - rewrite big_sepM2_insert=> //. iSplit=> //.
        iApply lty_le_branch. iIntros "!>".
        rewrite big_sepM2_insert=> //. iSplit.
        + iApply lty_le_send; [eauto|].
          iApply lty_le_recv; eauto.
        + rewrite big_sepM2_insert=> //. iSplit=> //.
          iApply lty_le_send; eauto.
    }
    (** Swap branch/send *)
    iApply (lty_le_trans _ prot6).
    {
      iApply lty_le_select.
      rewrite big_sepM2_insert=> //. iSplit.
      - iApply (lty_le_swap_branch_send _
          (<[1%Z:=(<??> TY Sr; Tr)%lty]> (<[2%Z:=(<??> TY Ss; Ts)%lty]> ∅))).
      - rewrite big_sepM2_insert=> //. iSplit=> //.
        iApply (lty_le_swap_branch_send _
          ((<[1%Z:=(<??> TY Sr'; Tr')%lty]> (<[2%Z:=(<??> TY Ss; Ts')%lty]> ∅)))).
    }
    (** Weaken branch *)
    iApply lty_le_select.
    rewrite big_sepM2_insert=> //. iSplit=> //.
    - iApply lty_le_send; [iApply lty_le_refl|].
      iApply lty_le_branch_subseteq.
      rewrite (insert_commute _ 2%Z 3%Z) //.
      rewrite (insert_commute _ 1%Z 3%Z) //.
      by apply insert_subseteq.
    - rewrite big_sepM2_insert=> //. eauto.
  Qed.

End choice_example.
