From actris.channel Require Import proofmode proto channel.
From actris.logrel Require Import subtyping_rules.
From iris.proofmode Require Import tactics.

Section choice_example.
  Context `{heapG Σ, chanG Σ}.

  Variables R M P Q S U : ltty Σ.

  (**
  ?R. ((!M._) <+> (!P._) <+> (!Q._))
  <&>
  ?S. ((!M._) <+> (!P._))
   *)
  Definition prot_sub : lsty Σ :=
    (lty_branch
       (<[1%Z:= <??> TY R ;
         lty_select
           (<[1%Z:= <!!> TY M ; END]>
            (<[2%Z:= <!!> TY P ; END]>
             (<[3%Z:= <!!> TY Q ; END]>∅)))]>
        (<[2%Z:= <??> TY S ;
          lty_select
            (<[1%Z := <!!> TY M ; END]>
             (<[2%Z := <!!> TY P; END]>∅))]>∅)))%lty.


  (**
  !M.((?R._) <&> (?S._) <&> (?U._))
  <+>
  !P.((?R._) <&> (?S._))
   *)
  Definition prot_sup : lsty Σ :=
    (lty_select
       (<[1%Z:= <!!> TY M ; lty_branch
                              (<[1%Z:= <??> TY R ; END]>
                               (<[2%Z:= <??> TY S ; END]>
                               (<[3%Z:= <??> TY U ; END]>∅)))]>
        (<[2%Z:= <!!> TY P ; lty_branch
                               (<[1%Z := <??> TY R ; END]>
                                (<[2%Z := <??> TY S; END]>∅))]>∅)))%lty.

  (**
  Weaken select
  ?R.((!M._) <+> (!P._))
  <&>
  ?S.((!M._) <+> (!P._))
  *)
  Definition prot1 : lsty Σ :=
    (lty_branch
       (<[1%Z:= <??> TY R ;
         lty_select
           (<[1%Z:= <!!> TY M ; END]>
            (<[2%Z:= <!!> TY P ; END]>∅))]>
        (<[2%Z:= <??> TY S ;
          lty_select
            (<[1%Z := <!!> TY M ; END]>
             (<[2%Z := <!!> TY P; END]>∅))]>∅)))%lty.

  (**
  Swap recv/select
  ((?R.!M._) <+> (?R.!P._))
  <&>
  ((?S.!M._) <+> (?S.!P._))
  *)
  Definition prot2 : lsty Σ :=
    (lty_branch
       (<[1%Z:= lty_select
                  (<[1%Z:= <??> TY R ; <!!> TY M ; END]>
                   (<[2%Z:= <??> TY R ; <!!> TY P ; END]>∅))]>
        (<[2%Z:= lty_select
                   (<[1%Z := <??> TY S ; <!!> TY M ; END]>
                    (<[2%Z := <??> TY S ; <!!> TY P; END]>∅))]>∅)))%lty.

  (**
  swap branch/select
  ((?R.!M._) <&> (?S.!M._))
  <+>
  ((?R.!P._) <&> (?S.!P._))
  *)
  Definition prot3 : lsty Σ :=
    (lty_select
       (<[1%Z:= lty_branch
                  (<[1%Z:= <??> TY R ; <!!> TY M ; END]>
                   (<[2%Z:= <??> TY S ; <!!> TY M ; END]>∅))]>
        (<[2%Z:= lty_branch
                   (<[1%Z := <??> TY R ; <!!> TY P ; END]>
                    (<[2%Z := <??> TY S ; <!!> TY P; END]>∅))]>∅)))%lty.

  (**
  swap recv/send
  ((!M.?R._) <&> (!M.?S._))
  <+>
  ((!P.?R._) <&> (!P.?S._))
  *)
  Definition prot4 : lsty Σ :=
    (lty_select
       (<[1%Z:= lty_branch
                  (<[1%Z:= <!!> TY M ; <??> TY R ; END]>
                   (<[2%Z:= <!!> TY M ; <??> TY S ; END]>∅))]>
        (<[2%Z:= lty_branch
                   (<[1%Z := <!!> TY P ; <??> TY R ; END]>
                    (<[2%Z := <!!> TY P; <??> TY S ; END]>∅))]>∅)))%lty.

  (**
  Swap branch/send
  !M.((?R._) <&> (?S._))
  <+>
  !P.((?R._) <&> (?S._))
  *)
  Definition prot5 : lsty Σ :=
    (lty_select
       (<[1%Z:= <!!> TY M ;
         lty_branch (<[1%Z:= <??> TY R ; END]>
                     (<[2%Z:= <??> TY S ; END]>∅))]>
        (<[2%Z:= <!!> TY P ;
          lty_branch
            (<[1%Z := <??> TY R ; END]>
             (<[2%Z := <??> TY S ; END]>∅))]>∅)))%lty.

  Lemma subtype_proof :
    ⊢ prot_sub <: prot_sup.
  Proof.
    (** Weakening of select *)
    iApply (lty_le_trans _ prot1).
    {
      iApply lty_le_branch. iIntros "!>".
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
      iApply lty_le_branch. iIntros "!>".
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
                     <[1%Z:=(<??> TY R; <!!> TY M; END)%lty]>
                     (<[2%Z:= (<??> TY R; <!!> TY P; END)%lty]>∅)]>
                 (<[2%Z:=
                     <[1%Z:=(<??> TY S; <!!> TY M; END)%lty]>
                     (<[2%Z:= (<??> TY S; <!!> TY P; END)%lty]>∅)]>∅))
                (<[1%Z:=
                     <[1%Z:=(<??> TY R; <!!> TY M; END)%lty]>
                     (<[2%Z:= (<??> TY S; <!!> TY M; END)%lty]>∅)]>
                 (<[2%Z:=
                     <[1%Z:=(<??> TY R; <!!> TY P; END)%lty]>
                     (<[2%Z:= (<??> TY S; <!!> TY P; END)%lty]>∅)]>∅))
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
      iApply lty_le_select. iIntros "!>".
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
    (** Swap branch/send *)
    iApply (lty_le_trans _ prot5).
    {
      iApply lty_le_select. iIntros "!>".
      rewrite big_sepM2_insert=> //. iSplit.
      - iApply (lty_le_swap_branch_send _
          (<[1%Z:=(<??> TY R; END)%lty]> (<[2%Z:=(<??> TY S; END)%lty]> ∅))).
      - rewrite big_sepM2_insert=> //. iSplit=> //.
        iApply (lty_le_swap_branch_send _
          ((<[1%Z:=(<??> TY R; END)%lty]> (<[2%Z:=(<??> TY S; END)%lty]> ∅)))).
    }
    (** Weaken branch *)
    iApply lty_le_select. iIntros "!>".
    rewrite big_sepM2_insert=> //. iSplit=> //.
    - iApply lty_le_send; [iApply lty_le_refl|].
      iApply lty_le_branch_subseteq.
      rewrite (insert_commute _ 2%Z 3%Z) //.
      rewrite (insert_commute _ 1%Z 3%Z) //.
      by apply insert_subseteq.
    - rewrite big_sepM2_insert=> //. eauto.
  Qed.

End choice_example.
