From iris.heap_lang Require Import adequacy.
From iris.heap_lang.lib Require Import assert.
From multi_actris.channel Require Import proofmode.

Notation A := 0.
Notation B := 1.
Notation C := 2.
Notation D := 3.

Definition program : val :=
  λ: <>,
     let: "cs" := new_chan #4 in
     let: "ch0" := get_chan "cs" #A in
     let: "ch1" := get_chan "cs" #B in
     let: "ch2" := get_chan "cs" #C in
     let: "ch3" := get_chan "cs" #D in
     (* A *)
     Fork (let: "a" := #42 in
           let: "a1" := #10 in
           let: "a2" := #20 in
           let: "a3" := #12 in
           (* (<(Send,B) @ (a2:Z)> MSG #a2 ; <(Send,C) @ (a3:Z)> MSG #a3 ; *)
           send "ch0" #B "a2";;
           send "ch0" #C "a3";;
           (* <(Recv,B) @ (b1:Z)> MSG #b1 ; <(Recv,C) @ (c1:Z)> MSG #c1 ; *)
           let: "b1" := recv "ch0" #B in
           let: "c1" := recv "ch0" #C in
           (* <(Send,B) @ (s1:Z) (a1:Z)> MSG #s1 {{ ⌜(s1 = a1 + b1 + c1)%Z⌝ }} ; *)
           let: "s1" := "a1"+"b1"+"c1" in
           send "ch0" #B "s1";;
           (* <(Send,C)> MSG #s1 ; *)
           send "ch0" #C "s1";;
           (* <(Recv,B) @ (s2:Z)> MSG #s2 ; <(Recv,C) @ (s3:Z)> MSG #s3; *)
           let: "s2" := recv "ch0" #B in
           let: "s3" := recv "ch0" #C in
           send "ch0" #D ("s1"+"s2"+"s3"));;
     (* B *)
     Fork (let: "b" := #100 in
           let: "b1" := #20 in
           let: "b2" := #30 in
           let: "b3" := #50 in
           (* <(Recv,A) @ (a2:Z)> MSG #a2 ; <(Send,A) @ (b1:Z)> MSG #b1 ; *)     
           let: "a2" := recv "ch1" #A in
           send "ch1" #A "b1";;
           (* <(Send,C) @ (b3:Z)> MSG #b3 ; <(Recv,C) @ (c2:Z)> MSG #c2 ; *)
           send "ch1" #C "b3";;
           let: "c2" := recv "ch1" #C in
           (* <(Recv,A) @ (s1:Z)> MSG #s1 ; *)
           let: "s1" := recv "ch1" #A in
           (* <(Send,A) @ (s2:Z) (b2:Z)> MSG #s2 {{ ⌜(s2 = a2 + b2 + c2)%Z⌝ }} ; *)
           let: "s2" := "a2"+"b2"+"c2" in
           send "ch1" #A "s2";;
           (* <(Send,C)> MSG #s2 ; <(Recv,C) @ (s3:Z)> MSG #s3 ; *)
           send "ch1" #C "s2";;
           let: "s3" := recv "ch1" #C in
           send "ch1" #D ("s1"+"s2"+"s3"));;
     Fork (let: "c" := #7 in
           let: "c1" := #1 in
           let: "c2" := #2 in
           let: "c3" := #4 in
           (* <(Recv,A) @ (a3:Z)> MSG #a3 ; <(Send,A) @ (c1:Z)> MSG #c1 ; *)
           let: "a3" := recv "ch2" #A in
           send "ch2" #A "c1";;
           (* <(Recv,B) @ (b3:Z)> MSG #b3 ; <(Send,B) @ (c2:Z)> MSG #c2 ; *)
           let: "b3" := recv "ch2" #B in
           send "ch2" #B "c2";;
           (* <(Recv,A) @ (s1:Z)> MSG #s1 ; *)
           let: "s1" := recv "ch2" #A in
           (* <(Send,A) @ (s3:Z) (c3:Z)> MSG #s3 {{ ⌜(s3 = a3 + b3 + c3)%Z⌝ }} ; *)
           let: "s3" := "a3"+"b3"+"c3" in
           send "ch2" #A "s3";;
           (* <(Recv,B) @ (s2:Z)> MSG #s2 ; <(Send,B)> MSG #s3; *)
           let: "s2" := recv "ch2" #B in
           send "ch2" #B "s3";;
           send "ch2" #D ("s1"+"s2"+"s3"));;
     let: "res1" := recv "ch3" #A in
     let: "res2" := recv "ch3" #B in
     let: "res3" := recv "ch3" #C in
     assert: ("res1" = "res2");;
     assert: ("res2" = "res3").

Section mpc_protocols.
  Context `{!heapGS Σ, chanG Σ}.

  Definition A_prot (p : Z → iProto Σ) : iProto Σ :=
    (<(Send,B) @ (a2:Z)> MSG #a2 ; <(Send,C) @ (a3:Z)> MSG #a3 ;
     <(Recv,B) @ (b1:Z)> MSG #b1 ; <(Recv,C) @ (c1:Z)> MSG #c1 ;
     <(Send,B) @ (s1:Z) (a1:Z)> MSG #s1 {{ ⌜(s1 = a1 + b1 + c1)%Z⌝ }} ;
     <(Send,C)> MSG #s1 ;
     <(Recv,B) @ (s2:Z)> MSG #s2 ; <(Recv,C) @ (s3:Z)> MSG #s3;
     p (s1 + s2 + s3)%Z)%proto.

  Definition B_prot (p : Z → iProto Σ) : iProto Σ :=
    (<(Recv,A) @ (a2:Z)> MSG #a2 ; <(Send,A) @ (b1:Z)> MSG #b1 ;
     <(Send,C) @ (b3:Z)> MSG #b3 ; <(Recv,C) @ (c2:Z)> MSG #c2 ;
     <(Recv,A) @ (s1:Z)> MSG #s1 ;
     <(Send,A) @ (s2:Z) (b2:Z)> MSG #s2 {{ ⌜(s2 = a2 + b2 + c2)%Z⌝ }} ;
     <(Send,C)> MSG #s2 ; <(Recv,C) @ (s3:Z)> MSG #s3 ;
     p (s1 + s2 + s3)%Z)%proto.

  Definition C_prot (p : Z → iProto Σ) : iProto Σ :=
    (<(Recv,A) @ (a3:Z)> MSG #a3 ; <(Send,A) @ (c1:Z)> MSG #c1 ;
     <(Recv,B) @ (b3:Z)> MSG #b3 ; <(Send,B) @ (c2:Z)> MSG #c2 ;
     <(Recv,A) @ (s1:Z)> MSG #s1 ;
     <(Send,A) @ (s3:Z) (c3:Z)> MSG #s3 {{ ⌜(s3 = a3 + b3 + c3)%Z⌝ }} ;
     <(Recv,B) @ (s2:Z)> MSG #s2 ; <(Send,B)> MSG #s3;
     p (s1 + s2 + s3)%Z)%proto.

  Definition D_prot : iProto Σ :=
    (<(Recv,A) @ (sum : Z)> MSG #sum ;
     <(Recv,B)> MSG #sum;
     <(Recv,C)> MSG #sum; END)%proto.

  Definition tail_prot (sum : Z) : iProto Σ :=
     (<(Send,D)> MSG #sum ; END)%proto.

  Definition mpc_prot_pool : list (iProto Σ) :=
     [A_prot tail_prot; B_prot tail_prot; C_prot tail_prot; D_prot].

  Lemma mpc_consistent :
    ⊢ iProto_consistent mpc_prot_pool.
  Proof. rewrite /mpc_prot_pool. iProto_consistent_take_steps. Qed.

  (* TODO: Clean up and move to proofmode.v? *)
  Tactic Notation "wp_recv" := try wp_recv (?) as "_"; try wp_recv as "_".
  Tactic Notation "wp_send" := wp_send with "[//]".
  Tactic Notation "wp_chan_pures" := repeat (repeat wp_send; repeat wp_recv).

  Lemma mpc_spec :
    {{{ True }}} program #() {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_new_chan mpc_prot_pool with mpc_consistent
      as (ch0 ch1 ch2 ch3) "Hc0" "Hc1" "Hc2" "Hc3".
    wp_smart_apply (wp_fork with "[Hc0]").
    { iIntros "!>". by wp_chan_pures. }
    wp_smart_apply (wp_fork with "[Hc1]").
    { iIntros "!>". by wp_chan_pures. }
    wp_smart_apply (wp_fork with "[Hc2]").
    { iIntros "!>". by wp_chan_pures. }
    wp_chan_pures. wp_smart_apply wp_assert. wp_pures.
    iSplitR; [by case_bool_decide|]. iIntros "!>!>".
    wp_smart_apply wp_assert. wp_pures.
    iSplitR; [by case_bool_decide|]. iIntros "!>!>".
    by iApply "HΦ".
  Qed.

End mpc_protocols.
