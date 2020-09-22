(** This file contains an example of a client for a mapper service
with the type:

  μ rec. ? (X,Y:★) (X ⊸ Y). ?X. !Y. rec

It shows increasingly complicating uses of the service,
employing swapping and polymorphism to send multiple function
and values of different types, before requesting the results.
 *)
From actris.logrel Require Import term_typing_rules session_typing_rules.
From actris.channel Require Import proofmode.

Section mapper_example.
  Context `{heapG Σ, chanG Σ}.

  (** Client type as dual of service type *)
  Definition mapper_client_type_aux (rec : lsty Σ) : lsty Σ :=
    <!!> TY (lty_int ⊸ lty_bool); <!!> TY lty_int; <??> TY lty_bool; rec.
  Definition mapper_client_type : lsty Σ :=
    mapper_client_type_aux END.
  Instance mapper_client_type_contractive : Contractive mapper_client_type_aux.
  Proof. solve_proto_contractive. Qed.
  Definition mapper_client_rec_type : lsty Σ :=
    lty_rec mapper_client_type_aux.

  (** Client that uses the service once *)
  Definition mapper_client : expr := λ: "c",
    send "c" (λ: "x", #9000 < "x");;
    send "c" #42;;
    recv "c".

  Lemma mapper_client_typed Γ :
    ⊢ Γ ⊨ mapper_client : lty_chan (mapper_client_type) ⊸ lty_bool.
  Proof.
    iApply (ltyped_frame _ [] []).
    iApply (ltyped_lam []); simpl.
    iApply ltyped_post_nil. iApply ltyped_let.
    { iApply ltyped_send; last first.
      { iApply (ltyped_lam []); simpl. iApply ltyped_post_nil.
        iApply ltyped_bin_op; [by iApply ltyped_var|]. by iApply ltyped_int. }
      done. }
    iApply ltyped_let.
    { by iApply ltyped_send; [|by iApply ltyped_int]. }
    by iApply ltyped_recv.
  Qed.

  (** Client that uses the service twice, using recursion and swapping *)
  Definition mapper_client_type_swap (rec : lsty Σ) : lsty Σ :=
    <!!> TY (lty_int ⊸ lty_bool); <!!> TY lty_int;
    <!!> TY (lty_int ⊸ lty_bool); <!!> TY lty_int;
    <??> TY lty_bool; <??> TY lty_bool; rec.

  Definition mapper_client_twice : expr := λ: "c",
    send "c" (λ: "x", #9000 < "x");; send "c" #42;;
    send "c" (λ: "x", #4500 < "x");; send "c" #20;;
    let: "x" := recv "c" in
    let: "y" := recv "c" in
    ("x","y").

  Lemma mapper_client_twice_typed Γ :
    Γ ⊨ mapper_client_twice :
          lty_chan (mapper_client_rec_type) ⊸ (lty_bool * lty_bool).
  Proof.
    iApply (ltyped_subsumption _ _ _ _ _ _
      ((lty_chan (mapper_client_type_swap mapper_client_rec_type)) ⊸ _)%lty);
      [ iApply ctx_le_refl | | iApply ctx_le_refl | ].
    { iApply lty_le_arr; [ | iApply lty_le_refl ].
      iApply lty_le_chan.
      iApply lty_le_l; [ iApply lty_le_rec_unfold | ].
      iIntros "!>!>!>!>".
      iApply lty_le_trans.
      { iApply lty_le_recv; [ iApply lty_le_refl | ].
        iApply lty_le_l; [ iApply lty_le_rec_unfold | iApply lty_le_refl ]. }
      iApply lty_le_trans; [ iApply lty_le_swap_recv_send | ].
      iIntros "!>".
      iApply lty_le_trans; [ iApply lty_le_swap_recv_send | ].
      iIntros "!>".
      iApply lty_le_refl. }
    iApply (ltyped_lam []).
    iApply ltyped_seq.
    { iApply (ltyped_send _ [CtxItem "c" _]); [ done | ].
      iApply (ltyped_lam []). iApply ltyped_post_nil.
      iApply ltyped_bin_op;
        [ by iApply ltyped_var | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [CtxItem "c" _]); [ done | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [CtxItem "c" _]); [ done | ].
      iApply (ltyped_lam []). iApply ltyped_post_nil.
      iApply ltyped_bin_op;
        [ by iApply ltyped_var | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [CtxItem "c" _]); [ done | iApply ltyped_int ]. }
    iApply ltyped_post_nil.
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_pair; [ by iApply ltyped_var | by iApply ltyped_var ].
  Qed.

  (** Client that also make use of polymorphism, to send
   different types *)
  Definition mapper_client_type_poly_aux (rec : lsty Σ) : lsty Σ :=
    <!! X Y> TY (X ⊸ Y); <!!> TY X; <??> TY Y; rec.
  Instance mapper_client_type_poly_contractive :
    Contractive mapper_client_type_poly_aux.
  Proof. solve_proto_contractive. Qed.
  Definition mapper_client_rec_type_poly : lsty Σ :=
    lty_rec mapper_client_type_poly_aux.

  Definition mapper_client_type_poly_swap (rec : lsty Σ) : lsty Σ :=
    <!!> TY (lty_int ⊸ lty_bool); <!!> TY lty_int;
    <!!> TY (lty_bool ⊸ lty_int); <!!> TY lty_bool;
    <??> TY lty_bool; <??> TY lty_int; rec.

  Definition mapper_client_twice_poly : expr := λ: "c",
    send "c" (λ: "x", #9000 < "x");; send "c" #42;;
    send "c" (λ: "x", if: #true then #1 else #0);; send "c" #true;;
    let: "x" := recv "c" in
    let: "y" := recv "c" in
    ("x","y").

  Lemma mapper_client_twice_poly_typed Γ :
    Γ ⊨ mapper_client_twice_poly :
      lty_chan (mapper_client_rec_type_poly) ⊸ (lty_bool * lty_int) ⫤ Γ.
  Proof.
    iApply (ltyped_subsumption _ _ _ _ _ _
      ((lty_chan (mapper_client_type_poly_swap mapper_client_rec_type_poly))
         ⊸ _)%lty);
      [ iApply ctx_le_refl | | iApply ctx_le_refl | ].
    { iApply lty_le_arr; [ | iApply lty_le_refl ].
      iApply lty_le_chan.
      iApply lty_le_l; [ iApply lty_le_rec_unfold | ].
      iExists lty_int, lty_bool.
      iIntros "!>!>!>!>".
      iApply lty_le_trans.
      { iApply lty_le_recv; [ iApply lty_le_refl | ].
        iApply lty_le_l; [ iApply lty_le_rec_unfold | iApply lty_le_refl ]. }
      iApply lty_le_trans.
      { iIntros "!>". iExists lty_bool, lty_int. iApply lty_le_refl. }
      iApply lty_le_trans; [ iApply lty_le_swap_recv_send | ].
      iIntros "!>".
      iApply lty_le_trans; [ iApply lty_le_swap_recv_send | ].
      iIntros "!>".
      iApply lty_le_refl. }
    iApply (ltyped_lam []).
    iApply ltyped_seq.
    { iApply (ltyped_send _ [CtxItem "c" _]); [ done | ].
      iApply (ltyped_lam []). iApply ltyped_post_nil.
      iApply ltyped_bin_op;
        [ by iApply ltyped_var | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [CtxItem "c" _]); [ done | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [CtxItem "c" _]); [ done | ].
      iApply (ltyped_lam []). iApply ltyped_post_nil.
      iApply ltyped_if;
        [ iApply ltyped_bool | iApply ltyped_int | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [CtxItem "c" _]); [ done | iApply ltyped_bool ]. }
    iApply ltyped_post_nil.
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_pair; [ by iApply ltyped_var | by iApply ltyped_var ].
  Qed.

End mapper_example.
