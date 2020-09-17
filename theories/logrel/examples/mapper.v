From actris.logrel Require Import term_typing_rules session_typing_rules.
From actris.channel Require Import proofmode.

Section mapper_example.
  Context `{heapG Σ, chanG Σ}.

  (** Client typing *)
  Definition mapper_client_type_aux (rec : lsty Σ) : lsty Σ :=
    <!!> TY (lty_int ⊸ lty_bool); <!!> TY lty_int; <??> TY lty_bool; rec.
  Definition mapper_client_type : lsty Σ :=
    mapper_client_type_aux END.
  Instance mapper_client_type_contractive : Contractive mapper_client_type_aux.
  Proof. solve_proto_contractive. Qed.
  Definition mapper_client_rec_type : lsty Σ :=
    lty_rec mapper_client_type_aux.

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

  (** Recursion and Swapping *)
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
    ⊢ Γ ⊨ mapper_client_twice :
          lty_chan (mapper_client_rec_type) ⊸ (lty_bool * lty_bool).
  Proof.
    iApply (ltyped_subsumption _ _ _ _ _ _
      ((lty_chan (mapper_client_type_swap mapper_client_rec_type)) ⊸ _)%lty);
      [ iApply env_le_refl | | iApply env_le_refl | ].
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
    { iApply (ltyped_send _ [EnvItem "c" _]); [ done | ].
      iApply (ltyped_lam []). iApply ltyped_post_nil.
      iApply ltyped_bin_op;
        [ by iApply ltyped_var | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [EnvItem "c" _]); [ done | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [EnvItem "c" _]); [ done | ].
      iApply (ltyped_lam []). iApply ltyped_post_nil.
      iApply ltyped_bin_op;
        [ by iApply ltyped_var | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [EnvItem "c" _]); [ done | iApply ltyped_int ]. }
    iApply ltyped_post_nil.
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_pair; [ by iApply ltyped_var | by iApply ltyped_var ].
  Qed.

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
    ⊢ Γ ⊨ mapper_client_twice_poly :
      (lty_chan (mapper_client_rec_type_poly) ⊸ (lty_bool * lty_int))%lty ⫤ Γ.
  Proof.
    iApply (ltyped_subsumption _ _ _ _ _ _
      ((lty_chan (mapper_client_type_poly_swap mapper_client_rec_type_poly))
         ⊸ _)%lty);
      [ iApply env_le_refl | | iApply env_le_refl | ].
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
    { iApply (ltyped_send _ [EnvItem "c" _]); [ done | ].
      iApply (ltyped_lam []). iApply ltyped_post_nil.
      iApply ltyped_bin_op;
        [ by iApply ltyped_var | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [EnvItem "c" _]); [ done | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [EnvItem "c" _]); [ done | ].
      iApply (ltyped_lam []). iApply ltyped_post_nil.
      iApply ltyped_if;
        [ iApply ltyped_bool | iApply ltyped_int | iApply ltyped_int ]. }
    iApply ltyped_seq.
    { iApply (ltyped_send _ [EnvItem "c" _]); [ done | iApply ltyped_bool ]. }
    iApply ltyped_post_nil.
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_pair; [ by iApply ltyped_var | by iApply ltyped_var ].
  Qed.

  (** Service typing *)
  Definition mapper_service_type : lsty Σ :=
    <??> TY (lty_int ⊸ lty_bool); <??> TY lty_int; <!!> TY lty_bool; END.

  Definition mapper_service : expr := λ: "c",
    let: "f" := recv "c" in
    let: "v" := recv "c" in
    send "c" ("f" "v");; "c".

  Lemma mapper_service_typed Γ :
    ⊢ Γ ⊨ mapper_service : (lty_chan (mapper_service_type) ⊸ (lty_chan END))%lty ⫤ Γ.
  Proof.
    iApply (ltyped_lam []). iApply ltyped_post_nil.
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_let; [ by iApply ltyped_recv | ].
    iApply ltyped_seq.
    { iApply (ltyped_send _ [EnvItem "f" _; EnvItem "v" _; EnvItem "c" _]);
        [ done | ].
      iApply ltyped_app; [ by iApply ltyped_var | ]=> /=.
      rewrite !(Permutation_swap (EnvItem "f" _)).
      by iApply ltyped_var. }
    by iApply ltyped_var.
  Qed.

End mapper_example.
