From actris.channel Require Import proofmode proto channel.
From actris.logrel Require Import subtyping_rules term_typing_judgment term_typing_rules environments operators.
From iris.proofmode Require Import tactics.

Section with_Σ.
  Context `{heapG Σ, chanG Σ}.

  Definition mapper_client_type_aux (rec : lsty Σ) : lsty Σ :=
    <!!> TY (lty_int ⊸ lty_bool); <!!> TY lty_int; <??> TY lty_bool; rec.
  Definition mapper_client_type : lsty Σ :=
    mapper_client_type_aux END.

  Instance mapper_client_type_contractive : Contractive mapper_client_type_aux.
  Proof. solve_proto_contractive. Qed.

  Definition mapper_client_rec_type : lsty Σ :=
    lty_rec mapper_client_type_aux.

  Definition mapper_service_type : lsty Σ :=
    <??> TY (lty_int ⊸ lty_bool); <??> TY lty_int; <!!> TY lty_bool; END.

  Definition mapper_client : expr := λ: "c",
    send "c" (λ: "x", #9000 < "x");;
    send "c" #42;; recv "c".

  Definition mapper_service : expr := λ: "c",
    let: "f" := recv "c" in
    let: "v" := recv "c" in
    send "c" ("f" "v");; "c".

  Lemma mapper_client_typed Γ :
    ⊢ Γ ⊨ mapper_client : (lty_chan (mapper_client_type) ⊸ lty_bool)%lty ⫤ Γ.
  Proof.
    iApply (ltyped_frame _ _ _ _ Γ).
    { iApply env_split_id_l. }
    2: { iApply env_split_id_l. }
    iApply ltyped_lam.
    iApply ltyped_let.
    { iApply ltyped_send. apply lookup_insert.
      iApply (ltyped_frame _ _ _ _ {["c":=_]}).
      { iApply env_split_id_l. }
      { iApply ltyped_lam. iApply ltyped_bin_op.
        - iApply ltyped_var. apply lookup_insert.
        - iApply ltyped_int. }
      { iApply env_split_id_l. } }
    rewrite insert_insert /=.
    iApply ltyped_let.
    { iApply ltyped_send. apply lookup_insert.
      iApply ltyped_int. }
    rewrite insert_insert /=. iApply ltyped_recv. apply lookup_insert.
  Qed.

  Lemma mapper_service_typed Γ :
    ⊢ Γ ⊨ mapper_service : (lty_chan (mapper_service_type) ⊸ (lty_chan END))%lty ⫤ Γ.
  Proof.
    iApply (ltyped_frame _ _ _ _ Γ).
    { iApply env_split_id_l. }
    2: { iApply env_split_id_l. }
    iApply ltyped_lam.
    iApply ltyped_let.
    { iApply ltyped_recv. by rewrite lookup_insert. }
    rewrite insert_insert /=.
    iApply ltyped_let.
    { iApply ltyped_recv. by rewrite insert_commute // lookup_insert. }
    rewrite (insert_commute _ "c" "f") // insert_insert.
    iApply ltyped_let=> /=; last first.
    { iApply ltyped_var. apply lookup_insert. }
    iApply ltyped_send. apply lookup_insert.
    rewrite (insert_commute _ "f" "c") // (insert_commute _ "v" "c") //.
    iApply (ltyped_frame _ _ _ _ {["c":=_]}).
    { iApply env_split_right=> //. iApply env_split_id_r. }
    { iApply ltyped_app.
      - iApply ltyped_var. apply lookup_insert.
      - rewrite insert_commute //.
        iApply (ltyped_frame _ _ _ _ {["f":=_]}).
        { iApply env_split_right=> //. iApply env_split_id_r. }
        { iApply ltyped_var. apply lookup_insert. }
        { iApply env_split_right=> //; last by iApply env_split_id_r. eauto. }
    }
    { iApply env_split_right=> //; last by iApply env_split_id_r. eauto. }
  Qed.

  Lemma lty_le_rec_unfold_l {k} (C : lty Σ k → lty Σ k) `{!Contractive C} :
    ⊢ lty_rec C <: C (lty_rec C).
  Proof. iApply lty_le_l. iApply lty_le_rec_unfold. iApply lty_le_refl. Qed.

  Definition mapper_client_type_swap (rec : lsty Σ) : lsty Σ :=
    <!!> TY (lty_int ⊸ lty_bool); <!!> TY lty_int;
    <!!> TY (lty_int ⊸ lty_bool); <!!> TY lty_int;
    <??> TY lty_bool; <??> TY lty_bool; rec.

  Definition mapper_client_rec : expr := λ: "c",
    send "c" (λ: "x", #9000 < "x");; send "c" #42;;
    send "c" (λ: "x", #4500 < "x");; send "c" #20;;
    let: "x" := recv "c" in
    let: "y" := recv "c" in
    ("x","y").

  Lemma mapper_client_rec_typed Γ :
    ⊢ Γ ⊨ mapper_client_rec :
      (lty_chan (mapper_client_rec_type) ⊸ (lty_bool * lty_bool))%lty ⫤ Γ.
  Proof.
    iApply (ltyped_frame _ _ _ _ Γ).
    { iApply env_split_id_l. }
    2: { iApply env_split_id_l. }
    iApply (ltyped_subsumption _ _ _((lty_chan (mapper_client_type_swap mapper_client_rec_type)) ⊸ _)).
    { iApply lty_le_arr.
      - iNext. iApply lty_le_chan. iNext.
        iApply lty_le_trans. iApply lty_le_rec_unfold_l.
        iModIntro. iModIntro.
        iApply lty_le_trans.
        { iModIntro. iApply lty_le_rec_unfold_l. }
        iApply lty_le_trans. iApply lty_le_swap_recv_send. iModIntro.
        iApply lty_le_trans. iApply lty_le_swap_recv_send. iModIntro.
        iModIntro. iModIntro. iApply lty_le_refl.
      - iApply lty_le_refl. }
    iApply ltyped_lam.
    iApply ltyped_let.
    { iApply ltyped_send. apply lookup_insert.
      iApply (ltyped_frame _ _ _ _ {["c":=_]}).
      { iApply env_split_id_l. }
      { iApply ltyped_lam. iApply ltyped_bin_op.
        - iApply ltyped_var. apply lookup_insert.
        - iApply ltyped_int. }
      { iApply env_split_id_l. } }
    rewrite insert_insert /=.
    iApply ltyped_let.
    { iApply ltyped_send. apply lookup_insert.
      iApply ltyped_int. }
    rewrite insert_insert /=.
    iApply ltyped_let.
    { iApply ltyped_send. apply lookup_insert.
      iApply (ltyped_frame _ _ _ _ (<["c":=_]>∅)).
      { iApply env_split_id_l. }
      { iApply ltyped_lam. iApply ltyped_bin_op.
        - iApply ltyped_var. apply lookup_insert.
        - iApply ltyped_int. }
      { iApply env_split_id_l. } }
    rewrite insert_insert /=.
    iApply ltyped_let.
    { iApply ltyped_send. apply lookup_insert.
      iApply ltyped_int. }
    rewrite insert_insert /=.
    iApply ltyped_let.
    { iApply ltyped_recv. apply lookup_insert. }
    rewrite insert_insert /=.
    iApply ltyped_let.
    { iApply ltyped_recv=> //. }
    iApply ltyped_pair.
    - iApply ltyped_var. apply lookup_insert.
    - rewrite (insert_commute _ "c" "x") //= (insert_commute _ "y" "x") //=.
      rewrite insert_insert.
      iApply (ltyped_frame _ _ _ _ {["x":=_]}).
      { iApply env_split_right=> //=. iApply env_split_id_r. }
      iApply ltyped_var. apply lookup_insert.
      iApply env_split_right=> //; last by iApply env_split_id_r=> //=. eauto.
  Qed.

End with_Σ.
