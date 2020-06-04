From actris.channel Require Import proofmode proto channel.
From actris.logrel Require Import subtyping_rules term_typing_judgment term_typing_rules environments.
From iris.proofmode Require Import tactics.

Section with_Σ.
  Context `{heapG Σ, chanG Σ}.

  Definition mapper_service_type : lsty Σ :=
    <??> TY (lty_int ⊸ lty_bool); <??> TY lty_int; <!!> TY lty_bool; END.

  Definition mapper_service : expr := λ: "c",
    let: "f" := recv "c" in
    let: "v" := recv "c" in
    send "c" ("f" "v");; "c".

  Lemma mapper_typed :
    ⊢ ∅ ⊨ mapper_service : (lty_chan (mapper_service_type) ⊸ (lty_chan END))%lty ⫤ ∅.
  Proof.
    iApply ltyped_lam.
    iApply ltyped_let.
    { iApply ltyped_recv. by rewrite lookup_insert. }
    rewrite insert_insert /=.
    iApply ltyped_let.
    { iApply ltyped_recv. by rewrite insert_commute // lookup_insert. }
    rewrite (insert_commute _ "c" "f") // insert_insert.
    iApply (ltyped_let _ (<["c":= lty_chan END]>_))=> /=; last first.
    { iApply ltyped_var. apply lookup_insert. }
    rewrite (insert_commute _ "f" "c") // (insert_commute _ "v" "c") //.
    iApply ltyped_send. apply lookup_insert.
    iApply (ltyped_frame _ _ _ _ {["c":=_]}).
    { iApply env_split_right=> //. iApply env_split_id_r. }
    { iApply env_split_right=> //. shelve. iApply env_split_id_r. }
    iApply ltyped_app.
    - iApply ltyped_var. apply lookup_insert.
    - rewrite insert_commute //.
      iApply (ltyped_frame _ _ _ _ {["f":=_]}).
      { iApply env_split_right=> //. iApply env_split_id_r. }
      { iApply env_split_right=> //. shelve. iApply env_split_id_r. }
      iApply ltyped_var. apply lookup_insert.
      Unshelve. eauto. eauto.
  Qed.

End with_Σ.
