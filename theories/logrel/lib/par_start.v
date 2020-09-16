From actris.logrel Require Export term_typing_rules environments.
From actris.channel Require Import proofmode.

Section properties.
  Context `{heapG Σ}.
  Context `{chanG Σ}.
  Context `{spawnG Σ}.

  Definition par_start : expr :=
    (λ: "e1" "e2",
     let: "c" := new_chan #() in
     let: "c1" := Fst "c" in
     let: "c2" := Snd "c" in
     ("e1" "c1") ||| ("e2" "c2"))%E.

  Lemma ltyped_par_start Γ S A B :
    ⊢ Γ ⊨ par_start : ((chan S) ⊸ A) ⊸ (chan (lty_dual S) ⊸ B) ⊸ A * B.
  Proof.
    iApply ltyped_lam; [ iApply env_split_id_l | ].
    iApply ltyped_lam; [ iApply env_split_id_r | ].
    iApply ltyped_let.
    { iApply ltyped_app; [ iApply ltyped_unit | iApply ltyped_new_chan ]. }
    iApply ltyped_let; [ by iApply ltyped_fst | ].
    rewrite insert_insert.
    iApply ltyped_let; [ by iApply ltyped_snd | ].
    rewrite /binder_insert (insert_commute _ "c1" "c") // insert_insert.
    iApply (ltyped_par).
    - iApply env_split_right; last first.
      { rewrite (insert_commute _ "c1" "e2"); [ | eauto ].
        rewrite (insert_commute _ "c" "e2"); [ | eauto ].
        iApply env_split_right; last by iApply env_split_id_r.
        eauto. eauto. }
      eauto. eauto.
    - iApply ltyped_app; by iApply ltyped_var.
    - iApply ltyped_app; by iApply ltyped_var.
    - rewrite insert_insert.
      rewrite (insert_commute _ "c2" "e2") // insert_insert.
      rewrite (insert_commute _ "c1" "c") // insert_insert.
      rewrite (insert_commute _ "c1" "e1") //
              (insert_commute _ "c" "e1") // insert_insert.
      iApply env_split_left=> //; last first.
      iApply env_split_left=> //; last first.
      iApply env_split_left=> //; last first.
      iApply env_split_id_l.
      eauto. eauto. eauto.
  Qed.

End properties.
