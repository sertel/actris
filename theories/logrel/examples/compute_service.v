From iris.algebra Require Import frac.
From iris.heap_lang Require Import metatheory.
From actris.utils Require Import llist.
From actris.channel Require Import proofmode proto channel.
From actris.logrel Require Import term_typing_rules session_typing_rules
     subtyping_rules napp.
From actris.logrel.lib Require Import par_start.

Definition cont : Z := 1.
Definition stop : Z := 2.

Definition compute_service : val :=
  rec: "go" "c":=
    branch [cont;stop] "c"
    (λ: "c", let: "v" := recv "c" in
             send "c" ("v" #());; "go" "c")
    (λ: "c", #()).
 
Section compute_example.
  Context `{heapG Σ, chanG Σ, spawnG Σ}.

  Definition compute_type_service_aux (rec : lsty Σ) : lsty Σ :=
    lty_branch $ <[cont := (<?? A> TY () ⊸ A; <!!> TY A ; rec)%lty]> $
                 <[stop := END%lty]> $ ∅.
  Instance mapper_type_rec_service_contractive :
    Contractive (compute_type_service_aux).
  Proof. solve_proto_contractive. Qed.
  Definition compute_type_service : lsty Σ :=
    lty_rec (compute_type_service_aux).

  (** This judgement is checked only with the typing rules of the type system *)
  Lemma ltyped_compute_service Γ :
    ⊢ Γ ⊨ compute_service : lty_chan compute_type_service ⊸ () ⫤ Γ.
  Proof.
    iApply (ltyped_subsumption _ _ _ _ _ _
              (lty_chan compute_type_service → ())%lty);
      [ iApply env_le_refl | iApply lty_le_copy_elim | iApply env_le_refl | ].
    iApply ltyped_val_ltyped.
    iApply ltyped_val_rec.
    iApply ltyped_post_nil.
    iApply ltyped_app.
    { iApply (ltyped_lam []). iApply ltyped_post_nil. iApply ltyped_unit. }
    iApply (ltyped_app _ _ _ _ _
              (chan (<?? A> TY () ⊸ A; <!!> TY A; compute_type_service) ⊸ ())%lty).
    {
      simpl.
      iApply (ltyped_lam [EnvItem "go" _]).
      iApply ltyped_post_nil.
      iApply ltyped_recv_texist; [ done | apply _ | ].
      iIntros (Ys).
      pose proof (ltys_S_inv Ys) as [A [Ys' HYs]].
      pose proof (ltys_O_inv Ys') as HYs'.
      rewrite HYs HYs' /=.
      iApply ltyped_seq.
      { iApply (ltyped_send _ [EnvItem "v" _; EnvItem "c" _; EnvItem "go" _]);
          [ done | ].
        iApply ltyped_app; [ by iApply ltyped_unit | ]=> /=.
        by iApply ltyped_var. }
      simpl.
      iApply ltyped_app; [ by iApply ltyped_var | ].
      simpl. rewrite !(Permutation_swap (EnvItem "go" _)).
      iApply ltyped_subsumption; [ | | iApply env_le_refl | ].
      { iApply env_le_cons; [ iApply lty_le_refl | iApply env_le_nil ]. }
      { iApply lty_le_copy_elim. }
      by iApply ltyped_var. }
    iApply ltyped_app; [ by iApply ltyped_var | ].
    iApply ltyped_subsumption; [ iApply env_le_nil | | iApply env_le_refl | ].
    { iApply lty_le_arr; [ | iApply lty_le_refl ]. iApply lty_le_chan.
      iApply lty_le_l; [ iApply lty_le_rec_unfold | iApply lty_le_refl ]. }
    rewrite /compute_type_service_aux.
    iApply ltyped_branch. intros x. rewrite -elem_of_dom. set_solver.
  Qed.

End compute_example.
