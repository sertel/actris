From actris.logrel Require Export term_typing_rules session_typing_rules.
From actris.channel Require Import proofmode.

Definition par_start : expr := λ: "e1" "e2",
  let: "c" := new_chan #() in
  let: "c1" := Fst "c" in
  let: "c2" := Snd "c" in
  ("e1" "c1") ||| ("e2" "c2").

Lemma ltyped_par_start `{!heapG Σ, !chanG Σ, !spawnG Σ} Γ S A B :
  ⊢ Γ ⊨ par_start : (chan S ⊸ A) ⊸ (chan (lty_dual S) ⊸ B) ⊸ A * B.
Proof.
  iApply (ltyped_lam []); iApply (ltyped_lam [EnvItem "e1" _] [] "e2"); simpl.
  iApply ltyped_post_nil. iApply ltyped_let.
  { iApply ltyped_app; [iApply ltyped_unit|iApply (ltyped_new_chan _ S)]. }
  iApply ltyped_let; [by iApply ltyped_fst|]; simpl.
  iApply ltyped_let; [by iApply ltyped_snd|]; simpl.
  rewrite !(Permutation_swap (EnvItem "c1" _))
    !(Permutation_swap (EnvItem "e1" _)).
  iApply (ltyped_par [EnvItem "e1" _; EnvItem "c1" _]).
  - iApply ltyped_app; by iApply ltyped_var.
  - iApply ltyped_app; by iApply ltyped_var.
Qed.
