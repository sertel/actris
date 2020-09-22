(** This file contains shows that the program

  λ c, (recv c, recv c)

can be assigned the type

  chan (?int.?int.end) ⊸ (int * int)

by exclusively using the semantic typing rules. *)
From actris.logrel Require Export term_typing_rules session_typing_rules.
From iris.proofmode Require Import tactics.

Definition prog : expr := λ: "c", (recv "c", recv "c").

Lemma prog_typed `{heapG Σ, chanG Σ} :
  [] ⊨ prog : chan (<??> TY lty_int; <??> TY lty_int; END) ⊸ lty_int * lty_int.
Proof.
  iApply (ltyped_lam []); simpl. iApply ltyped_post_nil.
  iApply ltyped_pair; [by iApply ltyped_recv|by iApply ltyped_recv].
Qed.
