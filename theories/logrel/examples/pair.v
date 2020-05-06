(** This file contains shows that the program

  λ c, (recv c, recv c)

can be assigned the type

  chan (?int.?int.end) ⊸ (int * int)

by exclusively using the semantic typing rules. *)
From actris.logrel Require Export term_typing_rules.
From iris.proofmode Require Import tactics.

Definition prog : expr := λ: "c", (recv "c", recv "c").

Section pair.
  Context `{heapG Σ, chanG Σ}.

  Lemma prog_typed :
    ⊢ ∅ ⊨ prog : chan (<??> TY lty_int; <??> TY lty_int; END) ⊸ lty_int * lty_int.
  Proof.
    rewrite /prog.
    iApply ltyped_lam. iApply ltyped_pair.
    iApply ltyped_recv.
    2:{ iApply ltyped_recv. by rewrite /binder_insert lookup_insert. }
    by rewrite lookup_insert.
  Qed.
End pair.
