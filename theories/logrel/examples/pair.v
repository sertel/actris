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
    iApply ltyped_recv. iApply ltyped_recv.
  Qed.
End pair.
