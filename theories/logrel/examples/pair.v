From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import channel proto proofmode.
From actris.logrel Require Export types.

Definition prog : expr := λ: "c", (recv "c", recv "c").

Section pair.
  Context `{heapG Σ, chanG Σ}.

  Lemma prog_typed :
    ⊢ ∅ ⊨ prog : chan (<??> lty_int; <??> lty_int; END) ⊸ lty_int * lty_int.
  Proof.
    rewrite /prog.
    iApply ltyped_lam. iApply ltyped_pair.
    iApply ltyped_recv. iApply ltyped_recv.
  Qed.

End pair.
