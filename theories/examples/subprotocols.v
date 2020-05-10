From actris.channel Require Import proofmode proto channel.
From actris.logrel Require Import subtyping_rules.
From iris.proofmode Require Import tactics.

Section basics.
  Context `{heapG Σ, chanG Σ}.

  Lemma reference_example (l2' : loc) :
    l2' ↦ #22 -∗
    (<! (l1 l2 : loc)> MSG (#l1, #l2) {{ l1 ↦ #20 ∗ l2 ↦ #22 }}; END)%proto ⊑
    (<! (l1 : loc)> MSG (#l1, #l2') {{ l1 ↦ #20 }}; END)%proto.
  Proof. iIntros "Hl2'" (l1) "Hl1". iExists l1, l2'. by iFrame "Hl1 Hl2'". Qed.

End basics.
