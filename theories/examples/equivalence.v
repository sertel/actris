From actris.channel Require Import channel proofmode.

Section equivalence_examples.
  Context `{heapG Σ, chanG Σ}.

  Lemma binder_swap_equivalence_example :
    ((<! (x y : Z)> MSG (#x,#y) ; END):iProto Σ)%proto ≡
    ((<! (y x : Z)> MSG (#x,#y) ; END):iProto Σ)%proto.
  Proof.
    apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iApply iProto_message_equiv; [ done | | ].
    - iIntros "!>" (x y) "_". iExists y, x. eauto.
    - iIntros "!>" (y x) "_". iExists x, y. eauto.
  Qed.

  Lemma choice_equivalence_example (P1 P2 Q1 Q2: iProp Σ) (S1 S2 : iProto Σ) :
    (S1 <{P1 ∗ Q1}+{P2 ∗ Q2}> S2)%proto ≡ (S1 <{Q1 ∗ P1}+{Q2 ∗ P2}> S2)%proto.
  Proof.
    apply (uPred.internal_eq_soundness (M:=iResUR Σ)).
    iApply iProto_choice_equiv; [ done | | | done | done ].
    iApply prop_ext. iSplit; iIntros "!> [$ $]".
    iApply prop_ext. iSplit; iIntros "!> [$ $]".
  Qed.

End equivalence_examples.
