From actris.channel Require Import proofmode proto channel.
From iris.proofmode Require Import tactics.

Section subprotocol_basics.
  Context `{heapG Σ, chanG Σ}.

  Lemma reference_example (l1' : loc) :
    l1' ↦ #20 -∗
    (<! (l1 l2 : loc)> MSG (#l1, #l2) {{ l1 ↦ #20 ∗ l2 ↦ #22 }}; END) ⊑
    (<! (l2 : loc)> MSG (#l1', #l2) {{ l2 ↦ #22 }}; END).
  Proof. iIntros "Hl1'" (l2) "Hl2". iExists l1', l2. by iFrame "Hl1' Hl2". Qed.

  Lemma framing_example (P Q R : iProp Σ) (v w : val) :
    ⊢ ((<!> MSG v {{ P }} ; <?> MSG w {{ Q }}; END)%proto ⊑
       (<!> MSG v {{ P ∗ R }} ; <?> MSG w {{ Q ∗ R }};END)%proto)%proto.
  Proof.
    iIntros "[HP HR]". iFrame "HP". iModIntro.
    iIntros "HQ". iFrame "HQ HR". eauto.
  Qed.

  Definition prot1_aux (prot : iProto Σ) : iProto Σ :=
    (<! (x:Z)> MSG #x ; <?> MSG #(x+2) ; prot)%proto.
  Definition prot2_aux (prot : iProto Σ) : iProto Σ :=
    (<! (x:Z)> MSG #x ; <! (y:Z)> MSG #y ;
     <?> MSG #(x+2) ; <?> MSG #(y+2) ; prot)%proto.

  Instance prot1_aux_contractive : Contractive prot1_aux.
  Proof. solve_proto_contractive. Qed.
  Instance prot2_aux_contractive : Contractive prot2_aux.
  Proof. solve_proto_contractive. Qed.

  Definition prot1 : iProto Σ := fixpoint prot1_aux.
  Definition prot2 : iProto Σ := fixpoint prot2_aux.

  Lemma nonstructural_recursion_example :
    ⊢ prot1 ⊑ prot2.
  Proof.
    iLöb as "IH".
    iEval (rewrite /prot1 /prot2).
    do 2 rewrite (fixpoint_unfold prot1_aux).
    rewrite (fixpoint_unfold prot2_aux).
    iIntros (x). iExists x. iModIntro.
    iIntros (y).
    iApply (iProto_le_trans).
    { iModIntro. iExists y. iApply iProto_le_refl. }
    iApply iProto_le_trans; [ iApply iProto_le_base_swap | ].
    iModIntro. iModIntro. iModIntro.
    iApply "IH".
  Qed.

End subprotocol_basics.
