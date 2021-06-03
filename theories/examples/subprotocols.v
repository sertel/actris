From actris.channel Require Import proofmode proto channel.
From iris.proofmode Require Import tactics.

Section subprotocol_basics.
  Context `{heapGS Σ, chanG Σ}.

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

  Fixpoint is_list (v : val) (ws : list val) : iProp Σ :=
    match ws with
    | []    => True
    | w::ws => ∃ (v' : val), ⌜v = PairV w v'⌝ ∗ is_list v' ws
  end.

  Fixpoint is_int_list (v : val) (xs : list Z) : iProp Σ :=
    match xs with
    | []    => True
    | x::xs => ∃ (v' : val), ⌜v = PairV (LitV $ LitInt $ x) v'⌝ ∗ is_int_list v' xs
  end.

  Lemma is_list_int_list v xs :
    is_int_list v xs -∗ ∃ (ws : list val), is_list v ws ∗
                        [∗ list] i↦x;w ∈ xs;ws, ⌜LitV $ LitInt $ x = w⌝%I.
  Proof.
    iIntros "H".
    iInduction (xs) as [|x xs] "IH" forall (v).
    { iExists []; eauto. }
    iDestruct "H" as (v' ->) "H".
    iDestruct ("IH" with "H") as (ws) "[Hlist Heq]".
    iExists (#x :: ws); simpl; eauto.
  Qed.

  Lemma list_length_example :
    ⊢ (<? (v:val) (xs : list Z)> MSG v {{ is_int_list v xs }} ;
       <!> MSG #(length xs) ; END) ⊑
      (<? (v:val) (ws : list val)> MSG v {{ is_list v ws }} ;
       <!> MSG #(length ws) ; END).
  Proof.
    iIntros (v xs) "H".
    iDestruct (is_list_int_list with "H") as (ws) "[H Hlen]".
    iDestruct (big_sepL2_length with "Hlen") as %Hlen.
    iExists v, ws. iFrame "H".
    iModIntro. rewrite Hlen. eauto.
  Qed.

End subprotocol_basics.
