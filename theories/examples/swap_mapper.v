From actris.channel Require Import proofmode proto channel.
From iris.proofmode Require Import tactics.
From actris.utils Require Import llist.
From iris.heap_lang Require Import notation.

Section with_Σ.
  Context `{heapG Σ, chanG Σ}.
  Context {T U R : Type}.
  Context (IT : T → val → iProp Σ).
  Context (IU : U → val → iProp Σ).
  Context (f : T → U).

  Definition mapper_prot_aux (rec : iProto Σ) : iProto Σ :=
    ((<! (x : T) (v : val)> MSG v {{ IT x v }};
     <? (w : val)> MSG w {{ IU (f x) w }}; rec) <+> END)%proto.

  Instance mapper_prot_aux_contractive : Contractive mapper_prot_aux.
  Proof. solve_proto_contractive. Qed.

  Definition mapper_prot := fixpoint mapper_prot_aux.

  Global Instance par_map_protocol_unfold :
    ProtoUnfold (mapper_prot) (mapper_prot_aux mapper_prot).
  Proof. apply proto_unfold_eq, (fixpoint_unfold mapper_prot_aux). Qed.

  Definition mapper_prot_twice :=
    (<!> MSG (LitV $ true);
     <! (x1 : T) (v1 : val)> MSG v1 {{ IT x1 v1 }};
     <? (w1 : val)> MSG w1 {{ IU (f x1) w1 }};
     <!> MSG (LitV $ true);
     <! (x2 : T) (v2 : val)> MSG v2 {{ IT x2 v2 }};
     <? (w2 : val)> MSG w2 {{ IU (f x2) w2 }};
      <!> MSG (LitV $ false);
      END)%proto.

  Definition mapper_prot_twice_swap :=
    (<!> MSG (LitV $ true) {{ True }};
     <! (x1 : T) (v1 : val)> MSG v1 {{ IT x1 v1 }};
     <!> MSG (LitV $ true) {{ True }};
     <! (x2 : T) (v2 : val)> MSG v2 {{ IT x2 v2 }};
     <!> MSG (LitV $ false) {{ True }};
     <? (w1 : val)> MSG w1 {{ IU (f x1) w1 }};
     <? (w2 : val)> MSG w2 {{ IU (f x2) w2 }};
    END)%proto.

  Lemma subprot_twice :
    ⊢ mapper_prot ⊑ mapper_prot_twice_swap.
  Proof.
    rewrite /mapper_prot /mapper_prot_twice.
    rewrite fixpoint_unfold fixpoint_unfold fixpoint_unfold /mapper_prot_aux.
    iApply (iProto_le_trans _ mapper_prot_twice).
    { rewrite /iProto_choice.
      iExists true. iModIntro.
      iIntros (x1 v1) "Hv1". iExists x1, v1. iFrame "Hv1". iModIntro.
      iIntros (w1) "Hw1". iExists w1. iFrame "Hw1". iModIntro.
      iExists true. iModIntro.
      iIntros (x2 v2) "Hv2". iExists x2, v2. iFrame "Hv2". iModIntro.
      iIntros (w2) "Hw2". iExists w2. iFrame "Hw2". iModIntro.
      iExists false. eauto. }
    rewrite /mapper_prot_twice /mapper_prot_twice_swap.
    iModIntro.
    iIntros (x1 v1) "Hv1". iExists x1, v1. iFrame "Hv1". iModIntro.
    iIntros (w1) "Hw1".
    iApply (iProto_le_trans); first by iApply iProto_le_base_swap.
    iModIntro.
    iIntros (x2 v2) "Hv2".
    iApply (iProto_le_trans with "[Hv2]").
    { iModIntro. iExists x2, v2. iFrame "Hv2". iModIntro. iApply iProto_le_refl. }
    iApply (iProto_le_trans).
    { iApply iProto_le_base_swap. }
    iModIntro.
    iApply iProto_le_trans.
    { iModIntro. iIntros (w2) "Hw2".
      iApply iProto_le_trans.
      { iApply iProto_le_base_swap. }
      iModIntro. iExists (w2). iSplitL. iExact "Hw2". iApply iProto_le_refl. }
    iApply iProto_le_trans.
    { iApply iProto_le_base_swap. }
    iModIntro.
    iExists (w1). iFrame "Hw1". iModIntro.
    eauto.
  Qed.

  Fixpoint mapper_prot_list n : iProto Σ :=
    match n with
    | O   => (<!> MSG (LitV $ false); END)%proto
    | S n => (<!> MSG (LitV $ true);
              <! (x : T) (v : val)> MSG v {{ IT x v }};
              <? (w : val)> MSG w {{ IU (f x) w }}; mapper_prot_list n)%proto
    end.

  Lemma subprot_list n :
    ⊢ mapper_prot ⊑ mapper_prot_list n.
  Proof.
    iEval (rewrite /mapper_prot).
    iInduction n as [|n] "IH"; iEval (rewrite fixpoint_unfold /mapper_prot_aux).
    - rewrite /iProto_choice. iExists false. eauto.
    - rewrite /iProto_choice /=.
      iExists true. iModIntro.
      iIntros (x1 v1) "Hv1". iExists x1, v1. iFrame "Hv1". iModIntro.
      iIntros (w1) "Hw1". iExists w1. iFrame "Hw1". iModIntro. iApply "IH".
  Qed.

  Fixpoint mapper_prot_list_swap_tail xs :=
    match xs with
    | []    => END%proto
    | x::xs => (<? (w : val)> MSG w {{ IU (f x) w }};
                    mapper_prot_list_swap_tail xs)%proto
    end.

  Fixpoint mapper_prot_list_swap n xs :=
    match n with
    | O   => (<!> MSG (LitV $ false); mapper_prot_list_swap_tail (rev xs))%proto
    | S n => (<!> MSG (LitV $ true);
              <! (x : T) (v : val)> MSG v {{ IT x v }};
              mapper_prot_list_swap n (x::xs))%proto
    end.

  Fixpoint mapper_prot_list_swap_recv_head xs prot :=
    match xs with
    | [] => prot
    | x::xs => (<? w> MSG w {{ IU (f x) w }};
               mapper_prot_list_swap_recv_head xs prot)%proto
  end.

  Lemma mapper_prot_list_swap_forward xs w prot :
    ⊢ (mapper_prot_list_swap_recv_head xs (<!> MSG w; prot))%proto ⊑
      (<!> MSG w; mapper_prot_list_swap_recv_head xs prot)%proto.
  Proof.
    iInduction xs as [|x xs] "IH"=> //=.
    iIntros (v) "Hv".
    iApply (iProto_le_trans _ (<!> MSG w; <?> MSG v ;_)%proto); last first.
    { iModIntro. iExists v. iFrame "Hv". eauto. }
    iApply iProto_le_trans; last first.
    { iApply iProto_le_base_swap. }
    iModIntro. iApply "IH".
  Qed.

  Lemma subprot_list_swap_general xs n :
    ⊢  mapper_prot_list_swap_recv_head xs (mapper_prot_list n) ⊑
       mapper_prot_list_swap n (rev xs).
  Proof.
    iInduction n as [|n] "IHn" forall (xs).
    - simpl. rewrite rev_involutive.
      iApply iProto_le_trans.
      { iApply mapper_prot_list_swap_forward. }
      iModIntro.
      iInduction xs as [|x xs] "IHxs"=> //.
      iIntros (w) "Hw". iExists w. iFrame "Hw". iModIntro. iApply "IHxs".
    - iApply iProto_le_trans.
      { iApply mapper_prot_list_swap_forward. }
      iModIntro.
      iApply (iProto_le_trans _
              (<! (x : T) (v : val)> MSG v {{ IT x v }};
               mapper_prot_list_swap_recv_head xs
    (<? (w : val)> MSG w {{
     IU (f x) w }}; mapper_prot_list n))%proto).
      {
        iInduction xs as [|x xs] "IHxs"=> //=.
        iIntros (w) "Hw".
        iApply iProto_le_trans.
        { iModIntro. iApply "IHxs". }
        iIntros (y v) "Hv".
        iApply (iProto_le_trans with "[Hv]").
        { iModIntro. iExists y,v. iFrame "Hv". eauto. }
        iApply (iProto_le_trans).
        { iApply iProto_le_base_swap. }
        iModIntro. iExists w. iFrame "Hw". eauto.
      }
      iIntros (x v) "Hv". iExists x,v. iFrame "Hv". iModIntro.
      rewrite -(rev_unit xs x).
      iApply (iProto_le_trans); last first.
      { iApply "IHn". }
      iInduction xs as [|y xs] "IHxs"=> //=.
      iIntros (w) "Hw". iExists w. iFrame "Hw". iModIntro.
      iApply "IHxs".
  Qed.

  Lemma subprot_list_swap n :
    ⊢  mapper_prot ⊑ mapper_prot_list_swap n [].
  Proof.
    iApply iProto_le_trans.
    { iApply (subprot_list n). }
    iApply (subprot_list_swap_general [] n).
  Qed.

End with_Σ.
