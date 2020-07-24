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

  Definition send_once prot :=
    (<!> MSG (LitV $ true);
     <! (x : T) (v : val)> MSG v {{ IT x v }};
     prot x)%proto.

  Definition recv_once prot x :=
    (<? (w : val)> MSG w {{ IU (f x) w }};
     prot)%proto.

  Definition map_once prot :=
    (send_once $ recv_once $ prot).

  Lemma send_once_mono prot1 prot2 :
    ▷ (∀ x, prot1 x ⊑ prot2 x) -∗ send_once prot1 ⊑ send_once prot2.
  Proof.
    iIntros "Hsub".
    iModIntro.
    iIntros (x v) "Hv". iExists x, v. iFrame "Hv". iModIntro.
    iApply "Hsub".
  Qed.

  Global Instance send_once_from_modal p1 p2 :
    FromModal (modality_instances.modality_laterN 1) (∀ x, p1 x ⊑ p2 x)
              ((send_once p1) ⊑ (send_once p2)) (∀ x, p1 x ⊑ p2 x).
  Proof. apply send_once_mono. Qed.

  Lemma recv_once_mono prot1 prot2 x :
    ▷ (prot1 ⊑ prot2) -∗ recv_once prot1 x ⊑ recv_once prot2 x.
  Proof.
    iIntros "Hsub".
    iIntros (w) "Hw". iExists w. iFrame "Hw". iModIntro.
    iApply "Hsub".
  Qed.

  Global Instance recv_once_from_modal p1 p2 x :
    FromModal (modality_instances.modality_laterN 1) (p1 ⊑ p2)
              ((recv_once p1 x) ⊑ (recv_once p2 x)) (p1 ⊑ p2).
  Proof. apply recv_once_mono. Qed.

  Lemma map_once_mono prot1 prot2 :
    ▷ (prot1 ⊑ prot2) -∗ map_once prot1 ⊑ map_once prot2.
  Proof. iIntros "Hsub". iModIntro. iIntros (x). iModIntro. eauto. Qed.

  Global Instance map_once_from_modal p1 p2 :
    FromModal (modality_instances.modality_laterN 1) (p1 ⊑ p2)
              ((map_once p1) ⊑ (map_once p2)) (p1 ⊑ p2).
  Proof. apply map_once_mono. Qed.

  Definition mapper_prot_once :=
    (map_once mapper_prot)%proto.

  Lemma subprot_once :
    ⊢ mapper_prot ⊑ mapper_prot_once.
  Proof.
    rewrite /mapper_prot /mapper_prot_once.
    rewrite fixpoint_unfold /mapper_prot_aux.
    rewrite /iProto_choice.
    iExists true.
    iModIntro.
    iApply iProto_le_refl.
  Qed.

  Definition mapper_prot_twice :=
    map_once $ map_once $ mapper_prot.

  Lemma subprot_twice :
    ⊢ mapper_prot ⊑ mapper_prot_twice.
  Proof.
    iApply iProto_le_trans.
    { iApply subprot_once. }
    iModIntro.
    iApply subprot_once.
  Qed.

  Definition mapper_prot_twice_swap :=
    (<!> MSG (LitV $ true);
     <! (x1 : T) (v1 : val)> MSG v1 {{ IT x1 v1 }};
     <!> MSG (LitV $ true);
     <! (x2 : T) (v2 : val)> MSG v2 {{ IT x2 v2 }};
     <? (w1 : val)> MSG w1 {{ IU (f x1) w1 }};
     <? (w2 : val)> MSG w2 {{ IU (f x2) w2 }};
     mapper_prot)%proto.

  Lemma subprot_twice_swap :
    ⊢ mapper_prot ⊑ mapper_prot_twice_swap.
  Proof.
    iApply iProto_le_trans.
    { iApply subprot_twice. }
    iModIntro. iIntros (x1).
    iIntros (w1) "Hw1".
    iApply iProto_le_trans.
    { iApply iProto_le_base_swap. }
    iModIntro.
    iIntros (x2 v2) "Hv2".
    iApply (iProto_le_trans with "[Hv2]").
    { iModIntro. iExists x2, v2. iFrame "Hv2". iApply iProto_le_refl. }
    iApply iProto_le_trans.
    { iApply iProto_le_base_swap. }
    iModIntro.
    iExists (w1). iFrame "Hw1". iModIntro.
    iApply iProto_le_refl.
  Qed.

  Definition mapper_prot_twice_swap_end :=
    (<!> MSG (LitV $ true);
     <! (x1 : T) (v1 : val)> MSG v1 {{ IT x1 v1 }};
     <!> MSG (LitV $ true);
     <! (x2 : T) (v2 : val)> MSG v2 {{ IT x2 v2 }};
     <!> MSG (LitV $ false);
     <? (w1 : val)> MSG w1 {{ IU (f x1) w1 }};
     <? (w2 : val)> MSG w2 {{ IU (f x2) w2 }};
     END)%proto.

  Lemma subprot_twice_swap_end :
    ⊢ mapper_prot ⊑ mapper_prot_twice_swap_end.
  Proof.
    iApply iProto_le_trans.
    { iApply subprot_twice_swap. }
    rewrite /mapper_prot_twice_swap /mapper_prot_twice_swap_end.
    iIntros "!>" (x1).
    iIntros "!>" (x2).
    iApply iProto_le_trans.
    { iModIntro. iModIntro.
      rewrite /mapper_prot fixpoint_unfold /mapper_prot_aux /iProto_choice.
      iExists false. iApply iProto_le_refl. }
    iApply iProto_le_trans.
    { iModIntro.
      iIntros (w2) "Hw2".
      iApply iProto_le_trans.
      { iApply iProto_le_base_swap. }
      iModIntro. iExists w2. iSplitL. iExact "Hw2". iApply iProto_le_refl. }
    iIntros (w1) "Hw1".
    iApply iProto_le_trans.
    { iApply iProto_le_base_swap. }
    iModIntro. iExists w1. iSplitL. iExact "Hw1". iApply iProto_le_refl.
  Qed.

  Fixpoint mapper_prot_n n prot : iProto Σ :=
    match n with
    | O   => prot
    | S n => (<!> MSG (LitV $ true);
              <! (x : T) (v : val)> MSG v {{ IT x v }};
              <? (w : val)> MSG w {{ IU (f x) w }}; mapper_prot_n n prot)%proto
    end.

  Lemma subprot_n n :
    ⊢ mapper_prot ⊑ mapper_prot_n n mapper_prot.
  Proof.
    iInduction n as [|n] "IH"=> //.
    simpl.
    iApply (iProto_le_trans).
    { iApply subprot_once. }
    rewrite /mapper_prot_once.
    iModIntro. iApply "IH".
  Qed.

  Fixpoint recv_list xs prot :=
    match xs with
    | [] => prot
    | x::xs => (<? (w : val)> MSG w {{ IU (f x) w }};
               recv_list xs prot)%proto
  end.

  Lemma recv_list_mono xs prot1 prot2 :
    prot1 ⊑ prot2 -∗ recv_list xs prot1 ⊑ recv_list xs prot2.
  Proof.
    iIntros "Hsub".
    iInduction xs as [|xs] "IHxs"=> //.
    simpl.
    iIntros (w) "Hw". iExists w. iFrame "Hw". iModIntro.
    by iApply "IHxs".
  Qed.

  Fixpoint mapper_prot_n_swap n xs prot :=
    match n with
    | O   => recv_list (rev xs) prot%proto
    | S n => (<!> MSG (LitV $ true);
              <! (x : T) (v : val)> MSG v {{ IT x v }};
              mapper_prot_n_swap n (x::xs) prot)%proto
    end.

  Lemma recv_list_fwd xs v prot :
    ⊢ recv_list xs (<!> MSG v ; prot)%proto ⊑ (<!> MSG v ; recv_list xs prot)%proto.
  Proof.
    iInduction xs as [|x xs] "IH"=> //=.
    iIntros (w) "Hw".
    iApply (iProto_le_trans _ (<!> MSG v; <?> MSG w ;_)%proto); last first.
    { iModIntro. iExists w. iFrame "Hw". eauto. }
    iApply iProto_le_trans; last first.
    { iApply iProto_le_base_swap. }
    iModIntro. iApply "IH".
  Qed.

  Lemma subprot_n_n_swap n xs prot :
    ⊢ (recv_list xs (mapper_prot_n n prot)) ⊑ mapper_prot_n_swap n (rev xs) prot.
  Proof.
    iInduction n as [|n] "IHn" forall (xs) => //=.
    - iInduction xs as [|x xs] "IHxs"=> //=.
      rewrite rev_unit /= rev_involutive.
      iIntros (w1) "Hw1". iExists w1. iFrame "Hw1". iModIntro. iApply "IHxs".
    - iApply iProto_le_trans.
      { iApply recv_list_fwd. }
      (* iModIntro. *)
      iApply (iProto_le_trans _
              (<!> MSG LitV $ true ; <! (x : T) (v : val)> MSG v {{ IT x v }};
               recv_list xs (<? (w : val)> MSG w {{
     IU (f x) w }}; mapper_prot_n n prot))%proto).
      { iModIntro.
        iInduction xs as [|x xs] "IHxs"=> //.
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
      iIntros "!>" (x).
      rewrite -(rev_unit xs x).
      iApply (iProto_le_trans); last first.
      { iApply "IHn". }
      iInduction xs as [|y xs] "IHxs"=> //=.
      iIntros (w) "Hw". iExists w. iFrame "Hw". iModIntro.
      iApply "IHxs".
  Qed.

  Lemma subprot_n_swap n :
    ⊢ mapper_prot ⊑ mapper_prot_n_swap n [] mapper_prot.
  Proof.
    iApply iProto_le_trans.
    { iApply (subprot_n n). }
    iInduction n as [|n] "IHn"=> //=.
    iIntros "!>" (x).
    iApply (subprot_n_n_swap n [x]).
  Qed.

  Fixpoint mapper_prot_n_swap_fwd n xs prot :=
    match n with
    | O   => (<!> MSG LitV $ false; recv_list (rev xs) prot)%proto
    | S n => (<!> MSG (LitV $ true);
              <! (x : T) (v : val)> MSG v {{ IT x v }};
              mapper_prot_n_swap_fwd n (x::xs) prot)%proto
    end.

  Lemma subprot_n_swap_n_swap_end n xs :
    ⊢ mapper_prot_n_swap n xs mapper_prot ⊑ mapper_prot_n_swap_fwd n xs END%proto.
  Proof.
    iInduction n as [|n] "IHn" forall (xs)=> /=.
    - iApply iProto_le_trans.
      { iApply recv_list_mono.
        rewrite /mapper_prot fixpoint_unfold /mapper_prot_aux /iProto_choice.
        iExists false. iApply iProto_le_refl. }
      iApply recv_list_fwd.
    - iIntros "!>" (x). iApply "IHn".
  Qed.

  Lemma subprot_n_swap_end n :
    ⊢ mapper_prot ⊑ mapper_prot_n_swap_fwd n [] END%proto.
  Proof.
    iApply iProto_le_trans.
    { iApply (subprot_n_swap n). }
    iApply subprot_n_swap_n_swap_end.
  Qed.

End with_Σ.
