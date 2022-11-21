From iris.heap_lang Require Import proofmode notation spin_lock.
From iris.base_logic.lib Require Import saved_prop.
From actris Require Import llist proto_model.

Definition new_chan : val := λ: <>,
  let: "l" := lnil #() in
  let: "r" := lnil #() in
  let: "lk" := newlock #() in
  ((("l","r"),"lk"), (("r","l"),"lk")).

Definition send : val := λ: "c" "v",
  let: "lk" := Snd "c" in
  let: "l" := Fst (Fst "c") in
  acquire "lk";; lsnoc "l" "v";; release "lk".

Definition recv : val := rec: "go" "c" :=
  let: "lk" := Snd "c" in
  let: "l" := Snd (Fst "c") in
  acquire "lk";;
  if: lisnil "l" then release "lk";; "go" "c" else
  let: "x" := lpop "l" in release "lk";; "x".

Class chanG Σ := {
  chanG_lock :> lockG Σ;
  chanG_proto :> savedAnythingG Σ (laterOF (protoOF val idOF idOF))
}.
Notation saved_anything_own := (saved_anything_own (F:=laterOF (protoOF val idOF idOF))).

Definition chanΣ := #[ lockΣ; savedAnythingΣ (laterOF (protoOF val idOF idOF)) ].
Global Instance subG_chanΣ {Σ} : subG chanΣ Σ → chanG Σ.
Proof. solve_inG. Qed.

Definition iProto Σ := proto val (iPropO Σ) (iPropO Σ).

Definition iProto_end {Σ} : iProto Σ := proto_end.

Program Definition iProto_message {Σ A} (a : action)
    (pc : A → val * iProp Σ * iProto Σ) : iProto Σ :=
  proto_message a (λ v, λne f, ∃ x : A,
    ⌜ v = (pc x).1.1 ⌝ ∗ (pc x).1.2 ∗ f (Next (pc x).2))%I.
Next Obligation. solve_proper. Qed.

Definition iProto_dual {Σ} (p : iProto Σ) : iProto Σ :=
  proto_map action_dual cid cid p.

Definition proto_eq_next {Σ} (p : iProto Σ) : laterO (iProto Σ) -n> iPropO Σ :=
  OfeMor (internal_eq (Next p)).

Program Definition iProto_le_aux {Σ} (rec : iProto Σ -n> iProto Σ -n> iPropO Σ) :
    iProto Σ -n> iProto Σ -n> iPropO Σ := λne p1 p2,
  ((p1 ≡ proto_end ∗ p2 ≡ proto_end) ∨
   (∃ pc1 pc2,
     p1 ≡ proto_message Send pc1 ∗ p2 ≡ proto_message Send pc2 ∗
     ∀ v p2', pc2 v (proto_eq_next p2') -∗
       ∃ p1', ▷ rec p1' p2' ∗ pc1 v (proto_eq_next p1')) ∨
   (∃ pc1 pc2,
     p1 ≡ proto_message Receive pc1 ∗ p2 ≡ proto_message Receive pc2 ∗
     ∀ v p1', pc1 v (proto_eq_next p1') -∗
       ∃ p2', ▷ rec p1' p2' ∗ pc2 v (proto_eq_next p2')))%I.
Solve Obligations with solve_proper.
Local Instance iProto_le_aux_contractive {Σ} : Contractive (@iProto_le_aux Σ).
Proof. solve_contractive. Qed.
Definition iProto_le {Σ} (p1 p2 : iProto Σ) : iProp Σ :=
  fixpoint iProto_le_aux p1 p2.

Fixpoint proto_interp {Σ} (vs : list val) (p1 p2 : iProto Σ) : iProp Σ :=
  match vs with
  | [] => iProto_dual p1 ≡ p2
  | v :: vs => ∃ pc p2',
     p2 ≡ proto_message Receive pc ∗ pc v (proto_eq_next p2') ∗ ▷ proto_interp vs p1 p2'
  end.

Definition proto_inv `{!chanG Σ, !heapGS Σ} (γl γr : gname) (l r : loc) : iProp Σ :=
  ∃ ls rs pl pr,
    llist l ls ∗ llist r rs ∗
    saved_anything_own γl (DfracOwn (1/2)) (Next pl) ∗
    saved_anything_own γr (DfracOwn (1/2)) (Next pr) ∗
    ▷ ((⌜rs = []⌝ ∗ proto_interp ls pl pr) ∨ (⌜ls = []⌝ ∗ proto_interp rs pr pl)).

Definition mapsto_proto `{!chanG Σ, !heapGS Σ} (c : val) (p : iProto Σ) : iProp Σ :=
  ∃ γ γl γr (l r : loc) lk p',
    ⌜ c = (#l, #r, lk)%V ⌝ ∗ is_lock γ lk (proto_inv γl γr l r) ∗
    iProto_le p' p ∗ saved_anything_own γl (DfracOwn (1/2)) (Next p').
Notation "c ↣ p" := (mapsto_proto c p) (at level 20, format "c  ↣  p").

Section proto.
  Context `{!chanG Σ, !heapGS Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types A : Type.

  Global Instance iProto_dual_ne : NonExpansive (@iProto_dual Σ).
  Proof. solve_proper. Qed.
  Global Instance iProto_dual_proper : Proper ((≡) ==> (≡)) (@iProto_dual Σ).
  Proof. apply (ne_proper _). Qed.
  Global Instance iProto_dual_involutive : Involutive (≡) (@iProto_dual Σ).
  Proof.
    intros p. rewrite /iProto_dual -proto_map_compose -{2}(proto_map_id p).
    apply: proto_map_ext=> //. by intros [].
  Qed.
  Lemma iProto_dual_end : iProto_dual (Σ:=Σ) iProto_end ≡ iProto_end.
  Proof. by rewrite /iProto_dual proto_map_end. Qed.
  Lemma iProto_dual_message {A} a (pc : A → val * iProp Σ * iProto Σ) :
    iProto_dual (iProto_message a pc)
    ≡ iProto_message (action_dual a) (prod_map id iProto_dual ∘ pc).
  Proof.
    rewrite /iProto_dual /iProto_message proto_map_message. f_equiv=> v f //=.
  Qed.

  Global Instance iProto_le_ne : NonExpansive2 (@iProto_le Σ).
  Proof. solve_proper. Qed.
  Global Instance iProto_le_proper : Proper ((≡) ==> (≡) ==> (⊣⊢)) (@iProto_le Σ).
  Proof. solve_proper. Qed.

  Lemma iProto_le_unfold p1 p2 :
    iProto_le p1 p2 ≡ iProto_le_aux (fixpoint iProto_le_aux) p1 p2.
  Proof. apply: (fixpoint_unfold iProto_le_aux). Qed.

  Lemma iProto_le_refl p : ⊢ iProto_le p p.
  Proof.
    iLöb as "IH" forall (p). destruct (proto_case p) as [->|([]&pc&->)].
    - rewrite iProto_le_unfold. iLeft; by auto.
    - rewrite iProto_le_unfold. iRight; iLeft. iExists _, _; do 2 (iSplit; [done|]).
      iIntros (v p') "Hpc". iExists p'. iIntros "{$Hpc} !>". iApply "IH".
    - rewrite iProto_le_unfold. iRight; iRight. iExists _, _; do 2 (iSplit; [done|]).
      iIntros (v p') "Hpc". iExists p'. iIntros "{$Hpc} !>". iApply "IH".
  Qed.

  Lemma iProto_le_end_inv p : iProto_le p proto_end -∗ p ≡ proto_end.
  Proof.
    rewrite iProto_le_unfold. iIntros "[[Hp _]|H] //".
    iDestruct "H" as "[H|H]"; iDestruct "H" as (pc1 pc2) "(_ & Heq & _)";
      by rewrite proto_end_message_equivI.
  Qed.

  Lemma iProto_le_send_inv p1 pc2 :
    iProto_le p1 (proto_message Send pc2) -∗ ∃ pc1,
      p1 ≡ proto_message Send pc1 ∗
      ∀ v p2', pc2 v (proto_eq_next p2') -∗
        ∃ p1', ▷ iProto_le p1' p2' ∗ pc1 v (proto_eq_next p1').
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Heq]|[H|H]]".
    - by rewrite proto_message_end_equivI.
    - iDestruct "H" as (pc1 pc2') "(Hp1 & Heq & H)".
      iDestruct (proto_message_equivI with "Heq") as "[_ #Heq]".
      iExists pc1. iIntros "{$Hp1}" (v p2') "Hpc".
      iSpecialize ("Heq" $! v). iDestruct (ofe_morO_equivI with "Heq") as "Heq'".
      iRewrite ("Heq'" $! (proto_eq_next p2')) in "Hpc". by iApply "H".
    - iDestruct "H" as (pc1 pc2') "(_ & Heq & _)".
      by iDestruct (proto_message_equivI with "Heq") as "[% ?]".
  Qed.

  Lemma iProto_le_recv_inv p1 pc2 :
    iProto_le p1 (proto_message Receive pc2) -∗ ∃ pc1,
      p1 ≡ proto_message Receive pc1 ∗
      ∀ v p1', pc1 v (proto_eq_next p1') -∗
        ∃ p2', ▷ iProto_le p1' p2' ∗ pc2 v (proto_eq_next p2').
  Proof.
    rewrite iProto_le_unfold. iIntros "[[_ Heq]|[H|H]]".
    - by rewrite proto_message_end_equivI.
    - iDestruct "H" as (pc1 pc2') "(_ & Heq & _)".
      by iDestruct (proto_message_equivI with "Heq") as "[% ?]".
    - iDestruct "H" as (pc1 pc2') "(Hp1 & Heq & H)".
      iDestruct (proto_message_equivI with "Heq") as "[_ #Heq]".
      iExists pc1. iIntros "{$Hp1}" (v p1') "Hpc".
      iSpecialize ("Heq" $! v). iDestruct (ofe_morO_equivI with "Heq") as "Heq'".
      iDestruct ("H" with "Hpc") as (p2') "[Hle Hpc]".
      iExists p2'. iFrame "Hle". by iRewrite ("Heq'" $! (proto_eq_next p2')).
  Qed.

  Lemma iProto_le_trans p1 p2 p3 :
    iProto_le p1 p2 -∗ iProto_le p2 p3 -∗ iProto_le p1 p3.
  Proof.
    iIntros "H1 H2". iLöb as "IH" forall (p1 p2 p3).
    destruct (proto_case p3) as [->|([]&pc3&->)].
    - rewrite iProto_le_end_inv. by iRewrite "H2" in "H1".
    - iDestruct (iProto_le_send_inv with "H2") as (pc2) "[Hp2 H3]".
      iRewrite "Hp2" in "H1".
      iDestruct (iProto_le_send_inv with "H1") as (pc1) "[Hp1 H2]".
      iRewrite "Hp1". rewrite iProto_le_unfold; iRight; iLeft.
      iExists _, _; do 2 (iSplit; [done|]). iIntros (v p3') "Hpc".
      iDestruct ("H3" with "Hpc") as (p2') "[Hle Hpc]".
      iDestruct ("H2" with "Hpc") as (p1') "[Hle' Hpc]".
      iExists p1'. iIntros "{$Hpc} !>". by iApply ("IH" with "Hle'").
    - iDestruct (iProto_le_recv_inv with "H2") as (pc2) "[Hp2 H3]".
      iRewrite "Hp2" in "H1".
      iDestruct (iProto_le_recv_inv with "H1") as (pc1) "[Hp1 H2]".
      iRewrite "Hp1". rewrite iProto_le_unfold; iRight; iRight.
      iExists _, _; do 2 (iSplit; [done|]).
      iIntros (v p1') "Hpc".
      iDestruct ("H2" with "Hpc") as (p2') "[Hle Hpc]".
      iDestruct ("H3" with "Hpc") as (p3') "[Hle' Hpc]".
      iExists p3'. iIntros "{$Hpc} !>". by iApply ("IH" with "Hle").
  Qed.

  Lemma iProto_send_le {A1 A2} (pc1 : A1 → val * iProp Σ * iProto Σ)
      (pc2 : A2 → val * iProp Σ * iProto Σ) :
    (∀ x2 : A2, (pc2 x2).1.2 -∗ ∃ x1 : A1,
      ⌜(pc1 x1).1.1 = (pc2 x2).1.1⌝ ∗
      (pc1 x1).1.2 ∗
      ▷ iProto_le (pc1 x1).2 (pc2 x2).2) -∗
    iProto_le (iProto_message Send pc1) (iProto_message Send pc2).
  Proof.
    iIntros "H". rewrite iProto_le_unfold. iRight; iLeft.
    iExists _, _; do 2 (iSplit; [done|]).
    iIntros (v p2') "/=". iDestruct 1 as (x2 ->) "[Hpc #Heq]".
    iDestruct ("H" with "Hpc") as (x1 ?) "[Hpc Hle]".
    iExists (pc1 x1).2. iSplitL "Hle".
    { iNext. change (fixpoint iProto_le_aux ?p1 ?p2) with (iProto_le p1 p2).
      by iRewrite "Heq". }
    iExists x1. iSplit; [done|]. iSplit; [by iApply "Hpc"|done].
  Qed.

  Lemma iProto_recv_le {A1 A2} (pc1 : A1 → val * iProp Σ * iProto Σ)
      (pc2 : A2 → val * iProp Σ * iProto Σ) :
    (∀ x1 : A1, (pc1 x1).1.2 -∗ ∃ x2 : A2,
      ⌜(pc1 x1).1.1 = (pc2 x2).1.1⌝ ∗
      (pc2 x2).1.2 ∗
      ▷ iProto_le (pc1 x1).2 (pc2 x2).2) -∗
    iProto_le (iProto_message Receive pc1) (iProto_message Receive pc2).
  Proof.
    iIntros "H". rewrite iProto_le_unfold. iRight; iRight.
    iExists _, _; do 2 (iSplit; [done|]).
    iIntros (v p1') "/=". iDestruct 1 as (x1 ->) "[Hpc #Heq]".
    iDestruct ("H" with "Hpc") as (x2 ?) "[Hpc Hle]". iExists (pc2 x2).2. iSplitL "Hle".
    { iIntros "!>". change (fixpoint iProto_le_aux ?p1 ?p2) with (iProto_le p1 p2).
      by iRewrite "Heq". }
    iExists x2. iSplit; [done|]. iSplit; [by iApply "Hpc"|done].
  Qed.

  Lemma iProto_mapsto_le c p1 p2 : c ↣ p1 -∗ iProto_le p1 p2 -∗ c ↣ p2.
  Proof.
    iDestruct 1 as (γ γl γr l r lk p1' ->) "(Hlk & Hle & H)".
    iIntros "Hle'". iExists γ, γl, γr, l, r, lk, p1'. iSplit; first done. iFrame.
    by iApply (iProto_le_trans with "Hle").
  Qed.

  Global Instance proto_interp_ne vs : NonExpansive2 (proto_interp (Σ:=Σ) vs).
  Proof. induction vs; solve_proper. Qed.
  Global Instance proto_interp_proper vs :
    Proper ((≡) ==> (≡) ==> (≡)) (proto_interp (Σ:=Σ) vs).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance mapsto_proto_ne c : NonExpansive (mapsto_proto c).
  Proof. solve_proper. Qed.
  Global Instance mapsto_proto_proper c : Proper ((≡) ==> (≡)) (mapsto_proto c).
  Proof. apply (ne_proper _). Qed.

  Lemma proto_eq_next_dual p :
    ofe_mor_map (laterO_map (proto_map action_dual cid cid)) cid (proto_eq_next (iProto_dual p)) ≡
    proto_eq_next p.
  Proof.
    intros lp. iSplit; iIntros "Hlp /="; last by iRewrite -"Hlp".
    destruct (Next_uninj lp) as [p' ->].
    rewrite /later_map /= !later_equivI. iNext.
    rewrite -{2}(involutive iProto_dual p) -{2}(involutive iProto_dual p').
    by iRewrite "Hlp".
  Qed.

  Lemma proto_interp_send v vs pc p1 p2 :
    proto_interp vs (proto_message Send pc) p2 -∗
    pc v (proto_eq_next p1) -∗
    proto_interp (vs ++ [v]) p1 p2.
  Proof.
    iIntros "Heval Hc". iInduction vs as [|v' vs] "IH" forall (p2); simpl.
    - iDestruct "Heval" as "#Heval".
      iExists _, (iProto_dual p1). iSplit.
      { iRewrite -"Heval". by rewrite /iProto_dual proto_map_message. }
      rewrite /= proto_eq_next_dual; auto.
    - iDestruct "Heval" as (pc' p2') "(Heq & Hc' & Heval)".
      iExists pc', p2'. iFrame "Heq Hc'". iNext. iApply ("IH" with "Heval Hc").
  Qed.

  Lemma proto_interp_recv v vs p1 pc :
    proto_interp (v :: vs) p1 (proto_message Receive pc) -∗
    ∃ p2, pc v (proto_eq_next p2) ∗ ▷ proto_interp vs p1 p2.
  Proof.
    simpl. iDestruct 1 as (pc' p2) "(Heq & Hc & Hp2)". iExists p2. iFrame "Hp2".
    iDestruct (@proto_message_equivI with "Heq") as "[_ Heq]".
    iSpecialize ("Heq" $! v). rewrite ofe_morO_equivI.
    by iRewrite ("Heq" $! (proto_eq_next p2)).
  Qed.

  Lemma proto_interp_False p pc v vs :
    proto_interp (v :: vs) p (proto_message Send pc) -∗ False.
  Proof.
    simpl. iDestruct 1 as (pc' p2') "[Heq _]".
    by iDestruct (@proto_message_equivI with "Heq") as "[% _]".
  Qed.

  Lemma proto_interp_nil p1 p2 : proto_interp [] p1 p2 -∗ p1 ≡ iProto_dual p2.
  Proof. iIntros "#H /=". iRewrite -"H". by rewrite involutive. Qed.

  Lemma proto_inv_flip γr γl r l : proto_inv γr γl r l ⊣⊢ proto_inv γl γr l r.
  Proof.
    iSplit; iDestruct 1 as (ls rs pl pr) "(?&?&?&?&[?|?])";
      iExists rs, ls, pr, pl; iFrame.
  Qed.

  Lemma new_chan_proto_spec p :
    {{{ True }}} new_chan #() {{{ c1 c2, RET (c1,c2); c1 ↣ p ∗ c2 ↣ iProto_dual p }}}.
  Proof.
    iIntros (Ψ _) "HΨ". wp_lam.
    wp_apply (lnil_spec with "[//]"); iIntros (l) "Hl".
    wp_smart_apply (lnil_spec with "[//]"); iIntros (r) "Hr".
    pose proof (saved_anything_alloc (F:=laterOF (protoOF val idOF idOF)) (Next p) (DfracOwn 1)) as Hl.
    iMod Hl as (γl) "[Hγl1 Hγl2]"; first done.
    pose proof (saved_anything_alloc (F:=laterOF (protoOF val idOF idOF))
      (Next (iProto_dual p)) (DfracOwn 1)) as Hr.
    iMod Hr as (γr) "[Hγr1 Hγr2]"; first done.
    wp_smart_apply (newlock_spec (proto_inv γl γr l r) with "[-HΨ Hγl1 Hγr1]").
    { iExists [], [], p, (iProto_dual p). eauto with iFrame. }
    iIntros (lk γ) "#Hlk". wp_pures. iApply "HΨ". iIntros "!>"; iSplitL "Hγl1".
    - iExists γ, γl, γr, l, r, lk, p; simpl. iFrame "Hγl1 Hlk".
      iSplit; [done|]. iApply iProto_le_refl.
    - iExists γ, γr, γl, r, l, lk, (iProto_dual p); simpl.
      rewrite proto_inv_flip. iFrame "Hγr1 Hlk". iSplit; [done|]. iApply iProto_le_refl.
  Qed.

  Lemma send_proto_spec_packed {A} c (pc : A → val * iProp Σ * iProto Σ) (x : A) :
    {{{ c ↣ iProto_message Send pc ∗ (pc x).1.2 }}}
      send c (pc x).1.1
    {{{ RET #(); c ↣ (pc x).2 }}}.
  Proof.
    iIntros (Ψ) "[Hp HP] HΨ". wp_lam.
    iDestruct "Hp" as (γ γl γr l r lk p' ->) "(#Hlock & Hle & Hp')". wp_pures.
    wp_smart_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    iDestruct "Hinv" as (ll rl pl pr) "(Hll & Hlr & Hpl & Hpr & H)".
    iDestruct (saved_anything_agree with "Hp' Hpl") as "#Heq".
    wp_smart_apply (lsnoc_spec with "[$Hll //]"); iIntros "Hll".
    iDestruct (iProto_le_send_inv with "Hle") as (pc') "[Hpc Hle] /=".
    iDestruct ("Hle" with "[HP]") as (p'') "[Hle Hpc']"; [iExists x; by iFrame|].
    iMod (saved_anything_update_halves with "Hp' Hpl") as "[Hp' Hpl]".
    wp_smart_apply (release_spec with "[-$Hlock $Hlocked HΨ Hle Hp']").
    { iExists (ll ++ [(pc x).1.1]), rl, p'', pr. iFrame. iNext. iLeft.
      iRewrite -"Heq" in "H". iRewrite "Hpc" in "H". iDestruct "H" as "[[-> H]|[-> H]]".
      { iSplit; [done|]. by iApply (proto_interp_send with "H"). }
      destruct rl; [|iDestruct (proto_interp_False with "H") as %[]].
      iSplit; [done|]. iRewrite (proto_interp_nil with "H").
      by iApply (proto_interp_send with  "[] Hpc'"). }
    iIntros "_". iApply "HΨ". iExists γ, γl, γr, l, r, lk, p''. auto with iFrame.
  Qed.

  Opaque proto_interp.

  Lemma recv_proto_spec_packed {A} c (pc : A → val * iProp Σ * iProto Σ) :
    {{{ c ↣ iProto_message Receive pc }}}
      recv c
    {{{ x, RET (pc x).1.1; c ↣ (pc x).2 ∗ (pc x).1.2 }}}.
  Proof.
    iIntros (Ψ) "Hp HΨ". iLöb as "IH". wp_lam.
    iDestruct "Hp" as (γ γl γr l r lk p' ->) "(#Hlock & Hle & Hp')". wp_pures.
    wp_smart_apply (acquire_spec with "Hlock"); iIntros "[Hlocked Hinv]".
    iDestruct "Hinv" as (ll rl pl pr) "(Hll & Hlr & Hpl & Hpr & H)".
    wp_smart_apply (lisnil_spec with "Hlr"); iIntros "Hlr". destruct rl as [|v rl].
    { wp_pures. wp_smart_apply (release_spec with "[-$Hlock $Hlocked HΨ Hle Hp']").
      { iExists ll, [], pl, pr. iFrame. }
      iIntros "_". wp_smart_apply ("IH" with "[Hle Hp'] HΨ").
      iExists γ, γl, γr, l, r, lk, p'. auto with iFrame. }
    iDestruct "H" as "[[% _]|[-> H]]"; [done|].
    iDestruct (saved_anything_agree with "Hp' Hpl") as "#Heq".
    wp_smart_apply (lpop_spec with "Hlr"); iIntros "Hlr"; simplify_eq.
    iDestruct (iProto_le_recv_inv with "Hle") as (pc') "[Hpc Hle] /=".
    iRewrite -"Heq" in "H". iRewrite "Hpc" in "H".
    iDestruct (proto_interp_recv with "H") as (p'') "[Hpc' H]".
    iDestruct ("Hle" with "Hpc'") as (p''') "(Hle & %x & -> & Hpc & #Heq')".
    iMod (saved_anything_update_halves with "Hp' Hpl") as "[Hp' Hpl]".
    wp_smart_apply (release_spec with "[-$Hlock $Hlocked HΨ Hle Hp' Hpc]").
    { iExists [], rl, p'', pr. auto with iFrame. }
    iIntros "_". wp_pures. iRewrite "Heq'" in "Hle". iApply "HΨ". iFrame.
    iExists γ, γl, γr, l, r, lk, p''. auto with iFrame.
  Qed.
End proto.
