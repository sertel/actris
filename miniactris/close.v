From miniactris Require Export sub.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang.lib Require Import assert.

Definition new : val := new1.
Definition recv : val := recv1.
Definition send : val := λ: "l" "v",
  let: "l'" := new #() in
  send1 "l" ("v","l'");; "l'".
Definition send_close : val := λ: "l" "v", send1 "l" ("v", #()).
Definition sym_close : val := λ: "l",
  if: CAS "l" NONE (SOME #()) then #() else Free "l".

Section close_proofs.
  Context `{!heapGS Σ, !chanG Σ}.
  Let N := nroot .@ "chan".
  Notation prot := (prot Σ).

  (* prot' ≜ prot | send_end | sym_end *)
  Definition prot' : ofe := optionO $ optionO prot.

  Definition is_send_end ch : iProp Σ := ▷ ⌜ch = #()⌝.
  Definition send_end_prot : prot' := Some None.

  Definition end_inv (γ1 γ2 : gname) (l : loc) : iProp Σ :=
    l ↦ NONEV ∨
    (l ↦ SOMEV #() ∗ (tok γ1 ∨ tok γ2)) ∨
    (tok γ1 ∗ tok γ2).
  Lemma end_inv_iff γ1 γ2 l : end_inv γ1 γ2 l ⊣⊢ end_inv γ2 γ1 l.
  Proof.
    by rewrite /end_inv (bi.or_comm (tok γ1) (tok γ2))
       (bi.sep_comm (tok γ1) (tok γ2)).
  Qed.
  Definition is_sym_end (ch : val) : iProp Σ :=
    ∃ γ1 γ2 (l : loc), ▷ ⌜ch = #l⌝ ∗ inv N (end_inv γ1 γ2 l) ∗ ▷ tok γ1.
  Definition sym_end_prot : prot' := None.

  Definition is_chan' (ch : val) (p : prot') : iProp Σ :=
    match p with
    | Some (Some p) => is_chan ch p
    | Some None => is_send_end ch
    | None => is_sym_end ch
    end.

  Definition dual' : prot' → prot' := λ p,
    match p with
    | Some (Some p) => Some $ Some $ dual p
    | Some None => Some None
    | None => None
    end.

  (* ?x <v x> {P x}. p x *)
  Definition recv_prot' {A} (v : A → val) (Φ : A → iPropO Σ) (p : A → prot') : prot' :=
    Some $ Some (false, λ r, ∃ x ch', ⌜r = (v x, ch')%V⌝ ∗ Φ x ∗ is_chan' ch' (p x))%I.

  (* !x <v x> {P x}. p x *)
  Definition send_prot' {A} (v : A → val) (Φ : A → iPropO Σ) (p : A → prot') : prot' :=
    dual' (recv_prot' v Φ (dual' ∘ p)).

  Definition subprot' (p1' p2' : prot') : iProp Σ :=
    match p1',p2' with
    | Some (Some p1), Some (Some p2) => subprot p1 p2
    | Some None, Some None => True
    | None, None => True
    | _, _ => False
    end.

  Global Instance dual_ne : NonExpansive dual'.
  Proof. solve_proper. Qed.
  Global Instance dual_proper : Proper ((≡) ==> (≡)) dual'.
  Proof. solve_proper. Qed.

  Global Instance subprot_ne' : NonExpansive2 subprot'.
  Proof. solve_proper. Qed.
  Global Instance subprot_proper' : Proper ((≡) ==> (≡) ==> (≡)) subprot'.
  Proof. apply ne_proper_2, _. Qed.

  Global Instance is_end_is_except_0 ch : IsExcept0 (is_sym_end ch).
  Proof.
    rewrite /IsExcept0 /is_sym_end. repeat (setoid_rewrite bi.except_0_exist).
    do 6 f_equiv. rewrite !bi.except_0_sep !bi.except_0_later.
    by rewrite except_0_inv.
  Qed.
  Global Instance is_chan_is_except_0' ch p : IsExcept0 (is_chan' ch p).
  Proof. destruct p as [[]|]; apply _. Qed.

  Global Instance is_chan_contractive' ch : Contractive (is_chan' ch).
  Proof.
    apply (uPred.contractive_internal_eq (M:=iResUR Σ)). iIntros (p p') "#H".
    rewrite option_equivI.
    destruct p as [[p|]|], p' as [[p'|]|]; simpl; try done; try rewrite option_equivI.
    - by iApply f_equivI_contractive.
    - iApply prop_ext. iIntros "!>". iSplit; by iMod "H".
    - iApply prop_ext. iIntros "!>". iSplit; by iMod "H".
    - iApply prop_ext. iIntros "!>". iSplit; by iMod "H".
    - iApply prop_ext. iIntros "!>". iSplit; by iMod "H".
    - iApply prop_ext. iIntros "!>". iSplit; by iMod "H".
    - iApply prop_ext. iIntros "!>". iSplit; by iMod "H".
  Qed.
  Global Instance is_chan_ne' ch : NonExpansive (is_chan' ch).
  Proof. solve_proper. Qed.
  Global Instance is_chan_proper' ch : Proper ((≡) ==> (≡)) (is_chan' ch).
  Proof. solve_proper. Qed.

  Global Instance recv_prot_contractive' A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist_later n) ==> dist n) recv_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /recv_prot'.
    do 2 apply: Some_ne. apply: pair_ne; [done|]. intros v.
    do 6 f_equiv; [by repeat f_equiv..|].
    f_contractive. by rewrite Hpeq.
  Qed.
  Global Instance recv_prot_ne' A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==> dist n) recv_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /recv_prot'.
    do 2 apply: Some_ne. apply: pair_ne; [done|]. intros v. solve_proper.
  Qed.
  Global Instance recv_prot_proper' A :
    Proper (pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==> (≡)) recv_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /recv_prot'.
    do 2 apply: Some_proper. apply: pair_proper; [done|]. intros v. solve_proper.
  Qed.

  Global Instance send_prot_contractive' A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist_later n) ==> dist n) send_prot'.
  Proof. intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /send_prot'.
         apply dual_ne. apply recv_prot_contractive'; [done..|].
         f_equiv. destruct n; [by apply dist_later_0|]=> /=.
         specialize (Hpeq a). apply dist_later_S in Hpeq.
         apply dist_later_S. by repeat f_equiv.
  Qed.
  Global Instance send_prot_ne' A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==> dist n) send_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /send_prot'.
    do 2 apply: Some_proper. apply: pair_proper; [done|]. intros v. solve_proper.
  Qed.
  Global Instance send_prot_proper' A :
    Proper (pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==> (≡)) send_prot'.
  Proof.
    intros v1 v2 Hveq P1 P2 HPeq p1 p2 Hpeq. rewrite /send_prot'.
    do 2 apply: Some_proper. apply: pair_proper; [done|]. intros v. solve_proper.
  Qed.

  Definition is_prot (o : option $ option prot) : Prop := ∃ p, o = Some $ Some p.

  (* TODO: This proof could be improved *)
  Global Instance is_prot_proper : Proper ((≡) ==> (iff)) is_prot.
  Proof.
    intros p1 p2 Hpeq. rewrite /is_prot.
    rewrite equiv_option_Forall2 in Hpeq.
    inversion Hpeq as [?? Hpeq'|]; simplify_eq; split; eauto;
      inversion Hpeq'; simplify_eq; eauto.
  Qed.

  Lemma new_spec' p :
    is_prot p →
    {{{ True }}}
      new #()
    {{{ ch, RET ch; is_chan' ch p ∗ is_chan' ch (dual' p) }}}.
  Proof.
    iIntros ([p' Heq] Φ) "_ HΦ". iApply (new1_spec p'); [done|].
    iIntros "!>" (ch) "[Hch1 Hch2]". iApply "HΦ". rewrite Heq. by iFrame.
  Qed.

  Lemma recv_spec' {A} ch (v : A → val) Φ p :
    {{{ is_chan' ch (recv_prot' v Φ p) }}}
      recv ch
    {{{ x ch', RET (v x, ch'); is_chan' ch' (p x) ∗ Φ x }}}.
  Proof.
    iIntros (Ψ) "Hr HΨ". wp_apply (recv1_spec with "Hr").
    iIntros (ch') "(%x&%w&->&?&?)". iApply "HΨ". iFrame.
  Qed.

  Lemma send_spec' {A} x ch (v : A → val) Φ p :
    is_prot (p x) →
    {{{ is_chan' ch (send_prot' v Φ p) ∗ ▷ Φ x }}}
      send ch (v x)
    {{{ ch', RET ch'; is_chan' ch' (p x) }}}.
  Proof.
    iIntros ([p' Hpeq] Ψ) "[Hs HΦ] HΨ". wp_lam. wp_let.
    wp_smart_apply (new1_spec p' with "[//]").
    iIntros (ch') "[H1 H2]". wp_let. wp_smart_apply (send1_spec with "[$Hs HΦ H2]").
    - iExists _,_. iSplit; [done|]=>/=. rewrite Hpeq. by iFrame.
    - iIntros "_". wp_seq. iApply "HΨ". by rewrite Hpeq.
  Qed.

  Lemma send_close_spec' {A} x ch (v : A → val) Φ p :
    p x ≡ send_end_prot →
    {{{ is_chan' ch (send_prot' v Φ p) ∗ ▷ Φ x }}}
      send_close ch (v x)
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (Hp Ψ) "[Hs HΦ] HΨ". wp_lam. wp_let.
    wp_smart_apply (send1_spec with "[$Hs HΦ]").
    - simpl. iExists _,_. iSplit; first done. rewrite Hp. by iFrame.
    - iIntros "_". by iApply "HΨ".
  Qed.

  Lemma sym_close_spec' ch :
    {{{ is_chan' ch sym_end_prot }}}
      sym_close ch
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (Ψ) "(%γ1 & %γ2 & %l & >-> & #Hinv & >Htok) HΨ". wp_lam. wp_pures.
    wp_bind (CmpXchg _ _ _). iInv N as "[H|[[H1 H2]|>[H1 H2]]]".
    - wp_cmpxchg_suc. iModIntro. iSplitL "H Htok".
      + iModIntro. unfold end_inv. eauto with iFrame.
      + wp_pures. iModIntro. by iApply "HΨ".
    - wp_cmpxchg_fail. iModIntro. iSplitL "Htok H2".
      + iModIntro. unfold end_inv.
        iDestruct "H2" as "[H2|H2]"; last eauto with iFrame.
        iDestruct (own_valid_2 with "Htok H2") as %[].
      + wp_pures. wp_free. iModIntro. by iApply "HΨ".
    - iDestruct (own_valid_2 with "Htok H1") as %[].
  Qed.

  Lemma subprot_is_chan' ch p p' :
    ▷ subprot' p p' -∗ is_chan' ch p -∗ is_chan' ch p'.
  Proof.
    iIntros "Hsp ?".
    destruct p as [[]|], p' as [[]|]; simpl; try by iMod "Hsp".
    by iApply (subprot_is_chan with "[$]").
  Qed.

  Lemma subprot_dual' p1 p2 :
    subprot' (dual' p1) (dual' p2) ⊣⊢ subprot' p2 p1.
  Proof.
    destruct p1 as [[]|], p2 as [[]|]; rewrite //= subprot_dual //.
  Qed.

  Lemma subprot_refl' p : ⊢ subprot' p p.
  Proof. destruct p as [[]|]; [apply subprot_refl|done..]. Qed.

  Lemma subprot_end' : ⊢ subprot' None None.
  Proof. apply subprot_refl'. Qed.

  Lemma subprot_recv' {A1 A2} (v1 : A1 → val) (v2 : A2 → val) Φ1 Φ2 p1 p2 :
    (∀ x1, Φ1 x1 -∗ ∃ x2, ⌜v1 x1 = v2 x2⌝ ∗ Φ2 x2 ∗ ▷ subprot' (p1 x1) (p2 x2)) -∗
    subprot' (recv_prot' v1 Φ1 p1) (recv_prot' v2 Φ2 p2).
  Proof.
    iIntros "H". rewrite {2}/subprot' /subprot /=. iIntros "%v".
    iIntros "(%x1 & %ch & -> & HΦ1 & Hch)".
    iDestruct ("H" with "HΦ1") as (x2 Heq) "[H1 H2]".
    iExists _,_. iSplit; first rewrite Heq //. iFrame.
    by iApply (subprot_is_chan' with "[$]").
  Qed.

  Lemma subprot_send' {A1 A2} (v1 : A1 → val) (v2 : A2 → val) Φ1 Φ2 p1 p2 :
    (∀ x2, Φ2 x2 -∗ ∃ x1, ⌜v2 x2 = v1 x1⌝ ∗ Φ1 x1 ∗ ▷ subprot' (p1 x1) (p2 x2)) -∗
    subprot' (send_prot' v1 Φ1 p1) (send_prot' v2 Φ2 p2).
  Proof.
    iIntros "H". rewrite subprot_dual'.
    iApply subprot_recv'. simpl.
    by setoid_rewrite subprot_dual'.
  Qed.

  Lemma dual_dual' p : dual' (dual' p) = p.
  Proof. destruct p as [[p|]|]; [|done..]. by destruct p as [[] ?]. Qed.
  Lemma recv_prot_dual' {A} (v : A → val) Φ p :
    dual' (recv_prot' v Φ p) ≡ send_prot' v Φ (dual'∘p).
  Proof.
    rewrite /send_prot'. f_equiv. eapply recv_prot_proper'; intro; try done.
    by rewrite /= dual_dual'.
  Qed.
  Lemma send_prot_dual' {A} (v : A → val) Φ p :
    dual' (send_prot' v Φ p) ≡ recv_prot' v Φ (dual'∘p).
  Proof. done. Qed.

End close_proofs.

Section close_examples.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation prot := (prot Σ).

  Definition sum_reduce {A B C} (f1 : A → C) (f2 : B → C) (ab : A + B) : C :=
    match ab with
    | inl a => f1 a
    | inr b => f2 b
    end.

  Definition branch_prot' {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot') (p2 : B → prot') : prot' :=
    recv_prot' (sum_reduce v1 v2) (sum_reduce P1 P2) (sum_reduce p1 p2).

  Definition choice_prot' {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot') (p2 : B → prot') : prot' :=
    dual' $ branch_prot' v1 v2 P1 P2 (dual' ∘ p1) (dual' ∘ p2).

  Lemma subprot_choice_l' {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot') (p2 : B → prot') :
    ⊢ subprot' (choice_prot' v1 v2 P1 P2 p1 p2) (send_prot' v1 P1 p1).
  Proof.
    rewrite /choice_prot' /branch_prot' recv_prot_dual'.
    iApply subprot_send'.
    iIntros (a) "HP1".
    iExists (inl a).
    iSplit; [eauto|].
    iSplitL; [eauto|]=> /=. rewrite dual_dual'. iApply subprot_refl'.
  Qed.

  Lemma subprot_choice_r' {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot') (p2 : B → prot') :
    ⊢ subprot' (choice_prot' v1 v2 P1 P2 p1 p2) (send_prot' v2 P2 p2).
  Proof.
    rewrite /choice_prot' /branch_prot' recv_prot_dual'.
    iApply subprot_send'.
    iIntros (a) "HP1".
    iExists (inr a).
    iSplit; [eauto|].
    iSplitL; [eauto|]=> /=. rewrite dual_dual'. iApply subprot_refl'.
  Qed.

  Lemma subprot_branch_l' {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot') (p2 : B → prot') :
    ⊢ subprot' (recv_prot' v1 P1 p1) (branch_prot' v1 v2 P1 P2 p1 p2).
  Proof.
    iApply subprot_recv'.
    iIntros (a) "HP1".
    iExists (inl a).
    iSplit; [eauto|].
    iSplitL; [eauto|].
    iApply subprot_refl'.
  Qed.

  Lemma subprot_branch_r' {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot') (p2 : B → prot') :
    ⊢ subprot' (recv_prot' v2 P2 p2) (branch_prot' v1 v2 P1 P2 p1 p2).
  Proof.
    iApply subprot_recv'.
    iIntros (a) "HP1".
    iExists (inr a).
    iSplit; [eauto|].
    iSplitL; [eauto|].
    iApply subprot_refl'.
  Qed.

  Lemma branch_prot_dual {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot') (p2 : B → prot') :
    dual' $ branch_prot' v1 v2 P1 P2 p1 p2 ≡
    choice_prot' v1 v2 P1 P2 (dual' ∘ p1) (dual' ∘ p2).
  Proof.
    rewrite /branch_prot' /choice_prot'. f_equiv.
    apply recv_prot_proper'; [done..|].
    f_equiv. rewrite /sum_reduce. f_equiv=> /=; by rewrite dual_dual'.
  Qed.

  Lemma choice_prot_dual {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot') (p2 : B → prot') :
    dual' $ choice_prot' v1 v2 P1 P2 p1 p2 ≡
    branch_prot' v1 v2 P1 P2 (dual' ∘ p1) (dual' ∘ p2).
  Proof.
    rewrite /branch_prot' /choice_prot'. rewrite dual_dual'.
    apply recv_prot_proper'; [done..|]. f_equiv.
  Qed.

  Definition prog_add_rec : val :=
    λ: "<>",
      let: "c" := new #() in
      Fork ((rec: "go" "c" :=
             let: "r" := recv "c" in
             let: "v" := Fst "r" in
             let: "c" := Snd "r" in
             match: "v" with
               InjL "l" =>
                 "l" <- (!"l" + #2);;
                 let: "c" := send "c" #() in "go" "c"
             | InjR <> => #()
            end) "c");;
      let: "l" := ref #38 in
      let: "c" := send "c" (InjL "l") in
      let: "r" := recv "c" in
      let: "c" := Snd "r" in
      let: "c" := send "c" (InjL "l") in
      let: "r" := recv "c" in
      let: "c" := Snd "r" in
      send_close "c" (InjR #());; assert: (!"l" = #42).

  Definition prot_add_base p : prot' :=
    choice_prot' (λ (lx : loc * Z), InjLV #lx.1) (λ (_:unit), InjRV #())
                (λ lx, lx.1 ↦ #lx.2)%I (λ _, True)%I
                (λ lx, recv_prot' (λ (_:unit), #())
                                  (λ _, lx.1 ↦ #(lx.2 + 2))%I
                                  (λ _, p))
                (λ _, send_end_prot).

  Instance prot_add_base_contractive : Contractive prot_add_base.
  Proof.
    rewrite /prot_add_base.
    intros n p1 p2 Hpeq.
    rewrite /choice_prot' /branch_prot' /recv_prot_dual'. f_equiv.
    apply recv_prot_contractive'; [done..|].
    f_equiv. rewrite /sum_reduce. f_equiv.
    destruct n; [by apply dist_later_0|]=> /=.
    apply dist_later_S. f_equiv. f_equiv. f_equiv.
    apply: pair_ne; [done|]. intros r.
    apply dist_later_S in Hpeq. by repeat f_equiv.
  Qed.
  Definition prot_add_rec := fixpoint prot_add_base.

  Lemma prot_add_rec_unfold :
    prot_add_rec ≡ prot_add_base prot_add_rec.
  Proof. rewrite /prot_add_rec. apply fixpoint_unfold. Qed.

  Lemma prog_add_rec_spec :
    {{{ True }}}
      prog_add_rec #()
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_spec' prot_add_rec);
      [by rewrite prot_add_rec_unfold; rewrite /is_prot; by eauto|done|].
    iIntros (ch) "[Hch1 Hch2]".
    wp_smart_apply (wp_fork with "[Hch2]").
    - iIntros "!>". wp_pure _.
      iLöb as "IH" forall (ch).
      rewrite {2}prot_add_rec_unfold.
      rewrite choice_prot_dual.
      wp_smart_apply (recv_spec' with "Hch2").
      iIntros ([[l x]|] ch') "Hch2"=> /=.
      + iDestruct "Hch2" as "[Hch2 Hl]". wp_load. wp_store.
        rewrite /dual=> /=. rewrite -{2}(dual_dual' prot_add_rec).
        wp_smart_apply (send_spec' (():unit) _ (λ _, #()) (λ _, l ↦ #(x + 2))%I
                         with "[$Hch2 $Hl]").
        { rewrite prot_add_rec_unfold. rewrite /is_prot. by eauto. }
      iIntros (ch'') "Hch2". do 2 wp_pure. by iApply "IH".
      + wp_pures. done.
    - rewrite prot_add_rec_unfold.
      wp_alloc l as "Hl".
      iDestruct (subprot_is_chan' with "[] Hch1") as "Hch1".
      { iApply subprot_choice_l'. }
      wp_smart_apply (send_spec' (l,38%Z) with "[$Hch1 $Hl]").
      { rewrite /is_prot. by eauto. }
      iIntros (ch') "Hch1". wp_smart_apply (recv_spec' with "Hch1").
      iIntros (_ ch'') "[Hch1 Hl]"=> /=.
      replace #(38 + 2) with #40; last by do 2 f_equiv; lia.
      rewrite prot_add_rec_unfold.
      iDestruct (subprot_is_chan' with "[] Hch1") as "Hch1".
      { iApply subprot_choice_l'. }
      wp_smart_apply (send_spec' (l,40%Z) with "[$Hch1 $Hl]").
      { rewrite /is_prot. by eauto. }
      iIntros (ch''') "Hch1". wp_smart_apply (recv_spec' with "Hch1").
      iIntros (_ ?) "[Hch1 Hl]".
      rewrite prot_add_rec_unfold.
      iDestruct (subprot_is_chan' with "[] Hch1") as "Hch1".
      { iApply subprot_choice_r'. }
      wp_smart_apply (send_close_spec' (():unit) _ (λ _ : (), InjRV #())
                       with "[$Hch1]"); [done..|].
      iIntros "_".
      wp_smart_apply wp_assert. wp_load. wp_pures.
      replace #(40 + 2) with #42; last by do 2 f_equiv; lia.
      iModIntro. iSplit; [done|].
      iIntros "!>". by iApply "HΦ".
  Qed.

End close_examples.
