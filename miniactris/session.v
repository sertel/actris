From miniactris Require Export sub.
From iris.heap_lang.lib Require Import assert.

Definition new : val := new1.
Definition recv : val := recv1.
Definition send : val := λ: "l" "v",
  let: "l'" := new1 #() in
  send1 "l" ("v","l'");; "l'".
Definition wait : val := recv1.
Definition close : val := λ: "l", send1 "l" #().

Section session_proofs.
  Context `{!heapGS Σ, !chanG Σ}.

  Notation prot := (prot Σ).

  (* ?x <v> {P}. p *)
  Definition recv_prot {A} (v : A → val) (Φ : A → iPropO Σ) (p : A → prot) : prot :=
    (false, λ r, ∃ x ch', ⌜r = (v x, ch')%V⌝ ∗ Φ x ∗ is_chan ch' (p x))%I.
  (* !x <v> {P}. p *)
  Definition send_prot {A} (v : A → val) (Φ : A -d> iPropO Σ) (p : A → prot) : prot :=
    dual (recv_prot v Φ (dual ∘ p)).

  (* End? *)
  Definition wait_prot : prot := (false, λ r, ⌜r = #()⌝)%I.
  (* End! *)
  Definition close_prot : prot := dual wait_prot.

  Lemma new_spec p :
    {{{ True }}} new #() {{{ ch, RET ch; is_chan ch p ∗ is_chan ch (dual p) }}}.
  Proof. apply new1_spec. Qed.

  Lemma recv_spec {A} ch (v : A → val) Φ p :
    {{{ is_chan ch (recv_prot v Φ p) }}}
      recv ch
    {{{ x ch', RET (v x, ch'); is_chan ch' (p x) ∗ Φ x }}}.
  Proof.
    iIntros (Ψ) "Hr HΨ". wp_apply (recv1_spec with "Hr").
    iIntros (ch') "(%x&%w&->&?&?)". iApply "HΨ". iFrame.
  Qed.

  Lemma send_spec {A} x ch (v : A → val) Φ p :
    {{{ is_chan ch (send_prot v Φ p) ∗ ▷ Φ x }}}
      send ch (v x)
    {{{ ch', RET ch'; is_chan ch' (p x) }}}.
  Proof.
    iIntros (Ψ) "[Hs HΦ] HΨ". wp_lam. wp_smart_apply (new_spec (p x) with "[//]").
    iIntros (ch') "[H1 H2]". wp_smart_apply (send1_spec with "[$Hs HΦ H2]").
    - simpl. eauto with iFrame.
    - iIntros "_". wp_seq. by iApply "HΨ".
  Qed.

  Lemma wait_spec ch :
    {{{ is_chan ch wait_prot }}}
      wait ch
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (Ψ) "Hch HΨ". wp_apply (recv1_spec with "Hch").
    iIntros (v') "->". by iApply "HΨ".
  Qed.

  Lemma close_spec ch :
    {{{ is_chan ch close_prot }}}
      close ch
    {{{ RET #(); emp }}}.
  Proof.
    iIntros (Ψ) "Hch HΨ". wp_lam.
    wp_smart_apply (send1_spec with "[$Hch]"); eauto.
  Qed.

  Lemma subprot_recv {A1 A2} (v1 : A1 → val) (v2 : A2 → val) Φ1 Φ2 p1 p2 :
    (∀ x1, Φ1 x1 -∗ ∃ x2, ⌜v1 x1 = v2 x2⌝ ∗ Φ2 x2 ∗ ▷ subprot (p1 x1) (p2 x2)) -∗
    subprot (recv_prot v1 Φ1 p1) (recv_prot v2 Φ2 p2).
  Proof.
    (** FIXME: We are breaking the abstraction of subprot here *)
    rewrite {2}/subprot. iIntros "H" (v).
    iIntros "(%x1 & %ch & → & HΦ1 & Hch)".
    iDestruct ("H" with "HΦ1") as (x2 Heq) "[H1 H2]".
    iExists _,_. iSplit; first rewrite Heq //. iFrame.
    by iApply (subprot_is_chan with "[$]").
  Qed.

  Lemma subprot_send {A1 A2} (v1 : A1 → val) (v2 : A2 → val) Φ1 Φ2 p1 p2 :
    (∀ x2, Φ2 x2 -∗ ∃ x1, ⌜v2 x2 = v1 x1⌝ ∗ Φ1 x1 ∗ ▷ subprot (p1 x1) (p2 x2)) -∗
    subprot (send_prot v1 Φ1 p1) (send_prot v2 Φ2 p2).
  Proof.
    iIntros "H". rewrite subprot_dual. iApply subprot_recv.
    by setoid_rewrite subprot_dual.
  Qed.

  Lemma subprot_frame {A B} (v1 : A → val) (v2 : A → B → val) Φ1 Φ2 Ψ p :
    ⊢ subprot (send_prot v1 Φ1 (λ x1, recv_prot (v2 x1) (Φ2 x1) (p x1)))
              (send_prot v1 (λ x1, Φ1 x1 ∗ ▷ Ψ x1)%I (λ x1, recv_prot (v2 x1) (λ x2, Ψ x1 ∗ Φ2 x1 x2)%I (p x1))).
  Proof.
    iApply subprot_send. iIntros (x1) "[HΦ1 HΨ]".
    iExists x1. iSplit; first done. iSplitL "HΦ1"; first done.
    iApply subprot_recv. iModIntro. iIntros (x2) "HΦ2".
    iExists x2. iSplit; first done. iFrame.
    iApply subprot_refl.
  Qed.

  Lemma subprot_payload_elim_l {A} (v1 v2 : A → val) Φ1 Φ2 p1 p2 :
    (∀ x, Φ1 x -∗
          subprot (recv_prot (λ (_:unit), v1 x) (λ _, True) (λ _, p1 x))
                  (recv_prot v2 Φ2 p2)) -∗
    subprot (recv_prot v1 Φ1 p1) (recv_prot v2 Φ2 p2).
  Proof.
    iIntros "H". rewrite /subprot/=. iIntros (v).
    iDestruct 1 as (x c ->) "[HΦ Hc]". iApply ("H" with "HΦ [Hc]").
    by iExists (), c; eauto.
  Qed.

  Lemma subprot_payload_elim_r {A} (v1 v2 : A → val) Φ1 Φ2 p1 p2 :
    (∀ x, Φ2 x -∗
          subprot (send_prot v1 Φ1 p1)
                  (send_prot (λ (_:unit), v2 x) (λ _, True) (λ _, p2 x))) -∗
    subprot (send_prot v1 Φ1 p1) (send_prot v2 Φ2 p2).
  Proof.
    iIntros "H". rewrite /subprot/=. iIntros (v).
    iDestruct 1 as (x c ->) "[HΦ Hc]". iApply ("H" with "HΦ [Hc]").
    by iExists (), c; eauto.
  Qed.

  Global Instance recv_prot_contractive A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist_later n) ==> dist n) recv_prot.
  Proof.
    intros v1 v2 Hveq Φ1 Φ2 HΦeq p1 p2 Hpeq. rewrite /recv_prot.
    split; [done|]=> /= v. do 6 f_equiv; [by rewrite Hveq|done|].
    apply is_chan_contractive. apply Hpeq.
  Qed.
  Global Instance recv_prot_ne A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==> dist n) recv_prot.
  Proof.
    intros v1 v2 Hveq Φ1 Φ2 HΦeq p1 p2 Hpeq. rewrite /recv_prot.
    split; [done|]=> /= v. do 6 f_equiv; [by rewrite Hveq|done|].
    apply is_chan_ne. apply Hpeq.
  Qed.
  Global Instance recv_prot_proper A :
    Proper (pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==> (≡)) recv_prot.
  Proof.
    intros v1 v2 Hveq Φ1 Φ2 HΦeq p1 p2 Hpeq. rewrite /recv_prot.
    split; [done|]=> /= v. do 6 f_equiv; [by rewrite Hveq|done|].
    apply is_chan_proper. apply Hpeq.
  Qed.

  Global Instance send_prot_contractive A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist_later n) ==> dist n) send_prot.
  Proof.
    intros v1 v2 Hveq Φ1 Φ2 HΦeq p1 p2 Hpeq. rewrite /send_prot.
    f_equiv. split; [done|]=> /= v. do 6 f_equiv; [by rewrite Hveq|done|].
    f_contractive. f_equiv. by apply Hpeq.
  Qed.
  Global Instance send_prot_ne A n :
    Proper (pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==>
            pointwise_relation A (dist n) ==> dist n) send_prot.
  Proof.
    intros v1 v2 Hveq Φ1 Φ2 HΦeq p1 p2 Hpeq. rewrite /send_prot.
    f_equiv. split; [done|]=> /= v. do 6 f_equiv; [by rewrite Hveq|done|].
    apply is_chan_ne. by f_equiv.
  Qed.
  Global Instance send_prot_proper A :
    Proper (pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==>
            pointwise_relation A (≡) ==> (≡)) send_prot.
  Proof.
    intros v1 v2 Hveq Φ1 Φ2 HΦeq p1 p2 Hpeq. rewrite /send_prot.
    f_equiv. split; [done|]=> /= v. do 6 f_equiv; [by rewrite Hveq|done|].
    apply is_chan_proper. by f_equiv.
  Qed.

  Lemma wait_prot_dual : dual wait_prot ≡ close_prot.
  Proof. split; [done|]. by intros v. Qed.
  Lemma close_prot_dual : dual close_prot ≡ wait_prot.
  Proof. split; [done|]. by intros v. Qed.
  Lemma recv_prot_dual {A} (v : A → val) Φ p :
    dual (recv_prot v Φ p) ≡ send_prot v Φ (dual∘p).
  Proof.
    rewrite /send_prot. f_equiv. eapply recv_prot_proper; intro; try done.
    by rewrite /= dual_dual.
  Qed.
  Lemma send_prot_dual {A} (v : A → val) Φ p :
    dual (send_prot v Φ p) ≡ recv_prot v Φ (dual∘p).
  Proof. split; [done|]. intro. done. Qed.
End session_proofs.

Section session_examples.
  Context `{!heapGS Σ, !chanG Σ}.
  Notation prot := (prot Σ).

  Definition prot_add_base p : prot :=
    send_prot (λ (lx : loc * Z), #lx.1) (λ lx, lx.1 ↦ #lx.2)%I
      (λ lx, recv_prot (λ (_:unit), #()) (λ _, lx.1 ↦ #(lx.2 + 2))%I
                       (λ _, p)).

  Instance prot_add_base_contractive : Contractive prot_add_base.
  Proof.
    unfold prot_add_base.
    repeat intro. eapply send_prot_ne; try done.
    repeat intro. eapply recv_prot_contractive; try done.
    solve_proper.
  Qed.

  Definition prog_add : val :=
    λ: "<>",
      let: "c" := new #() in
      Fork (let: "r" := recv "c" in
            Fst "r" <- ((!(Fst "r") + #2));;
            let: "c" := send (Snd "r") #() in wait "c");;
      let: "l" := ref #40 in
      let: "c" := send "c" "l" in
      let: "r" := recv "c" in
      close (Snd "r");; assert: (!"l" = #42).

  Definition prot_add : prot := prot_add_base close_prot.

  Lemma prog_add_spec :
    {{{ True }}}
      prog_add #()
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_spec prot_add); [done|].
    iIntros (ch) "[Hch1 Hch2]".
    wp_smart_apply (wp_fork with "[Hch2]").
    - iIntros "!>". wp_smart_apply (recv_spec with "Hch2").
      iIntros ([l x] ch') "[Hch2 Hl]"=> /=. rewrite recv_prot_dual.
      wp_load. wp_store. wp_smart_apply (send_spec () with "[$Hch2 $Hl]").
      iIntros (ch'') "Hch2". by wp_smart_apply (wait_spec with "Hch2").
    - wp_alloc l as "Hl". wp_smart_apply (send_spec (l,40%Z) with "[$Hch1 $Hl]").
      iIntros (ch') "Hch1". wp_smart_apply (recv_spec with "Hch1").
      iIntros (_ ?) "[Hch1 Hl]". wp_smart_apply (close_spec with "Hch1").
      iIntros "_". wp_smart_apply wp_assert. wp_load. wp_pures.
      iModIntro. iSplit; [done|]. by iApply "HΦ".
  Qed.

  Definition prog_add_rec : val :=
    λ: "<>",
      let: "c" := new #() in
      Fork ((rec: "go" "c" :=
             let: "r" := recv "c" in
             Fst "r" <- ((!(Fst "r") + #2));;
             let: "c" := send (Snd "r") #() in "go" "c") "c");;
      let: "l" := ref #38 in
      let: "c" := send "c" "l" in
      let: "r" := recv "c" in
      let: "c" := send (Snd "r") "l" in
      let: "r" := recv "c" in
      assert: (!"l" = #42);; Snd "r".

  Definition prot_add_rec := fixpoint prot_add_base.

  Lemma prot_add_rec_unfold :
    prot_add_rec ≡ prot_add_base prot_add_rec.
  Proof. rewrite /prot_add_rec. apply fixpoint_unfold. Qed.

  Lemma prog_add_rec_spec :
    {{{ True }}}
      prog_add_rec #()
    {{{ c, RET c; is_chan c prot_add_rec }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    wp_smart_apply (new_spec prot_add_rec); [done|].
    iIntros (ch) "[Hch1 Hch2]".
    wp_smart_apply (wp_fork with "[Hch2]").
    - iIntros "!>". wp_pure _.
      iLöb as "IH" forall (ch).
      rewrite {2}prot_add_rec_unfold.
      wp_smart_apply (recv_spec with "Hch2").
      iIntros ([l x] ch') "[Hch2 Hl]"=> /=. rewrite recv_prot_dual.
      wp_load. wp_store. wp_smart_apply (send_spec () with "[$Hch2 $Hl]").
      iIntros (ch'') "Hch2". do 2 wp_pure. by iApply "IH".
    - rewrite {2}prot_add_rec_unfold.
      wp_alloc l as "Hl". wp_smart_apply (send_spec (l,38%Z) with "[$Hch1 $Hl]").
      iIntros (ch') "Hch1". wp_smart_apply (recv_spec with "Hch1").
      iIntros (_ ch'') "[Hch1 Hl]"=> /=.
      replace #(38 + 2) with #40; last by do 2 f_equiv; lia.
      rewrite {2}prot_add_rec_unfold.
      wp_smart_apply (send_spec (l,40%Z) with "[$Hch1 $Hl]").
      iIntros (ch''') "Hch1". wp_smart_apply (recv_spec with "Hch1").
      iIntros (_ ?) "[Hch1 Hl]". wp_smart_apply wp_assert. wp_load. wp_pures.
      replace #(40 + 2) with #42; last by do 2 f_equiv; lia.
      iModIntro. iSplit; [done|].
      iIntros "!>". wp_pures. by iApply "HΦ".
  Qed.

  Definition sum_reduce {A B C} (f1 : A → C) (f2 : B → C) (ab : A + B) : C :=
    match ab with
    | inl a => f1 a
    | inr b => f2 b
    end.

  Definition choice_prot {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot) (p2 : B → prot) : prot :=
    send_prot (sum_reduce v1 v2) (sum_reduce P1 P2) (sum_reduce p1 p2).

  Definition branch_prot {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot) (p2 : B → prot) : prot :=
    dual $ choice_prot v1 v2 P1 P2 (dual ∘ p1) (dual ∘ p2).

  Lemma subprot_choice_l {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot) (p2 : B → prot) :
    ⊢ subprot (choice_prot v1 v2 P1 P2 p1 p2) (send_prot v1 P1 p1).
  Proof.
    iApply subprot_send.
    iIntros (a) "HP1".
    iExists (inl a).
    iSplit; [eauto|].
    iSplitL; [eauto|].
    iApply subprot_refl.
  Qed.

  Lemma subprot_choice_r {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot) (p2 : B → prot) :
    ⊢ subprot (choice_prot v1 v2 P1 P2 p1 p2) (send_prot v2 P2 p2).
  Proof.
    iApply subprot_send.
    iIntros (a) "HP1".
    iExists (inr a).
    iSplit; [eauto|].
    iSplitL; [eauto|].
    iApply subprot_refl.
  Qed.

  Lemma subprot_branch_l {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot) (p2 : B → prot) :
    ⊢ subprot (recv_prot v1 P1 p1) (branch_prot v1 v2 P1 P2 p1 p2).
  Proof.
    iApply subprot_recv.
    iIntros (a) "HP1".
    iExists (inl a).
    iSplit; [eauto|].
    iSplitL; [eauto|]=> /=. rewrite dual_dual.
    iApply subprot_refl.
  Qed.

  Lemma subprot_branch_r {A B : Type}
             (v1 : A → val) (v2 : B → val)
             (P1 : A → iProp Σ) (P2 : B → iProp Σ)
             (p1 : A → prot) (p2 : B → prot) :
    ⊢ subprot (recv_prot v2 P2 p2) (branch_prot v1 v2 P1 P2 p1 p2).
  Proof.
    iApply subprot_recv.
    iIntros (a) "HP1".
    iExists (inr a).
    iSplit; [eauto|].
    iSplitL; [eauto|]=> /=. rewrite dual_dual.
    iApply subprot_refl.
  Qed.

  Definition my_prot_ex_1 p1 p2 : prot :=
    choice_prot (λ (b:bool), #b) (λ i:Z, #i) (λ _, True)%I (λ _, True)%I p1 p2.

  Definition my_prot_ex_2 p : prot :=
    send_prot (λ (b : bool), #b) (λ b, True)%I (λ b, p).

  Lemma subprot_example p1 p2 :
    ⊢ subprot (my_prot_ex_1 (λ _, p1) p2) (my_prot_ex_2 p1).
  Proof. by iApply subprot_choice_l. Qed.

End session_examples.
