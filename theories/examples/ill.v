From stdpp Require Import gmap fin_maps fin_sets stringmap.
From actris.channel Require Import proofmode.
From actris.utils Require Import syntax_facts.

Section big_op_lemma.
Context `{Countable K, !heapG Σ}.

Local Lemma owohelper {A B} (Φ : K → A → B → iProp Σ)
      (m1 m2 : gmap K A) :
  ∀ (n : gmap K B) ,
   m1 ##ₘ m2 →
    ([∗ map] k↦x;y ∈ (m1 ∪ m2);n, Φ k x y)
      ⊢ ∃ n1 n2, ⌜n = n1 ∪ n2⌝ ∗ ([∗ map] k↦x;y ∈ m1;n1, Φ k x y) ∗ ([∗ map] k↦x;y ∈ m2;n2, Φ k x y).
Proof.
  pose (P := λ m1,
    ∀ (m2 : gmap K A) (n : gmap K B),
      m1 ##ₘ m2 →
    ([∗ map] k↦x;y ∈ (m1 ∪ m2);n, Φ k x y)
      -∗ ∃ n1 n2 : gmap K B,
           ⌜n = n1 ∪ n2⌝
           ∗ ([∗ map] k↦x;y ∈ m1;n1, Φ k x y) ∗ ([∗ map] k↦x;y ∈ m2;n2, Φ k x y)).
  revert m1 m2. eapply (map_ind P); unfold P; clear P.
  { intros m2 n ?.
    rewrite left_id. iIntros "H".
    iExists ∅,n. rewrite left_id big_sepM2_empty.
    repeat iSplit; eauto. }
  intros i x m1 Hm1 IH m2 n [Hm2i Hmm]%map_disjoint_insert_l.
  iIntros "H".
  iAssert (⌜dom (gset K) n = {[i]} ∪ dom (gset K) m1 ∪ dom (gset K) m2⌝)%I as %Hdomn.
  { rewrite big_sepM2_dom. rewrite dom_union_L dom_insert_L.
    iDestruct "H" as %Hfoo. iPureIntro. symmetry. done. }

  destruct (n !! i) as [y|] eqn:Hni; last first.
  { exfalso. eapply (not_elem_of_dom n i); eauto.
    set_solver. }

  assert (n = <[i:=y]>(delete i n)) as ->.
  { by rewrite insert_delete insert_id//. }

  assert ((m1 ∪ m2) !! i = None) as Hm1m2i.
  { eapply lookup_union_None; naive_solver. }

  assert (delete i n !! i = None) by eapply lookup_delete.

  rewrite -insert_union_l.
  rewrite big_sepM2_insert; eauto.
  iDestruct "H" as "[H1 H2]".
  rewrite (IH m2 (delete i n)); eauto.
  iDestruct "H2" as (n1 n2 Hn12) "[H2 H3]".
  iExists (<[i:=y]>n1), n2. iFrame "H3".
  iAssert (⌜n1 !! i = None⌝)%I as %Hn1i.
  { rewrite big_sepM2_dom.
    iDestruct "H2" as %Hfoo. iPureIntro.
    eapply not_elem_of_dom. rewrite -Hfoo.
    by eapply not_elem_of_dom. }
  rewrite big_sepM2_insert//. iFrame "H1 H2".
  iPureIntro. rewrite -insert_union_l.
  by f_equiv.
Qed.


Lemma big_sepM2_union_l {A B} (Φ : K → A → B → iProp Σ)
      (m1 m2 : gmap K A) (n : gmap K B) :
  m1 ##ₘ m2 →
  ([∗ map] k↦x;y ∈ (m1 ∪ m2);n, Φ k x y) ⊢
  (∃ n1 n2, ⌜n1 ##ₘ n2⌝ ∗ ⌜n = n1 ∪ n2⌝
                        ∗ ([∗ map] k↦x;y ∈ m1;n1, Φ k x y)
                        ∗ ([∗ map] k↦x;y ∈ m2;n2, Φ k x y)).
Proof.
  intros Hmm. rewrite owohelper; eauto.
  iDestruct 1 as (n1 n2 ->) "[H1 H2]".
  iExists n1, n2.
  iAssert (⌜dom (gset K) m1 = dom (gset K) n1⌝)%I as %Hdom1.
  { by rewrite (big_sepM2_dom _ m1). }
  iAssert (⌜dom (gset K) m2 = dom (gset K) n2⌝)%I as %Hdom2.
  { by rewrite (big_sepM2_dom _ m2). }
  iFrame "H1 H2". iSplit; eauto. iPureIntro.
  eapply map_disjoint_dom_2.
  rewrite -Hdom1 -Hdom2.
  by eapply map_disjoint_dom_1.
Qed.

End big_op_lemma.

Inductive ty :=
| tone : ty
| totimes : ty -> ty -> ty
| toplus : ty → ty → ty
| twith : ty → ty → ty
| tlolli : ty -> ty -> ty
.

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with ty.
Notation "1" := tone : FType_scope.
Infix "⊕" := toplus (at level 11, right associativity) : FType_scope.
Infix "⊗" := totimes (at level 11, right associativity) : FType_scope.
Infix "&" := twith (at level 11, right associativity) : FType_scope.
Infix "⊸" := tlolli (at level 11, right associativity) : FType_scope.

Section interp.
Context `{!heapG Σ, !chanG Σ}.

Fixpoint interp_ty (τ : ty) : iProto Σ :=
  match τ with
  | 1%ty => (<!> MSG #(); END)%proto
  | (τ1 ⊗ τ2)%ty => (<! c> MSG c {{ ▷ c ↣ iProto_dual (interp_ty τ1) }}; interp_ty τ2)%proto
  | (τ1 ⊕ τ2)%ty => iProto_choice Send True True (interp_ty τ1) (interp_ty τ2)
  | (τ1 & τ2)%ty => iProto_choice Recv True True (interp_ty τ1) (interp_ty τ2)
  | (τ1 ⊸ τ2)%ty => (<? c> MSG c {{ ▷ c ↣ iProto_dual (interp_ty τ1) }}; interp_ty τ2)%proto
  end.

Arguments interp_ty τ%ty.

Definition tyctx := gmap string ty.
Definition interp_seq (Δ : tyctx) (e : expr) (x : string) (τ : ty) : iProp Σ :=
  ∀ (cs : gmap string val) (* substitution map *)
    (o : val),    (* "output" channel *)
    ([∗ map] x ↦ σ;c ∈ Δ;cs, c ↣ iProto_dual (interp_ty σ)) -∗
  o ↣ interp_ty τ -∗
  WP (subst_map (<[x:=o]>cs) e) {{ _, o ↣ END (* ∗ ([∗ map] x ↦ σ;c ∈ Δ;cs, c ↣ END) *) }}%I.

Notation "Δ '⊢ₗ' P ':' '(' c ':' τ ')'" := (interp_seq Δ%ty P c τ%ty) (at level 74, P, c, τ at next level).

(* Attempt to prove that [cs2 !! y = None] *)
Ltac assert_not_in_map cs2 y :=
  assert (cs2 !! y = None);
  first (eapply not_elem_of_dom;
         repeat match goal with
         | [ H : _ = dom _ cs2 |- _ ] => rewrite -H
         | [ H : dom _ cs2 = _ |- _ ] => rewrite H
         | [ H : ?Δ !! y = None |- context[dom stringset ?Δ] ] =>
           eapply not_elem_of_dom in H
         end;
         try set_solver); eauto.

Ltac assert_in_map_ cs y yv Hyv :=
  assert (is_Some (cs !! y)) as [yv Hyv];
  first (eapply elem_of_dom;
         repeat match goal with
         | [ H : _ = dom _ cs |- _ ] => rewrite -H
         | [ H : dom _ cs = _ |- _ ] => rewrite H
         | [ H : ?Δ !! y = None |- context[dom stringset ?Δ] ] =>
           eapply not_elem_of_dom in H
         end; try set_solver).

Ltac assert_in_map cs y :=
  let yv := fresh "y" in let Hyv := fresh "Hy" in
  assert_in_map_ cs y yv Hyv.

Lemma cut_ Δ1 Δ2 (x y : string) τ1 τ2 e1 e2 :
  x ≠ y →
  Δ1 !! y = None →
  Δ2 !! y = None →
  Δ1 ##ₘ Δ2 →
  is_closed_expr_set ({[x]} ∪ dom _ Δ1) e1 →
  is_closed_expr_set ({[x;y]} ∪ dom _ Δ2) e2 →
  (Δ1 ⊢ₗ e1 : (x : τ1)) -∗
  ((<[x:=τ1]>Δ2) ⊢ₗ e2 : (y : τ2)) -∗
  (Δ1 ∪ Δ2 ⊢ₗ (let: x := start_chan (λ: x, e1) in e2) : (y : τ2)).
Proof.
  intros Hxy Hy1 Hy2 HΔ Hclosed1 Hclosed2. iIntros "H1 H2".
  iIntros (cs oy) "HΔ Hoy". simpl.
  rewrite big_sepM2_union_l //.
  iDestruct "HΔ" as (cs1 cs2 Hcs ->) "[HΔ HΔ']".
  iAssert (⌜dom stringset Δ1 = dom stringset cs1⌝)%I as %Hdom1.
  { by rewrite big_sepM2_dom. }
  iAssert (⌜dom stringset Δ2 = dom stringset cs2⌝)%I as %Hdom2.
  { by rewrite (big_sepM2_dom _ Δ2). }

  assert_not_in_map cs1 y.
  assert_not_in_map cs2 y.

  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[H1 HΔ]").
  { iNext. iIntros (c) "Hc".
    rewrite iProto_dual_involutive. wp_pures.
    iSpecialize ("H1" with "HΔ Hc").
    rewrite -subst_map_insert.
    - assert (subst_map (<[x:=c]> cs1) e1
              = subst_map (<[x:=c]> (<[y:=oy]> (cs1 ∪ cs2))) e1) as ->.
      { eapply subst_map_agree_weaken; eauto.
        - by rewrite Hdom1 dom_insert_L.
        - eapply insert_mono.
          rewrite insert_union_l. etrans; last eapply map_union_subseteq_l.
          eapply insert_subseteq.
          eapply not_elem_of_dom. rewrite -Hdom1.
          by eapply not_elem_of_dom. }
      iApply (wp_wand with "H1"). eauto. }
  iIntros (xc) "Hx". wp_pures.
  iSpecialize ("H2" $! (<[x:=xc]>cs2) with "[HΔ' Hx] Hoy").
  { iApply (big_sepM2_insert_2 with "[Hx]"); eauto. }
  rewrite -subst_map_insert.
  cut (subst_map (<[y:=oy]> (<[x:=xc]> cs2)) e2
       = subst_map (<[x:=xc]> (<[y:=oy]> (cs1 ∪ cs2))) e2); first by intros ->.
  rewrite insert_commute//.
  eapply subst_map_fact_2; eauto.
  by rewrite -Hdom2.
Qed.

Lemma tone_right (x : string) :
  (⊢ ∅ ⊢ₗ send (Var x) #() : (x : 1)).
Proof.
  iIntros (vs o) "Hemp Ho". wp_pures.
  rewrite big_sepM2_empty_r. iDestruct "Hemp" as "->".
  rewrite lookup_insert /=.
  wp_send with "[]"; eauto with iFrame.
Qed.

Lemma tone_left (x y : string) e Δ τ  :
  x ≠ y →
  Δ !! y = None →
  is_closed_expr_set ({[x]} ∪ dom _ Δ) e →
  (Δ ⊢ₗ e : (x : τ)) -∗
  (<[y:=1]>Δ) ⊢ₗ (recv y;; e) : (x : τ).
Proof.
  iIntros (Hxy HΔ Hdome) "IH".
  iIntros (cs o) "Hcs Ho". simpl.
  rewrite lookup_insert_ne//.
  iAssert (⌜dom stringset (<[y:=1%ty]>Δ) = dom stringset cs⌝)%I as %Hdom1.
  { by rewrite big_sepM2_dom. }

  assert_in_map_ cs y cy Hcy.

  assert (cs = <[y:=cy]>(delete y cs)) as ->.
  { by rewrite insert_delete insert_id//. }
  rewrite big_sepM2_insert; eauto; last first.
  { eapply lookup_delete. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  rewrite lookup_insert.
  wp_recv as "_". wp_pures.
  iSpecialize ("IH" $! (delete y cs) with "Hcs Ho").
  cut (subst_map (<[x:=o]> (delete y cs)) e
       = subst_map (<[x:=o]> (<[y:=cy]> (delete y cs))) e); first by intros ->.
  eapply subst_map_agree_weaken; eauto.
  { assert (y ∉ dom stringset Δ).
    { by eapply not_elem_of_dom. }
    set_unfold. naive_solver. }
  eapply insert_mono. eapply insert_subseteq.
  eapply lookup_delete.
Qed.

Lemma tlolli_right (Δ : tyctx) τ1 τ2 e (x y : string) :
  x ≠ y →
  Δ !! x = None →
  Δ !! y = None →
  ((<[x:=τ1]>Δ) ⊢ₗ e : (y : τ2)) -∗
  Δ ⊢ₗ (let: x := recv y in e) : (y : τ1 ⊸ τ2).
Proof.
  intros Hxy Hx Hy. iIntros "H".
  iIntros (cs oy) "HΔ Hoy". wp_pures.
  rewrite lookup_insert.
  iSimpl in "Hoy".
  wp_recv (cx) as "Hx". wp_pures.
  rewrite -subst_map_insert.
  iSpecialize ("H" $! (<[x:=cx]>cs) with "[Hx HΔ] Hoy").
  { iApply (big_sepM2_insert_2 with "[Hx] HΔ"); simpl; eauto. }
  rewrite insert_commute//.
Qed.

Lemma tlolli_left (Δ Δ' : tyctx) τ1 τ2 e1 e2 σ (x y z : string) :
  x ≠ y →
  x ≠ z →
  y ≠ z →
  Δ !! x = None →
  Δ' !! x = None →
  Δ !! y = None →
  Δ' !! y = None →
  Δ !! z = None →
  Δ' !! z = None →
  Δ ##ₘ Δ' →
  is_closed_expr_set ({[y]} ∪ dom stringset Δ') e1 →
  is_closed_expr_set ({[x;z]} ∪ dom stringset Δ) e2 →
  (Δ' ⊢ₗ e1 : (y : τ1)) -∗
  (<[x:=τ2]>Δ ⊢ₗ e2 : (z : σ)) -∗
  ((<[x:=τ1 ⊸ τ2]>Δ) ∪ Δ' ⊢ₗ (let: y := start_chan (λ: y, e1) in send x y;; e2) : (z : σ)).
Proof.
  intros Hxy Hxz Hyz Hx Hx' Hy Hy' Hz Hz' HΔ He1 He2. iIntros "H1 H2".
  iIntros (cs o) "Hcs Ho". simpl.
  rewrite lookup_delete.
  rewrite !lookup_delete_ne//.
  rewrite lookup_insert_ne//.

  rewrite big_sepM2_union_l //; last first.
  { by eapply map_disjoint_insert_l_2. }
  iDestruct "Hcs" as (cs1 cs2 Hcs' ->) "[HΔ HΔ']".
  iAssert (⌜{[x]} ∪ dom stringset Δ = dom stringset cs1⌝)%I as %Hdom1.
  { rewrite (big_sepM2_dom _ _ cs1). iDestruct "HΔ" as %Hfoo.
    iPureIntro. revert Hfoo. rewrite dom_insert_L. done. }
  iAssert (⌜dom stringset Δ' = dom stringset cs2⌝)%I as %Hdom2.
  { by rewrite (big_sepM2_dom _ _ cs2). }


  assert_in_map cs1 x.

  assert_not_in_map cs1 y.
  assert_not_in_map cs2 y.

  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[H1 HΔ']").
  { iNext. iIntros (c) "Hc".
    rewrite iProto_dual_involutive. wp_pures.
    iSpecialize ("H1" with "HΔ' Hc").
    rewrite -subst_map_insert.
    cut (subst_map (<[y:=c]> cs2) e1
         = subst_map (<[y:=c]> (<[z:=o]> (cs1 ∪ cs2))) e1); first intros ->.
    { iApply (wp_wand with "H1"); eauto. }
    eapply subst_map_fact_1; eauto.
    - by rewrite -Hdom2.
    - eapply not_elem_of_dom. rewrite -Hdom1.
      eapply not_elem_of_dom in Hz.
      set_solver.
    - eapply not_elem_of_dom. rewrite -Hdom2.
      by eapply not_elem_of_dom. }

  iIntros (yc) "Hy". wp_pures.
  case_decide; last naive_solver.
  rewrite (lookup_union_Some_l _ _ x y0) //.
  rewrite big_sepM2_insert_acc //; last first.
  { eapply lookup_insert. }
  iDestruct "HΔ" as "[Hx Hcs]".
  simpl.

  wp_send with "[$Hy]". wp_pures.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert (insert_id cs1)//.
  iSpecialize ("H2" with "Hcs Ho").
  rewrite -subst_map_insert. rewrite insert_commute//.
  cut (subst_map (<[z:=o]> cs1) e2
       = subst_map (<[z:=o]> (<[y:=yc]> (cs1 ∪ cs2))) e2); first by intros ->.
  eapply subst_map_fact_0; eauto.
  rewrite -Hdom1. rewrite union_assoc_L. by rewrite (union_comm_L {[z]}).
Qed.


Lemma twith_right Δ τ1 τ2 e1 e2 (x : string) :
  Δ !! x = None →
  (Δ ⊢ₗ e1 : (x : τ1)) -∗
  (Δ ⊢ₗ e2 : (x : τ2)) -∗
  Δ ⊢ₗ (if: recv x then e1 else e2) : (x : τ1 & τ2).
Proof.
  intros Hx. iIntros "H1 H2". iIntros (cs ox) "Hcs Hx /=".
  rewrite lookup_insert.
  wp_branch; wp_pures.
  - iApply ("H1" with "Hcs Hx").
  - iApply ("H2" with "Hcs Hx").
Qed.

Lemma twith_left_1 Δ τ1 τ2 e (x y : string) σ :
  x ≠ y →
  Δ !! x = None →
  (<[x:=τ1]>Δ ⊢ₗ e : (y : σ)) -∗
  <[x:=τ1 & τ2]>Δ ⊢ₗ (send x #true;; e) : (y : σ).
Proof.
  intros Hxy HΔ. iIntros "H".
  iIntros (cs oy) "Hcs Hy /=".
  iAssert (⌜{[x]} ∪ dom stringset Δ = dom stringset cs⌝)%I as %Hdom.
  { by rewrite big_sepM2_dom dom_insert_L. }
  assert_in_map_ cs x xv Hxv.
  rewrite lookup_insert_ne// Hxv.
  rewrite big_sepM2_insert_acc; eauto; last first.
  { eapply lookup_insert. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_select. wp_pures.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert // (insert_id cs)//.
  iApply ("H"  with "Hcs Hy").
Qed.

Lemma twith_left_2 Δ τ1 τ2 e (x y : string) σ :
  x ≠ y →
  Δ !! x = None →
  (<[x:=τ2]>Δ ⊢ₗ e : (y : σ)) -∗
  <[x:=τ1 & τ2]>Δ ⊢ₗ (send x #false;; e) : (y : σ).
Proof.
  intros Hxy HΔ. iIntros "H".
  iIntros (cs oy) "Hcs Hy /=".
  iAssert (⌜{[x]} ∪ dom stringset Δ = dom stringset cs⌝)%I as %Hdom.
  { by rewrite big_sepM2_dom dom_insert_L. }
  assert_in_map_ cs x xv Hxv.
  rewrite lookup_insert_ne// Hxv.
  rewrite big_sepM2_insert_acc; eauto; last first.
  { eapply lookup_insert. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_select. wp_pures.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert // (insert_id cs)//.
  iApply ("H"  with "Hcs Hy").
Qed.

Lemma tplus_right_1 Δ τ1 τ2 e (x : string) :
  Δ !! x = None →
  (Δ ⊢ₗ e : (x : τ1)) -∗
  Δ ⊢ₗ (send x #true;; e) : (x : τ1 ⊕ τ2).
Proof.
  intros Hx. iIntros "H1". iIntros (cs ox) "Hcs Hx /=".
  rewrite lookup_insert.
  wp_select. wp_pures.
  iApply ("H1" with "Hcs Hx").
Qed.

Lemma tplus_right_2 Δ τ1 τ2 e (x : string) :
  Δ !! x = None →
  (Δ ⊢ₗ e : (x : τ2)) -∗
  Δ ⊢ₗ (send x #false;; e) : (x : τ1 ⊕ τ2).
Proof.
  intros Hx. iIntros "H1". iIntros (cs ox) "Hcs Hx /=".
  rewrite lookup_insert.
  wp_select. wp_pures.
  iApply ("H1" with "Hcs Hx").
Qed.

Lemma tplus_left Δ τ1 τ2 e1 e2 (x y : string) σ :
  x ≠ y →
  Δ !! x = None →
  (<[x:=τ1]>Δ ⊢ₗ e1 : (y : σ)) -∗
  (<[x:=τ2]>Δ ⊢ₗ e2 : (y : σ)) -∗
  <[x:=τ1⊕τ2]>Δ ⊢ₗ (if: recv x then e1 else e2) : (y : σ).
Proof.
  intros Hxy HΔ. iIntros "He1 He2".
  iIntros (cs oy) "Hcs Hy /=".
  iAssert (⌜{[x]} ∪ dom stringset Δ = dom stringset cs⌝)%I as %Hdom.
  { by rewrite big_sepM2_dom dom_insert_L. }
  assert_in_map_ cs x xv Hxv.
  rewrite lookup_insert_ne// Hxv.
  rewrite big_sepM2_insert_acc; eauto; last first.
  { eapply lookup_insert. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_branch; wp_pures.
  - iSpecialize ("Hcs" with "Hx").
    rewrite insert_insert (insert_id cs) //.
    iApply ("He1" with "Hcs Hy").
  - iSpecialize ("Hcs" with "Hx").
    rewrite insert_insert (insert_id cs) //.
    iApply ("He2" with "Hcs Hy").
Qed.

Lemma ttimes_right (Δ Δ' : tyctx) τ1 τ2 e e' (x y : string) :
  x ≠ y →
  Δ ##ₘ Δ' →
  Δ !! y = None →
  Δ' !! y = None →
  Δ !! x = None →
  Δ' !! x = None →
  is_closed_expr_set ({[x]} ∪ dom stringset Δ) e →
  is_closed_expr_set ({[y]} ∪ dom stringset Δ') e' →
  (Δ ⊢ₗ e : (x : τ1)) -∗
  (Δ' ⊢ₗ e' : (y : τ2)) -∗
  (Δ ∪ Δ' ⊢ₗ (let: x := start_chan (λ: x, e) in
              send y x;;
              e') : (y : τ1 ⊗ τ2)).
Proof.
  intros Hxy HΔ Hy1 Hy2 Hx1 Hx2 Hcle Hcle'. iIntros "H1 H2".
  iIntros (cs oy) "HΔ Hoy". wp_pures.
  rewrite lookup_delete_ne// !lookup_delete lookup_insert.
  simpl.
  rewrite big_sepM2_union_l //.
  iDestruct "HΔ" as (cs1 cs2 Hcs ->) "[HΔ HΔ']".

  iAssert (⌜dom stringset Δ = dom stringset cs1⌝)%I as %Hdom1.
  { by rewrite big_sepM2_dom. }
  iAssert (⌜dom stringset Δ' = dom stringset cs2⌝)%I as %Hdom2.
  { by rewrite (big_sepM2_dom _ Δ'). }
  assert_not_in_map cs1 y.
  assert_not_in_map cs2 y.
  assert_not_in_map cs1 x.
  assert_not_in_map cs2 x.

  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[H1 HΔ]").
  { iNext. iIntros (c) "Hc".
    rewrite iProto_dual_involutive. wp_pures.
    iSpecialize ("H1" with "HΔ Hc").
    rewrite -subst_map_insert.
    assert (subst_map (<[x:=c]> cs1) e
         = subst_map (<[x:=c]> (<[y:=oy]> (cs1 ∪ cs2))) e) as ->.
    { eapply subst_map_fact_0; eauto.
      by rewrite -Hdom1. }
    iApply (wp_wand with "H1"); eauto. }
  iIntros (xc) "Hxc". wp_pures.
  case_decide; last naive_solver.
  wp_send with "[$Hxc]". wp_pures.
  iSpecialize ("H2" with "HΔ' Hoy").
  rewrite -subst_map_insert. rewrite insert_commute //.
  rewrite -(subst_map_fact_1 cs1 cs2 y x)//.
  by rewrite -Hdom2.
Qed.

Lemma ttimes_left (Δ : tyctx) τ1 τ2 (x y : string) (c : string) σ e :
  x ≠ y →
  x ≠ c →
  y ≠ c →
  Δ !! x = None →
  Δ !! y = None →
  ((<[y:=τ1]>(<[x:=τ2]>Δ)) ⊢ₗ e : (c : σ)) -∗
  ((<[x:=τ1 ⊗ τ2]>Δ) ⊢ₗ (let: y := recv x in e) : (c : σ)).
Proof.
  intros Hxy Hxc Hyc Hx Hy. iIntros "IH".
  iIntros (cs o) "Hcs Ho". simpl.
  rewrite lookup_insert_ne//.

  iAssert (⌜{[x]} ∪ dom stringset Δ = dom stringset cs⌝)%I as %Hdom.
  { by rewrite (big_sepM2_dom _ _ cs) dom_insert_L. }

  assert_in_map_ cs x cx Hcx. rewrite Hcx.
  assert_not_in_map cs y.
  rewrite big_sepM2_insert_acc; eauto; last first.
  { eapply lookup_insert. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_recv (cy) as "Hy". wp_pures.
  rewrite -subst_map_insert.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert (insert_id cs) //.
  iSpecialize ("IH" $! (<[y:=cy]>(map_insert x cx cs)) with "[Hcs Hy] Ho").
  { iApply big_sepM2_insert.
    - rewrite lookup_insert_ne//.
    - replace (map_insert x cx cs) with (<[x:=cx]>cs) by reflexivity.
      rewrite lookup_insert_ne//.
    - iFrame "Hy".
      replace (map_insert x cx cs) with (<[x:=cx]>cs) by reflexivity.
      rewrite (insert_id cs)//. }
  replace (map_insert x cx cs) with (<[x:=cx]>cs) by reflexivity.
  rewrite (insert_id cs)//.
  rewrite insert_commute//.
Qed.
