From stdpp Require Import gmap fin_maps fin_sets stringmap.
From actris.channel Require Import proofmode.
From iris.heap_lang Require Import metatheory.

Definition maybe_insert_binder (x : binder) (X : stringset) : stringset :=
  match x with
  | BAnon => X
  | BNamed f => {[f]} ∪ X
  end.

Fixpoint is_closed_expr_set (X : stringset) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val_set v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr_set (maybe_insert_binder f (maybe_insert_binder x X)) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Free e | Load e =>
     is_closed_expr_set X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 | FAA e1 e2 =>
     is_closed_expr_set X e1 && is_closed_expr_set X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2 | Resolve e0 e1 e2 =>
     is_closed_expr_set X e0 && is_closed_expr_set X e1 && is_closed_expr_set X e2
  | NewProph => true
  end
with is_closed_val_set (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV f x e => is_closed_expr_set (maybe_insert_binder f (maybe_insert_binder x ∅)) e
  | PairV v1 v2 => is_closed_val_set v1 && is_closed_val_set v2
  | InjLV v | InjRV v => is_closed_val_set v
  end.

Lemma is_closed_expr_permute (e : expr) (xs ys : list string) :
  xs ≡ₚ ys →
  is_closed_expr xs e = is_closed_expr ys e.
Proof.
  revert xs ys. induction e=>xs ys Hxsys /=;
    repeat match goal with
    | [ |- _ && _ = _ && _ ] => f_equal
    | [ H : ∀ xs ys, xs ≡ₚ ys → is_closed_expr xs _ = is_closed_expr ys _
      |- is_closed_expr _ _ = is_closed_expr _ _ ] => eapply H; eauto
    end; try done.
  - apply bool_decide_iff. by rewrite Hxsys.
  - by rewrite Hxsys.
Qed.

Global Instance is_closed_expr_proper : Proper (Permutation ==> eq ==> eq) is_closed_expr.
Proof.
  intros X1 X2 HX x y ->. by eapply is_closed_expr_permute.
Qed.

Lemma is_closed_expr_set_sound (X : stringset) (e : expr) :
  is_closed_expr_set X e → is_closed_expr (elements X) e
with is_closed_val_set_sound (v : val) :
  is_closed_val_set v → is_closed_val v.
Proof.
  - induction e; simplify_eq/=; try by (intros; destruct_and?; split_and?; eauto).
    + intros. case_bool_decide; last done.
      by apply bool_decide_pack, elem_of_elements.
    + destruct f as [|f], x as [|x]; simplify_eq/=.
      * eapply IHe.
      * intros H%is_closed_expr_set_sound.
        eapply is_closed_weaken; eauto. by set_solver.
      * intros H%is_closed_expr_set_sound.
        eapply is_closed_weaken; eauto. by set_solver.
      * intros H%is_closed_expr_set_sound.
        eapply is_closed_weaken; eauto. by set_solver.
  - induction v; simplify_eq/=; try naive_solver.
    destruct f as [|f], x as [|x]; simplify_eq/=;
      intros H%is_closed_expr_set_sound; revert H.
    + set_solver.
    + by rewrite ?right_id_L elements_singleton.
    + by rewrite ?right_id_L elements_singleton.
    + rewrite ?right_id_L.
      intros. eapply is_closed_weaken; eauto.
      destruct (decide (f = x)) as [->|?].
      * rewrite union_idemp_L elements_singleton.
        set_solver.
      * rewrite elements_disj_union; last set_solver.
        rewrite !elements_singleton. set_solver.
Qed.

Lemma subst_map_subseteq md m1 m2 e :
  is_closed_expr_set (dom _ md) e →
  md ⊆ m1 →
  m1 ⊆ m2 →
  subst_map m1 e = subst_map m2 e.
Proof. Admitted.


Inductive ty :=
| tone : ty
| totimes : ty -> ty -> ty
| tlolli : ty -> ty -> ty
.

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with ty.
Notation "1" := tone : FType_scope.
(* Infix "⊕" := toplus (at level 11, right associativity) : FType_scope. *)
Infix "⊗" := totimes (at level 11, right associativity) : FType_scope.
(* Infix "&" := twith (at level 11, right associativity) : FType_scope. *)
Infix "⊸" := tlolli (at level 11, right associativity) : FType_scope.

Section interp.
Context `{!heapG Σ, !chanG Σ}.

Fixpoint interp_ty (τ : ty) : iProto Σ :=
  match τ with
  | 1%ty => (<!> MSG #(); END)%proto
  | (τ1 ⊗ τ2)%ty => (<! c> MSG c {{ ▷ c ↣ iProto_dual (interp_ty τ1) }}; interp_ty τ2)%proto
  | (τ1 ⊸ τ2)%ty => (<? c> MSG c {{ ▷ c ↣ iProto_dual (interp_ty τ1) }}; interp_ty τ2)%proto
  end.

Arguments interp_ty τ%ty.

Definition tyctx := gmap string ty.
Definition interp_seq (Δ : tyctx) (e : expr) (x : string) (τ : ty) : iProp Σ :=
  ∀ (o : val)    (* "output" channel *)
    (cs : gmap string val), (* substitution map *)
    ([∗ map] x ↦ σ;c ∈ Δ;cs, c ↣ iProto_dual (interp_ty σ)) -∗
  o ↣ interp_ty τ -∗
  WP (subst_map (<[x:=o]>cs) e) {{ _, o ↣ END (* ∗ ([∗ map] x ↦ σ;c ∈ Δ;cs, c ↣ END) *) }}%I.

Notation "Δ '⊢ₗ' P ':' '(' c ':' τ ')'" := (interp_seq Δ%ty P c τ%ty) (at level 74, P, c, τ at next level).

Lemma big_sepM2_union_l {A B} (Φ : string → A → B → iProp Σ)
      (m1 m2 : gmap string A) (n : gmap string B) :
  m1 ##ₘ m2 →
  ([∗ map] k↦x;y ∈ (m1 ∪ m2);n, Φ k x y) ⊢
  (∃ n1 n2, ⌜n1 ##ₘ n2⌝ ∗ ⌜n = n1 ∪ n2⌝
                        ∗ ([∗ map] k↦x;y ∈ m1;n1, Φ k x y)
                        ∗ ([∗ map] k↦x;y ∈ m2;n2, Φ k x y)).
Proof.
  intros Hm.
  pose (n1 := (filter (λ x, x ∈ dom _ m1) n) : gmap string B).
  pose (n2 := (filter (λ x, ¬ (x ∈ dom _ m1)) n) : gmap string B).
  assert (n1 ##ₘ n2) as Hndisj.
  { eapply map_disjoint_filter. }
  iIntros "H".
  iAssert (⌜dom (gset string) (m1 ∪ m2) = dom (gset string) n⌝)%I as %Hfoo.
  { by  rewrite big_sepM2_dom. }
  assert (n = n1 ∪ n2) as Hn.
  { eapply map_eq=>i. admit. }
    (* destruct (n !! i) as [x|] eqn:Hx. *)
  assert (dom (gset string) m1 = dom (gset string) n1) as Hmn1.
  { admit. }
  assert (dom (gset string) m2 = dom (gset string) n2) as Hmn2.
  { admit. }

  iExists n1, n2. repeat iSplit; eauto.
  rewrite Hn.
  rewrite big_sepM2_alt.
  iDestruct "H" as (Hk) "H".
Admitted.




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
  iIntros (oy cs) "HΔ Hoy". simpl.
  rewrite big_sepM2_union_l //.
  iDestruct "HΔ" as (cs1 cs2 Hcs ->) "[HΔ HΔ']".
  iAssert (⌜dom stringset Δ1 = dom stringset cs1⌝)%I as %Hdom1.
  { by rewrite big_sepM2_dom. }
  iAssert (⌜dom stringset Δ2 = dom stringset cs2⌝)%I as %Hdom2.
  { by rewrite (big_sepM2_dom _ Δ2). }
  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[H1 HΔ]").
  { iNext. iIntros (c) "Hc".
    rewrite iProto_dual_involutive. wp_pures.
    iSpecialize ("H1" $! c cs1 with "HΔ Hc").
    rewrite -subst_map_insert.
    rewrite (subst_map_subseteq (<[x:=c]>cs1) (<[x:=c]>cs1) (<[x:=c]> (<[y:=oy]> (cs1 ∪ cs2))))//.
    - iApply (wp_wand with "H1"). eauto.
    - revert Hclosed1. by rewrite dom_insert_L Hdom1.
    - eapply insert_mono. etrans; first by eapply map_union_subseteq_l.
      eapply insert_subseteq.
      eapply not_elem_of_dom.
      rewrite dom_union_L -Hdom1 -Hdom2.
      rewrite not_elem_of_union. rewrite !not_elem_of_dom. naive_solver. }
  iIntros (xc) "Hx". wp_pures.
  iSpecialize ("H2" $! _ (<[x:=xc]>cs2) with "[HΔ' Hx] Hoy").
  { iApply (big_sepM2_insert_2 with "[Hx]"); eauto. }
  rewrite -subst_map_insert.
  rewrite (subst_map_subseteq (<[y:=oy]> (<[x:=xc]> cs2)) (<[y:=oy]> (<[x:=xc]> cs2)) (<[x:=xc]> (<[y:=oy]> (cs1 ∪ cs2))))//.
  { revert Hclosed2.
    rewrite !dom_insert_L. rewrite assoc_L. rewrite (comm_L _ {[y]} {[x]}).
    by rewrite Hdom2. }
  rewrite insert_commute //.
  do 2 eapply insert_mono. eapply map_union_subseteq_r. done.
Qed.

Lemma tone_right (x : string) :
  (⊢ ∅ ⊢ₗ send (Var x) #() : (x : 1)).
Proof.
  iIntros (o vs) "Hemp Ho". wp_pures.
  rewrite big_sepM2_empty_r. iDestruct "Hemp" as "->".
  rewrite lookup_insert /=.
  wp_send with "[]"; eauto with iFrame.
Qed.

Lemma tone_left (x y : string) e Δ τ  :
  x ≠ y →
  Δ !! y = None →
  (Δ ⊢ₗ e : (x : τ)) -∗
  (<[y:=1]>Δ) ⊢ₗ (recv y;; e) : (x : τ).
Proof.
  iIntros (Hxy HΔ) "IH".
  iIntros (o cs) "Hcs Ho". simpl.
  rewrite lookup_insert_ne//.
  destruct (cs !! y) as [cy|] eqn:Hcs; last first.
  { rewrite big_sepM2_dom. iDestruct "Hcs" as %Hcsdom.
    exfalso. admit. }
  assert (cs = <[y:=cy]>(delete y cs)) as ->.
  { by rewrite insert_delete insert_id//. }
  rewrite big_sepM2_insert; eauto; last first.
  { eapply lookup_delete. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_recv as "_". wp_pures.
  iSpecialize ("IH" $! o (delete y cs) with "Hcs Ho").
  admit.
Admitted.

Lemma tlolli_right (Δ : tyctx) τ1 τ2 e (x y : string) :
  x ≠ y →
  Δ !! x = None →
  Δ !! y = None →
  ((<[x:=τ1]>Δ) ⊢ₗ e : (y : τ2)) -∗
  Δ ⊢ₗ (let: x := recv y in e) : (y : τ1 ⊸ τ2).
Proof.
  intros Hxy Hx Hy. iIntros "H".
  iIntros (oy cs) "HΔ Hoy". wp_pures.
  rewrite lookup_insert.
  iSimpl in "Hoy".
  wp_recv (cx) as "Hx". wp_pures.
  rewrite -subst_map_insert.
  iSpecialize ("H" $! _ (<[x:=cx]>cs) with "[Hx HΔ] Hoy").
  { iApply (big_sepM2_insert_2 with "[Hx] HΔ"); simpl; eauto. }
  rewrite insert_commute//.
Qed.

Lemma tlolli_left (Δ Δ' : tyctx) τ1 τ2 e1 e2 σ (x y z : string) :
  x ≠ y →
  x ≠ z →
  y ≠ z →
  Δ !! x = None →
  Δ' !! x = None →
  Δ ##ₘ Δ' →
  (Δ' ⊢ₗ e1 : (y : τ1)) -∗
  (<[x:=τ2]>Δ ⊢ₗ e2 : (z : σ)) -∗
  ((<[x:=τ1 ⊸ τ2]>Δ) ∪ Δ' ⊢ₗ (let: y := start_chan (λ: y, e1) in send x y;; e2) : (z : σ)).
Proof.
  intros Hxy Hxz Hyz Hx Hx' HΔ. iIntros "H1 H2".
  iIntros (o cs) "Hcs Ho". simpl.
  rewrite lookup_delete.
  rewrite !lookup_delete_ne//.
  rewrite lookup_insert_ne//.

  rewrite big_sepM2_union_l //; last first.
  { admit. }
  iDestruct "Hcs" as (cs1 cs2 Hcs' ->) "[HΔ HΔ']".
  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[H1 HΔ']").
  { iNext. iIntros (c) "Hc".
    rewrite iProto_dual_involutive. wp_pures.
    iSpecialize ("H1" $! c cs2 with "HΔ' Hc").
    rewrite -subst_map_insert.
    admit. }

  iIntros (yc) "Hy". wp_pures.
  case_decide; last naive_solver.

  destruct (cs1 !! x) as [xc|] eqn:Hcs; last first.
  { rewrite big_sepM2_dom. iDestruct "HΔ" as %Hcsdom.
    exfalso. admit. }
  rewrite (lookup_union_Some_l cs1 cs2 x xc) //.
  rewrite big_sepM2_insert_acc //; last first.
  { eapply lookup_insert. }
  iDestruct "HΔ" as "[Hx Hcs]".
  simpl.

  wp_send with "[$Hy]". wp_pures.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert (insert_id cs1)//.
  iSpecialize ("H2" $! o cs1 with "Hcs Ho").
  rewrite -subst_map_insert. admit.
Admitted.


Lemma ttimes_right (Δ Δ' : tyctx) τ1 τ2 e e' (x y : string) :
  x ≠ y →
  Δ ##ₘ Δ' →
  (Δ ⊢ₗ e : (x : τ1)) -∗
  (Δ' ⊢ₗ e' : (y : τ2)) -∗
  (Δ ∪ Δ' ⊢ₗ (let: x := start_chan (λ: x, e) in
              send y x;;
              e') : (y : τ1 ⊗ τ2)).
Proof.
  intros Hxy HΔ. iIntros "H1 H2". iIntros (oy cs) "HΔ Hoy". wp_pures.
  rewrite lookup_delete_ne// !lookup_delete lookup_insert.
  simpl.
  rewrite big_sepM2_union_l //.
  iDestruct "HΔ" as (cs1 cs2 Hcs) "[HΔ HΔ']".

  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[H1 HΔ]").
  { iNext. iIntros (c) "Hc".
    rewrite iProto_dual_involutive. wp_pures.
    iSpecialize ("H1" $! c cs1 with "HΔ Hc").
    rewrite -subst_map_insert.
    (* need additional information about the closedness of [e], and cs1 ⊑ cs *)
    admit. }
  iIntros (xc) "Hxc". wp_pures.
  case_decide; last naive_solver.
  wp_send with "[$Hxc]". wp_pures.
  iSpecialize ("H2" with "HΔ' Hoy").
  rewrite -subst_map_insert. admit.
Admitted.

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
  iIntros (o cs) "Hcs Ho". simpl.
  rewrite lookup_insert_ne//.
  destruct (cs !! x) as [cx|] eqn:Hcs; last first.
  { rewrite big_sepM2_dom. iDestruct "Hcs" as %Hcsdom.
    exfalso. admit. }
  destruct (cs !! y) as [cy|] eqn:Hcs2.
  { rewrite big_sepM2_dom. iDestruct "Hcs" as %Hcsdom.
    exfalso. admit. }
  rewrite big_sepM2_insert_acc; eauto; last first.
  { eapply lookup_insert. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_recv (cy) as "Hy". wp_pures.
  rewrite -subst_map_insert.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert (insert_id cs) //.
  iSpecialize ("IH" $! o (<[y:=cy]>(map_insert x cx cs)) with "[Hcs Hy] Ho").
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
Admitted.
