(** Interpretation of the πDILL type system from
    Luís Caires, Frank Pfenning, and Bernardo Toninho. “Linear Logic Propositions as Session Types.” Mathematical Structures in Computer Science 26, no. 3 (March 2016): 367–423. <https://doi.org/10.1017/S0960129514000218>.
 *)
From stdpp Require Import gmap fin_maps fin_sets stringmap.
From iris.base_logic.lib Require Import invariants.
From actris.channel Require Import proofmode.
From actris.utils Require Import syntax_facts big_sepM2_facts.

Inductive ty :=
| tone : ty
| totimes : ty → ty → ty
| toplus : ty → ty → ty
| twith : ty → ty → ty
| tlolli : ty → ty → ty
| tofc : ty → ty
.

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with ty.
Notation "1" := tone : FType_scope.
Infix "⊕" := toplus (at level 11, right associativity) : FType_scope.
Infix "⊗" := totimes (at level 11, right associativity) : FType_scope.
Infix "&" := twith (at level 11, right associativity) : FType_scope.
Infix "⊸" := tlolli (at level 11, right associativity) : FType_scope.
Notation "! τ" := (tofc τ%ty) (at level 9, τ at level 9) : FType_scope.

Section interp.
Context `{!heapG Σ, !chanG Σ}.

Program Definition iProto_server_aux
    (P : iProto Σ) : iProto Σ -n> iProto Σ := λne self,
   (<? c> MSG c {{ c ↣ P }}; self)%proto.
Next Obligation. solve_proper. Qed.

Instance iProto_server_contractive P :
  Contractive (iProto_server_aux P).
Proof. solve_contractive. Qed.

Definition iProto_server (P : iProto Σ) := fixpoint (iProto_server_aux P).
Lemma iProto_server_unfold P :
  (iProto_server P ≡ <? c> MSG c {{ c ↣ P }}; iProto_server P)%proto.
Proof.
  rewrite /iProto_server. eapply (fixpoint_unfold (iProto_server_aux P)).
Qed.


Fixpoint interp_ty (τ : ty) : iProto Σ :=
  match τ with
  | 1%ty => (<!> MSG #(); END)%proto
  | (τ1 ⊗ τ2)%ty => (<! c> MSG c {{ ▷ c ↣ iProto_dual (interp_ty τ1) }}; interp_ty τ2)%proto
  | (τ1 ⊕ τ2)%ty => iProto_choice Send True True (interp_ty τ1) (interp_ty τ2)
  | (τ1 & τ2)%ty => iProto_choice Recv True True (interp_ty τ1) (interp_ty τ2)
  | (τ1 ⊸ τ2)%ty => (<? c> MSG c {{ ▷ c ↣ iProto_dual (interp_ty τ1) }}; interp_ty τ2)%proto
  | (! τ)%ty => iProto_server (interp_ty τ)
  end.

Arguments interp_ty τ%ty.

Definition nctx (u : val) := nroot.@"illctx".@u.

Definition tyctx := gmap string ty.
Definition interp_seq (Γ : tyctx) (Δ : tyctx) (e : expr) (x : string) (τ : ty) : iProp Σ :=
  □
  ∀ (ss cs : gmap string val) (* substitution maps *)
    (o : val),    (* "output" channel *)
  ⌜ss ##ₘ cs⌝ -∗
  ([∗ map] x ↦ σ;u ∈ Γ;ss, inv (nctx u) (u ↣ iProto_dual (iProto_server (interp_ty σ)))) -∗
  ([∗ map] x ↦ σ;c ∈ Δ;cs, c ↣ iProto_dual (interp_ty σ)) -∗
  o ↣ interp_ty τ -∗
  WP (subst_map (<[x:=o]>(ss ∪ cs)) e) {{ _, o ↣ END }}%I.

Notation "Γ '&;' Δ '⊢ₗ' P ':' '(' c ':' τ ')'" := (interp_seq Γ%ty Δ%ty P%E c τ%ty) (at level 74, P, c, τ at next level).

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

(* attempt to prove [Hyv : cs !! y = Some yv] *)
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




Lemma cut_ Γ Δ1 Δ2 (x y : string) τ1 τ2 e1 e2 :
  x ≠ y →
  Δ1 !! y = None →
  Δ2 !! y = None →
  Γ !! x = None →
  Γ !! y = None →
  Δ1 ##ₘ Δ2 →
  is_closed_expr_set ({[x]} ∪ dom _ Δ1 ∪ dom _ Γ) e1 →
  is_closed_expr_set ({[x;y]} ∪ dom _ Δ2 ∪ dom _ Γ) e2 →
  (Γ &; Δ1 ⊢ₗ e1 : (x : τ1)) -∗
  (Γ &; (<[x:=τ1]>Δ2) ⊢ₗ e2 : (y : τ2)) -∗
  (Γ &; Δ1 ∪ Δ2 ⊢ₗ (let: x := start_chan (λ: x, e1) in e2) : (y : τ2)).
Proof.
  intros Hxy Hy1 Hy2 Hx0 Hy0 HΔ Hclosed1 Hclosed2. iIntros "#H1 #H2".
  iModIntro. iIntros (ss cs oy Hsscs) "#HΓ HΔ Hoy". simpl.
  rewrite big_sepM2_union_l //.
  iDestruct "HΔ" as (cs1 cs2 Hcs ->) "[HΔ HΔ']".
  iAssert (⌜dom stringset Δ1 = dom stringset cs1⌝)%I as %Hdom1.
  { by rewrite (big_sepM2_dom _ Δ1). }
  iAssert (⌜dom stringset Δ2 = dom stringset cs2⌝)%I as %Hdom2.
  { by rewrite (big_sepM2_dom _ Δ2). }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ Γ). }

  assert_not_in_map cs1 y.
  assert_not_in_map cs2 y.
  assert_not_in_map ss x.
  assert_not_in_map ss y.

  eapply map_disjoint_union_r in Hsscs.
  destruct Hsscs as [Hsscs1 Hsscs2].
  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[H1 HΔ]").
  { iNext. iIntros (c) "Hc".
    rewrite iProto_dual_involutive. wp_pures.
    iSpecialize ("H1" with "[%] HΓ HΔ Hc"); eauto.
    rewrite -subst_map_insert.
    - assert (subst_map (<[x:=c]> (ss ∪ cs1)) e1
              = subst_map (<[x:=c]> (<[y:=oy]> (ss ∪ (cs1 ∪ cs2)))) e1) as ->.
      { eapply subst_map_agree_weaken; eauto.
        - rewrite Hdom1 Hdom0 dom_insert_L. by set_solver.
        - eapply insert_mono.
          rewrite insert_union_l.
          rewrite assoc_L.
          etrans; last eapply map_union_subseteq_l.
          eapply map_union_mono_r.
          { eapply map_disjoint_insert_l. eauto. }
          eapply insert_subseteq.
          eapply not_elem_of_dom. rewrite -Hdom0.
          by eapply not_elem_of_dom. }
      iApply (wp_wand with "H1"). eauto. }
  iIntros (xc) "Hx". wp_pures.
  iSpecialize ("H2" $! ss (<[x:=xc]>cs2) with "[%] HΓ [HΔ' Hx] Hoy").
  - eapply map_disjoint_insert_r. eauto.
  - iApply (big_sepM2_insert_2 with "[Hx]"); eauto.
  - rewrite -subst_map_insert.
    rewrite -insert_union_r//.
    rewrite insert_commute//.
    cut (subst_map (<[x:=xc]> (<[y:=oy]> (ss ∪ cs2))) e2
         = subst_map (<[x:=xc]> (<[y:=oy]> (ss ∪ (cs1 ∪ cs2)))) e2); first by intros ->.
    rewrite assoc_L (map_union_comm ss cs1) // -assoc_L.
    eapply subst_map_fact_2; eauto.
    + rewrite dom_union_L -Hdom2 -Hdom0.
      assert (({[x; y]} ∪ (dom stringset Γ ∪ dom stringset Δ2))
                = ({[x; y]} ∪ dom stringset Δ2 ∪ dom stringset Γ)) as ->.
      { set_unfold. tauto. }
      done.
    + eapply lookup_union_None; eauto.
    + eapply map_disjoint_union_r; eauto.
Qed.

Lemma tcopy Γ Δ (x y u : string) τ1 τ2 e :
  x ≠ y →
  y ≠ u →
  u ≠ "z" →
  y ≠ "z" →
  Δ !! x = None →
  Γ !! x = None →
  Γ !! u = Some τ1 →
  is_closed_expr_set ({[x;y]} ∪ dom _ Δ ∪ dom _ Γ) e →
  (Γ &; (<[x:=τ1]>Δ) ⊢ₗ e : (y : τ2)) -∗
  (Γ &; Δ ⊢ₗ (let: x := start_chan (λ: "z", send u "z") in e) : (y : τ2)).
Proof.
  intros Hxy Hyu Huz Hyz HΔ1 HΔ HG Hclosed1. iIntros "#H1".
  iModIntro.
  iIntros (ss cs oy Hsscs) "#HΓ HΔ Hoy".

  iAssert (⌜dom stringset Δ = dom stringset cs⌝)%I as %Hdom.
  { by rewrite (big_sepM2_dom _ Δ). }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ Γ). }
  assert (u ∈ dom stringset Γ).
  { eapply elem_of_dom. eauto. }

  assert_not_in_map cs x.
  assert_not_in_map ss x.
  assert_in_map_ ss u uv Huv.

  simpl. rewrite lookup_delete_ne//. rewrite lookup_delete.
  rewrite lookup_insert_ne//.
  rewrite (lookup_union_Some_l _ _ _ _ Huv).

  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[]").
  { iNext. iIntros (c) "Hc". wp_pures.
    rewrite iProto_dual_involutive.
    iApply (send_spec_atomic val (λ v, v ↣ interp_ty τ1) True%I c id with "Hc [//]").
    iModIntro. iAssert (inv (nctx uv) (uv ↣ iProto_dual (iProto_server (interp_ty τ1))))%I as "#Hinv".
    {  rewrite (big_sepM2_insert_acc _ Γ ss u) //. by iDestruct "HΓ" as "[$ _]". }
    iInv (nctx uv) as "Huv" "Hcl". iModIntro.
    rewrite {2}iProto_server_unfold.
    rewrite iProto_dual_message /=.
    rewrite iMsg_dual_exist.
    iExists (λ _, iProto_dual (iProto_server (interp_ty τ1))).
    assert ((<! (x0 : val)> MSG x0 {{ x0 ↣ interp_ty τ1 }}; iProto_dual (iProto_server (interp_ty τ1)))%proto
               ≡ (<! (x0 : val)> iMsg_dual (MSG x0 {{ x0 ↣ interp_ty τ1 }}; iProto_server (interp_ty τ1)))%proto) as ->.
    { f_equiv. f_equiv. intros xx.
      by rewrite iMsg_dual_base. }
    iFrame "Huv". iSplit.
    { iIntros "HH". iApply "Hcl".
      rewrite {3}iProto_server_unfold.
      rewrite iProto_dual_message /= iMsg_dual_exist. iFrame "HH". }
    iIntros "[Huv _]". by iApply "Hcl". }
  iIntros (xc) "Hx". wp_pures.
  iSpecialize ("H1" $! ss (<[x:=xc]>cs) with "[%] HΓ [HΔ Hx] Hoy").
  - eapply map_disjoint_insert_r. eauto.
  - iApply (big_sepM2_insert_2 with "[Hx]"); eauto.
  - rewrite -subst_map_insert.
    rewrite insert_commute //.
    rewrite -(insert_union_r _ _ x)//.
Qed.


Definition loop_ : val :=
  (rec: "f" "z" "t" := let: "x" := recv "z" in Fork ("t" "x") ;; "f" "z" "t")%V.

Lemma cut_bang Γ Δ (x y u : string) τ1 τ2 e1 e2 :
  x ≠ y →
  x ≠ u →
  u ≠ y →
  is_closed_expr_set ({[x]} ∪ dom stringset Γ) e1 →
  is_closed_expr_set ({[u;y]} ∪ dom stringset Δ ∪ dom stringset Γ) e2 →
  Δ !! x = None →
  Δ !! u = None →
  Γ !! x = None →
  Γ !! y = None →
  Γ !! u = None →
  (Γ &; ∅ ⊢ₗ e1 : (x : τ1)) -∗
  ((<[u:=τ1]>Γ) &; Δ ⊢ₗ e2 : (y : τ2)) -∗
  Γ &; Δ ⊢ₗ (let: u := start_chan (λ: u, e2) in loop_ u (λ: x, e1)) : (y : τ2).
Proof.
  intros Hxy Hxu Huy He1 He2 Hx Hx2 Hy2 Hu Hu2. iIntros "#H1 #H2".
  iModIntro. iIntros (ss cs oy Hsscs) "#HΓ HΔ Hoy".
  iAssert (⌜dom stringset Δ = dom stringset cs⌝)%I as %Hdom1.
  { by rewrite (big_sepM2_dom _ Δ). }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ Γ). }

  assert_not_in_map cs x.
  assert_not_in_map cs u.
  assert_not_in_map ss x.
  assert_not_in_map ss y.
  assert_not_in_map ss u.

  simpl.
  rewrite lookup_delete.
  wp_pures.

  wp_smart_apply (start_chan_spec (iProto_server (interp_ty τ1)) with "[-]").
  { iNext.
    iIntros (uv) "Hu". wp_pures.
    iMod (inv_alloc (nctx uv) _  (uv ↣ iProto_dual (iProto_server (interp_ty τ1))) with "[Hu]")  as "#Hinv".
    { by iNext. }
    iSpecialize ("H2" $! (<[u:=uv]> ss) cs oy with "[%]").
    { eapply map_disjoint_insert_l_2; eauto. }
    iSpecialize ("H2" with "[] HΔ Hoy").
    - rewrite big_sepM2_insert //. iFrame "HΓ Hinv".
    - rewrite -subst_map_insert. rewrite -insert_union_l.
      rewrite insert_commute//.
      iApply (wp_wand with "H2"). eauto. }
  iIntros (c) "Hc". wp_pure _.
  wp_pure _.
  rewrite decide_left//.
  case_decide; last naive_solver.
  rewrite delete_commute//. rewrite -subst_map_insert.
  rewrite delete_notin; last first.
  { rewrite lookup_insert_ne//. eapply lookup_union_None. eauto. }
  wp_pures.
  iLöb as "IH". wp_rec. wp_pures.
  rewrite {2}iProto_server_unfold. wp_recv (xv) as "Hx". wp_pures.
  wp_bind (Fork _). iApply (wp_fork with "[Hx]").
  { iApply (wp_wand _ _ _ (λ _, xv ↣ END)%proto with "[Hx]").
    { iSpecialize ("H1" $! ss ∅ xv with "[%] HΓ [] Hx").
      - eapply map_disjoint_empty_r.
      - by iApply big_sepM2_empty.
      - rewrite subst_map_insert. rewrite right_id.
        rewrite -subst_map_insert.
        wp_rec.
        rewrite -(delete_notin (<[u:=c]> _) x); last first.
        {  rewrite !lookup_insert_ne//.
           eapply lookup_union_None; eauto. }
        rewrite -subst_map_insert.
        assert (subst_map (<[x:=xv]> ss) e1 = subst_map (<[x:=xv]> (<[u:=c]> (<[y:=oy]> (ss ∪ cs)))) e1) as ->.
        { eapply subst_map_agree_weaken; eauto.
          - by rewrite dom_insert_L Hdom0.
          - eapply insert_mono. do 2 eapply insert_subseteq_r=>//.
            eapply map_union_subseteq_l. }
        iApply "H1". }
      iNext. iIntros (?) "_". done. }
  iNext. wp_pure _. wp_pure _. by iApply "IH".
Qed.

Lemma tofc_right Γ e (x y : string) τ :
  x ≠ y →
  Γ !! x = None →
  is_closed_expr_set ({[y]} ∪ dom stringset Γ) e →
  (Γ &; ∅ ⊢ₗ e : (y : τ)) -∗
  (Γ &; ∅ ⊢ₗ (loop_ x (λ: y, e)) : (x : ! τ)).
Proof.
  intros Hxy Hx0 He. iIntros "#H".
  iModIntro. iIntros (ss cs o Hsscs) "#Hss Hemp Ho". simpl.

  rewrite lookup_insert.

  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ Γ). }
  iAssert (⌜dom stringset ∅ = dom stringset cs⌝)%I as %Hdom1.
  { by rewrite (big_sepM2_dom _ _ cs). }
  assert (cs = ∅) as ->.
  { eapply dom_empty_inv_L. simpl in Hdom1.
    by rewrite -Hdom1 dom_empty_L. }
  assert_not_in_map ss x.

  iClear "Hemp". wp_pures.
  iLöb as "IH". wp_rec. wp_pures.
  rewrite {2}iProto_server_unfold.
  wp_recv (yv) as "Hy". wp_pures.
  rewrite right_id.
  wp_bind (Fork _). iApply (wp_fork with "[Hy]").
  { iNext. wp_rec. rewrite -subst_map_insert.
    iSpecialize ("H" $! ss ∅ yv with "[%] Hss [] Hy").
    { eapply map_disjoint_empty_r. }
    { by iApply big_sepM2_empty. }
    rewrite right_id.
    rewrite (subst_map_agree_weaken e ({[y]} ∪ dom stringset Γ) (<[y:=yv]> ss) (<[y:=yv]> (<[x:=o]> ss)))//.
    2:{ by rewrite dom_insert_L Hdom0. }
    2:{ eapply insert_mono. eapply insert_subseteq_r; eauto. }
    iApply (wp_wand with "H"). eauto. }
  iNext. wp_pures. by iApply "IH".
Qed.

Lemma tofc_left Γ Δ e (x y : string) τ σ :
  x ≠ y →
  Γ !! y = None →
  Δ !! y = None →
  is_closed_expr_set ({[x;y]} ∪ dom _ Δ ∪ dom _ Γ) e →
  (<[y:=τ]>Γ &; Δ ⊢ₗ e : (x : σ)) -∗
  (Γ &; (<[y:=tofc τ]>Δ) ⊢ₗ e : (x : σ)).
Proof.
  intros Hxy Hy0 Hy1 He. iIntros "#H".
  iModIntro. iIntros (ss cs xv Hsscs) "Hss Hcs Hx".
  iAssert (⌜dom stringset (<[y:=(tofc τ)]>Δ) = dom stringset cs⌝)%I as %Hdom1.
  { by rewrite (big_sepM2_dom _ (<[y:=(tofc τ)]>Δ)). }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ Γ). }

  assert_in_map_ cs y yv Hyv.
  assert_not_in_map ss y.

  assert (cs = <[y:=yv]>(delete y cs)) as Hcs.
  { rewrite insert_delete insert_id//. }
  rewrite {1}Hcs.
  rewrite big_sepM2_insert//; last first.
  { eapply lookup_delete. }
  iDestruct "Hcs" as "[Hy Hcs]".
  iSimpl in "Hy".
  iMod (inv_alloc (nctx yv) _  (yv ↣ iProto_dual (iProto_server (interp_ty τ))) with "[Hy]")  as "#Hinv".
  { by iNext. }
  iSpecialize ("H" $! (<[y:=yv]>ss) (delete y cs) with "[%] [Hss] Hcs Hx").
  { eapply map_disjoint_insert_l. split.
    + eapply lookup_delete.
    + by eapply map_disjoint_delete_r. }
  iApply (big_sepM2_insert_2 with "[] Hss").
  { simpl. by iFrame. }
  rewrite -insert_union_l.
  rewrite (insert_union_r ss _ y)//.
  by rewrite -Hcs.
Qed.

Lemma tone_right Γ  (x : string) :
  (⊢ Γ &; ∅ ⊢ₗ send (Var x) #() : (x : 1)).
Proof.
  iModIntro. iIntros (ss cs o Hsscs) "Hserv Hemp Ho". wp_pures.
  rewrite lookup_insert /=.
  wp_send with "[]"; eauto with iFrame.
Qed.

Lemma tone_left (x y : string) e Γ Δ τ  :
  x ≠ y →
  Δ !! y = None →
  is_closed_expr_set ({[x]} ∪ dom _ Δ ∪ dom _ Γ) e →
  (Γ &; Δ ⊢ₗ e : (x : τ)) -∗
  (Γ &; (<[y:=1]>Δ) ⊢ₗ (recv y;; e) : (x : τ)).
Proof.
  iIntros (Hxy HΔ Hdome) "#IH".
  iModIntro. iIntros (ss cs o Hsscs) "Hss Hcs Ho". simpl.
  rewrite lookup_insert_ne//.
  iAssert (⌜dom stringset (<[y:=1%ty]>Δ) = dom stringset cs⌝)%I as %Hdom1.
  { by rewrite (big_sepM2_dom _ (<[y:=1%ty]>Δ)). }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ Γ). }

  assert_in_map_ cs y cy Hcy.
  assert_not_in_map ss y.
  { rewrite Hdom0. eapply not_elem_of_dom.
    by eapply map_disjoint_Some_r. }

  assert (cs = <[y:=cy]>(delete y cs)) as Hcs.
  { by rewrite insert_delete insert_id//. }
  rewrite {1}Hcs.
  rewrite big_sepM2_insert; eauto; last first.
  { eapply lookup_delete. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  rewrite (lookup_union_Some_r _ _ _ _ Hsscs Hcy).
  wp_recv as "_". wp_pures.
  iSpecialize ("IH" $! ss (delete y cs) with "[%] Hss Hcs Ho").
  { by apply map_disjoint_delete_r. }
  cut (subst_map (<[x:=o]> (ss ∪ delete y cs)) e
       = subst_map (<[x:=o]> (ss ∪ cs)) e); first by intros ->.
  eapply subst_map_agree_weaken; eauto.
  { rewrite dom_insert_L dom_union_L (comm_L _ (dom stringset ss)) assoc_L.
    repeat f_equiv; eauto.
    rewrite dom_delete_L -Hdom1 dom_insert_L.
    rewrite difference_union_distr_l_L.
    rewrite difference_diag_L left_id_L.
    rewrite -dom_delete_L.
    rewrite delete_notin //. }
  eapply insert_mono. eapply map_union_mono_l.
  eapply delete_subseteq.
Qed.

Lemma tlolli_right (Γ Δ : tyctx) τ1 τ2 e (x y : string) :
  x ≠ y →
  Δ !! x = None →
  Δ !! y = None →
  Γ !! x = None →
  (Γ &; (<[x:=τ1]>Δ) ⊢ₗ e : (y : τ2)) -∗
  Γ &; Δ ⊢ₗ (let: x := recv y in e) : (y : τ1 ⊸ τ2).
Proof.
  intros Hxy Hx Hy Hx'. iIntros "#H". iModIntro.
  iIntros (ss cs oy Hsscs) "HΓ HΔ Hoy".

  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ Γ). }
  assert_not_in_map ss x.

  wp_pures. rewrite lookup_insert.
  iSimpl in "Hoy".
  wp_recv (cx) as "Hx". wp_pures.
  rewrite -subst_map_insert.
  iSpecialize ("H" $! ss (<[x:=cx]>cs) with "[%] HΓ [Hx HΔ] Hoy").
  { by eapply map_disjoint_insert_r_2. }
  { iApply (big_sepM2_insert_2 with "[Hx] HΔ"); simpl; eauto. }
  rewrite insert_commute//.
  rewrite -insert_union_r //.
Qed.

Lemma tlolli_left (Γ Δ Δ' : tyctx) τ1 τ2 e1 e2 σ (x y z : string) :
  x ≠ y →
  x ≠ z →
  y ≠ z →
  Γ !! x = None →
  Γ !! y = None →
  Γ !! z = None →
  Δ !! x = None →
  Δ' !! x = None →
  Δ !! y = None →
  Δ' !! y = None →
  Δ !! z = None →
  Δ' !! z = None →
  Δ ##ₘ Δ' →
  is_closed_expr_set ({[y]} ∪ dom stringset Δ' ∪ dom stringset Γ) e1 →
  is_closed_expr_set ({[x;z]} ∪ dom stringset Δ ∪ dom stringset Γ) e2 →
  (Γ &; Δ' ⊢ₗ e1 : (y : τ1)) -∗
  (Γ &; <[x:=τ2]>Δ ⊢ₗ e2 : (z : σ)) -∗
  (Γ &; (<[x:=τ1 ⊸ τ2]>Δ) ∪ Δ' ⊢ₗ (let: y := start_chan (λ: y, e1) in send x y;; e2) : (z : σ)).
Proof.
  intros Hxy Hxz Hyz HxΓ HyΓ HzΓ Hx Hx' Hy Hy' Hz Hz' HΔ He1 He2.
  iIntros "#H1 #H2". iModIntro.
  iIntros (ss cs o Hsscs) "#Hss Hcs Ho". simpl.
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
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ Γ). }


  assert_in_map cs1 x.

  assert_not_in_map cs1 y.
  assert_not_in_map cs2 y.
  assert_not_in_map ss x.
  assert_not_in_map ss y.

  eapply map_disjoint_union_r in Hsscs.
  destruct Hsscs as [Hsscs1 Hsscs2].

  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[H1 HΔ']").
  { iNext. iIntros (c) "Hc".
    rewrite iProto_dual_involutive. wp_pures.
    iSpecialize ("H1" $! ss cs2 with "[%] Hss HΔ' Hc"); eauto.
    rewrite -subst_map_insert.
    cut (subst_map (<[y:=c]> (ss ∪ cs2)) e1
         = subst_map (<[y:=c]> (<[z:=o]> (ss ∪ (cs1 ∪ cs2)))) e1); first intros ->.
    { iApply (wp_wand with "H1"); eauto. }
    rewrite assoc_L (map_union_comm ss cs1)// -assoc_L.
    eapply (subst_map_fact_1); eauto.
    - by rewrite (map_union_comm ss cs2) // dom_union_L -Hdom2 -Hdom0 assoc_L.
    - eapply not_elem_of_dom. rewrite -Hdom1.
      eapply not_elem_of_dom in Hz.
      set_solver.
    - eapply not_elem_of_dom. rewrite dom_union_L -Hdom2 -Hdom0.
      eapply not_elem_of_union; split; by eapply not_elem_of_dom.
    - eapply map_disjoint_union_r; eauto.
  }

  iIntros (yc) "Hy". wp_pures.
  case_decide; last naive_solver.
  rewrite lookup_union_r //.
  rewrite (lookup_union_Some_l _ _ x y0) //.

  rewrite (big_sepM2_insert_acc _ _ cs1 x) //; last first.
  { eapply lookup_insert. }
  iDestruct "HΔ" as "[Hx Hcs]".
  simpl.

  wp_send with "[$Hy]". wp_pures.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert (insert_id cs1)//.
  iSpecialize ("H2" $! ss _ with "[%] Hss Hcs Ho"); eauto.
  rewrite -subst_map_insert. rewrite insert_commute//.
  cut (subst_map (<[z:=o]> (ss ∪ cs1)) e2
       = subst_map (<[z:=o]> (<[y:=yc]> (ss ∪ (cs1 ∪ cs2)))) e2); first by intros ->.
  rewrite assoc_L. rewrite (map_union_comm ss cs1)//.
  eapply subst_map_fact_0; eauto.
  - rewrite dom_union_L -Hdom0 -Hdom1.
    cut (({[z]} ∪ ({[x]} ∪ dom stringset Δ ∪ dom stringset Γ)) =
         ({[x; z]} ∪ dom stringset Δ ∪ dom stringset Γ)) ; first by intros ->.
    set_unfold. tauto.
  - eapply lookup_union_None. tauto.
Qed.


Lemma twith_right Γ Δ τ1 τ2 e1 e2 (x : string) :
  (Γ &; Δ ⊢ₗ e1 : (x : τ1)) -∗
  (Γ &; Δ ⊢ₗ e2 : (x : τ2)) -∗
  Γ &; Δ ⊢ₗ (if: recv x then e1 else e2) : (x : τ1 & τ2).
Proof.
  iIntros "#H1 #H2". iModIntro.
  iIntros (ss cs ox Hsscs) "Hss Hcs Hx /=".
  rewrite lookup_insert.
  wp_branch; wp_pures.
  - iApply ("H1" $! ss cs with "[%] Hss Hcs Hx"); eauto.
  - iApply ("H2" $! ss cs with "[%] Hss Hcs Hx"); eauto.
Qed.

Lemma twith_left_1 Γ Δ τ1 τ2 e (x y : string) σ :
  x ≠ y →
  Γ !! x = None →
  Δ !! x = None →
  (Γ &; <[x:=τ1]>Δ ⊢ₗ e : (y : σ)) -∗
  Γ &; <[x:=τ1 & τ2]>Δ ⊢ₗ (send x #true;; e) : (y : σ).
Proof.
  intros Hxy HΓ HΔ. iIntros "#H".
  iModIntro. iIntros (ss cs oy Hsscs) "Hss Hcs Hy /=".
  iAssert (⌜{[x]} ∪ dom stringset Δ = dom stringset cs⌝)%I as %Hdom.
  { by rewrite (big_sepM2_dom _ _ cs) dom_insert_L. }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ _ ss). }


  assert_in_map_ cs x xv Hxv.
  assert_not_in_map ss x.

  rewrite lookup_insert_ne//. rewrite lookup_union_r // Hxv.
  rewrite (big_sepM2_insert_acc _ _ cs); eauto; last first.
  { eapply lookup_insert. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_select. wp_pures.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert // (insert_id cs)//.
  by iApply ("H"  with "[%] Hss Hcs Hy").
Qed.

Lemma twith_left_2 Γ Δ τ1 τ2 e (x y : string) σ :
  x ≠ y →
  Γ !! x = None →
  Δ !! x = None →
  (Γ &; <[x:=τ2]>Δ ⊢ₗ e : (y : σ)) -∗
  Γ &; <[x:=τ1 & τ2]>Δ ⊢ₗ (send x #false;; e) : (y : σ).
Proof.
  intros Hxy HΓ HΔ. iIntros "#H".
  iModIntro. iIntros (ss cs oy Hsscs) "Hss Hcs Hy /=".
  iAssert (⌜{[x]} ∪ dom stringset Δ = dom stringset cs⌝)%I as %Hdom.
  { by rewrite (big_sepM2_dom _ _ cs) dom_insert_L. }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ _ ss). }


  assert_in_map_ cs x xv Hxv.
  assert_not_in_map ss x.

  rewrite lookup_insert_ne//. rewrite lookup_union_r // Hxv.
  rewrite (big_sepM2_insert_acc _ _ cs); eauto; last first.
  { eapply lookup_insert. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_select. wp_pures.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert // (insert_id cs)//.
  by iApply ("H"  with "[%] Hss Hcs Hy").
Qed.

Lemma tplus_right_1 Γ Δ τ1 τ2 e (x : string) :
  (Γ &; Δ ⊢ₗ e : (x : τ1)) -∗
  Γ &; Δ ⊢ₗ (send x #true;; e) : (x : τ1 ⊕ τ2).
Proof.
  iIntros "#H1". iModIntro.
  iIntros (ss cs ox Hsscs) "Hss Hcs Hx /=".
  rewrite lookup_insert.
  wp_select. wp_pures.
  iApply ("H1" with "[%//] Hss Hcs Hx").
Qed.

Lemma tplus_right_2 Γ Δ τ1 τ2 e (x : string) :
  (Γ &; Δ ⊢ₗ e : (x : τ2)) -∗
  Γ &; Δ ⊢ₗ (send x #false;; e) : (x : τ1 ⊕ τ2).
Proof.
  iIntros "#H1". iModIntro.
  iIntros (ss cs ox Hsscs) "Hss Hcs Hx /=".
  rewrite lookup_insert.
  wp_select. wp_pures.
  iApply ("H1" with "[%//] Hss Hcs Hx").
Qed.

Lemma tplus_left Γ Δ τ1 τ2 e1 e2 (x y : string) σ :
  x ≠ y →
  Γ !! x = None →
  Δ !! x = None →
  (Γ &; <[x:=τ1]>Δ ⊢ₗ e1 : (y : σ)) -∗
  (Γ &; <[x:=τ2]>Δ ⊢ₗ e2 : (y : σ)) -∗
  Γ &; <[x:=τ1⊕τ2]>Δ ⊢ₗ (if: recv x then e1 else e2) : (y : σ).
Proof.
  intros Hxy HΓ HΔ. iIntros "#He1 #He2". iModIntro.
  iIntros (ss cs oy Hsscs) "Hss Hcs Hy /=".
  iAssert (⌜{[x]} ∪ dom stringset Δ = dom stringset cs⌝)%I as %Hdom.
  { by rewrite (big_sepM2_dom _ _ cs) dom_insert_L. }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ _ ss). }
  assert_in_map_ cs x xv Hxv.
  assert_not_in_map ss x.
  rewrite lookup_insert_ne// lookup_union_r // Hxv.
  rewrite (big_sepM2_insert_acc _ _ cs); eauto; last first.
  { eapply lookup_insert. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_branch; wp_pures.
  - iSpecialize ("Hcs" with "Hx").
    rewrite insert_insert (insert_id cs) //.
    iApply ("He1" with "[%//] Hss Hcs Hy").
  - iSpecialize ("Hcs" with "Hx").
    rewrite insert_insert (insert_id cs) //.
    iApply ("He2" with "[%//] Hss Hcs Hy").
Qed.

Lemma ttimes_right (Γ Δ Δ' : tyctx) τ1 τ2 e e' (x y : string) :
  x ≠ y →
  Δ ##ₘ Δ' →
  Γ !! x = None →
  Γ !! y = None →
  Δ !! y = None →
  Δ' !! y = None →
  Δ !! x = None →
  Δ' !! x = None →
  is_closed_expr_set ({[x]} ∪ dom stringset Δ ∪ dom stringset Γ) e →
  is_closed_expr_set ({[y]} ∪ dom stringset Δ' ∪ dom stringset Γ) e' →
  (Γ &; Δ ⊢ₗ e : (x : τ1)) -∗
  (Γ &; Δ' ⊢ₗ e' : (y : τ2)) -∗
  (Γ &; Δ ∪ Δ' ⊢ₗ (let: x := start_chan (λ: x, e) in
                   send y x;;
                   e') : (y : τ1 ⊗ τ2)).
Proof.
  intros Hxy HΔ Hx0 Hy0 Hy1 Hy2 Hx1 Hx2 Hcle Hcle'. iIntros "#H1 #H2". iModIntro.
  iIntros (ss cs oy Hsscs) "#Hss HΔ Hoy". wp_pures.
  rewrite lookup_delete_ne// !lookup_delete lookup_insert.
  simpl.
  rewrite big_sepM2_union_l //.
  iDestruct "HΔ" as (cs1 cs2 Hcs ->) "[HΔ HΔ']".

  iAssert (⌜dom stringset Δ = dom stringset cs1⌝)%I as %Hdom1.
  { by rewrite (big_sepM2_dom _ Δ). }
  iAssert (⌜dom stringset Δ' = dom stringset cs2⌝)%I as %Hdom2.
  { by rewrite (big_sepM2_dom _ Δ'). }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ Γ). }
  assert_not_in_map cs1 y.
  assert_not_in_map cs2 y.
  assert_not_in_map cs1 x.
  assert_not_in_map cs2 x.
  assert_not_in_map ss x.
  assert_not_in_map ss y.

  eapply map_disjoint_union_r in Hsscs. destruct Hsscs as [Hsscs1 Hsscs2].
  wp_smart_apply (start_chan_spec (iProto_dual (interp_ty τ1)) with "[H1 HΔ]").
  { iNext. iIntros (c) "Hc".
    rewrite iProto_dual_involutive. wp_pures.
    iSpecialize ("H1" with "[%] Hss HΔ Hc"); eauto.
    rewrite -subst_map_insert.
    assert (subst_map (<[x:=c]> (ss ∪ cs1)) e
         = subst_map (<[x:=c]> (<[y:=oy]> (ss ∪ (cs1 ∪ cs2)))) e) as ->.
    { rewrite assoc_L.
      eapply subst_map_fact_0; eauto.
      - rewrite dom_union_L -Hdom1 -Hdom0.
        assert (({[x]} ∪ (dom stringset Γ ∪ dom stringset Δ)) =
                ({[x]} ∪ dom stringset Δ ∪ dom stringset Γ)) as ->.
        { set_unfold; tauto. }
        done.
      - eapply lookup_union_None. tauto.
    }
    iApply (wp_wand with "H1"); eauto. }
  iIntros (xc) "Hxc". wp_pures.
  case_decide; last naive_solver.
  wp_send with "[$Hxc]". wp_pures.
  iSpecialize ("H2" with "[%] Hss HΔ' Hoy"); eauto.
  rewrite -subst_map_insert. rewrite insert_commute //.
  rewrite assoc_L (map_union_comm ss cs1) //.
  rewrite -assoc_L.
  rewrite -(subst_map_fact_1 cs1 (ss ∪ cs2) y x)//.
  - rewrite dom_union_L -Hdom0 -Hdom2.
    cut (({[y]} ∪ (dom stringset Γ ∪ dom stringset Δ')) =
         ({[y]} ∪ dom stringset Δ' ∪ dom stringset Γ)); first by intros ->.
    set_unfold. tauto.
  - eapply lookup_union_None. tauto.
  - eapply map_disjoint_union_r. eauto.
Qed.

Lemma ttimes_left (Γ Δ : tyctx) τ1 τ2 (x y : string) (c : string) σ e :
  x ≠ y →
  x ≠ c →
  y ≠ c →
  Γ !! x = None →
  Γ !! y = None →
  Δ !! x = None →
  Δ !! y = None →
  (Γ &; (<[y:=τ1]>(<[x:=τ2]>Δ)) ⊢ₗ e : (c : σ)) -∗
  (Γ &; (<[x:=τ1 ⊗ τ2]>Δ) ⊢ₗ (let: y := recv x in e) : (c : σ)).
Proof.
  intros Hxy Hxc Hyc Hx0 Hy0 Hx Hy. iIntros "#IH". iModIntro.
  iIntros (ss cs o Hsscs) "Hss Hcs Ho". simpl.
  rewrite lookup_insert_ne//.

  iAssert (⌜{[x]} ∪ dom stringset Δ = dom stringset cs⌝)%I as %Hdom.
  { by rewrite (big_sepM2_dom _ _ cs) dom_insert_L. }
  iAssert (⌜dom stringset Γ = dom stringset ss⌝)%I as %Hdom0.
  { by rewrite (big_sepM2_dom _ _ ss). }

  assert_in_map_ cs x cx Hcx.
  assert_not_in_map cs y.
  assert_not_in_map ss x.
  assert_not_in_map ss y.
  rewrite lookup_union_r // Hcx.

  rewrite (big_sepM2_insert_acc _ _ cs); eauto; last first.
  { eapply lookup_insert. }
  iDestruct "Hcs" as "[Hx Hcs]". iSimpl in "Hx".
  wp_recv (cy) as "Hy". wp_pures.
  rewrite -subst_map_insert.
  iSpecialize ("Hcs" with "Hx").
  rewrite insert_insert (insert_id cs) //.
  iSpecialize ("IH" $! ss (<[y:=cy]>(<[x:=cx]> cs)) with "[%] Hss [Hcs Hy] Ho").
  { eapply map_disjoint_insert_r; split; eauto.
    eapply map_disjoint_insert_r. split; eauto. }
  { iApply big_sepM2_insert.
    - rewrite lookup_insert_ne//.
    - rewrite lookup_insert_ne//.
    - iFrame "Hy".
      rewrite (insert_id cs)//. }
  rewrite (insert_id cs)//.
  rewrite insert_commute//.
  rewrite -insert_union_r//.
Qed.

End interp.
