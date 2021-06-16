From stdpp Require Import gmap fin_maps fin_sets stringmap.
From iris.heap_lang Require Export lang notation metatheory.
From iris.proofmode Require tactics.
From iris.bi Require Import big_op.
From iris.bi Require Import derived_laws_later.


(** ** [is_closed_expr] in terms of sets *)
Local Definition maybe_insert_binder (x : binder) (X : stringset) : stringset :=
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
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 | FAA e1 e2 | Xchg e1 e2 =>
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

(** ** Facts about the substitution *)
Lemma subst_map_agree_on_dom D m1 m2 e :
  is_closed_expr_set D e →
  filter (λ '(x,v), x ∈ D) m1 = filter (λ '(x,v), x ∈ D) m2 →
  subst_map m1 e = subst_map m2 e.
Proof.
  revert m1 m2 D.
  induction e=> /= m1 m2 D Hdom Heq; eauto; destruct_and?.
  all: try by (f_equiv; eapply IHe; eauto).
  all: try by (f_equiv; [ eapply IHe1 | eapply IHe2 ] ; eauto).
  all: try by (f_equiv; [ eapply IHe1 | eapply IHe2 | eapply IHe3 ] ; eauto).
  - case_match.
    + assert (filter (λ '(x, _), x ∈ D) m1 !! x = Some v) as Hm1x.
      { eapply map_filter_lookup_Some_2; eauto. }
      rewrite Heq in Hm1x.
      eapply map_filter_lookup_Some_1_1 in Hm1x.
      by rewrite Hm1x.
    + assert (filter (λ '(x, _), x ∈ D) m1 !! x = None) as Hm1x.
      { eapply map_filter_lookup_None_2; eauto. }
      rewrite Heq in Hm1x.
      eapply map_filter_lookup_None_1 in Hm1x.
      case_match; naive_solver.
  - f_equiv.
    eapply IHe; eauto.
    destruct x as [|x], f as [|f]; simpl in *; eauto.
    + eapply map_filter_strong_ext=>i v.
      set_unfold. eapply map_filter_strong_ext_2 in Heq.
      split.
      { move=> [[->|Hi] Hm1]; simplify_map_eq/=.
        destruct (decide (i = f)) as [->|?]; first by simplify_map_eq/=.
        move: Hm1. rewrite !lookup_delete_ne //.
        naive_solver. }
      { move=> [[->|Hi] Hm1]; simplify_map_eq/=.
        destruct (decide (i = f)) as [->|?]; first by simplify_map_eq/=.
        move: Hm1. rewrite !lookup_delete_ne //.
        naive_solver. }
    + eapply map_filter_strong_ext=>i v.
      set_unfold. eapply map_filter_strong_ext_2 in Heq.
      split.
      { move=> [[->|Hi] Hm1]; simplify_map_eq/=.
        destruct (decide (i = x)) as [->|?]; first by simplify_map_eq/=.
        move: Hm1. rewrite !lookup_delete_ne //.
        naive_solver. }
      { move=> [[->|Hi] Hm1]; simplify_map_eq/=.
        destruct (decide (i = x)) as [->|?]; first by simplify_map_eq/=.
        move: Hm1. rewrite !lookup_delete_ne //.
        naive_solver. }
    + eapply map_filter_strong_ext=>i v.
      set_unfold. eapply map_filter_strong_ext_2 in Heq.
      split.
      { move=> [[->|[->|Hi]] Hm1]; simplify_map_eq/=.
        + destruct (decide (f = x)) as [->|?]; simplify_map_eq/=.
        + destruct (decide (i = x)) as [->|?]; first by simplify_map_eq/=.
          destruct (decide (i = f)) as [->|?]; first by simplify_map_eq/=.
          move: Hm1. rewrite !lookup_delete_ne //.
          naive_solver. }
      { move=> [[->|[->|Hi]] Hm1]; simplify_map_eq/=.
        + destruct (decide (f = x)) as [->|?]; simplify_map_eq/=.
        + destruct (decide (i = x)) as [->|?]; first by simplify_map_eq/=.
          destruct (decide (i = f)) as [->|?]; first by simplify_map_eq/=.
          move: Hm1. rewrite !lookup_delete_ne //.
          naive_solver. }
Qed.


Lemma subst_map_agree_weaken e X m1 m2 :
  is_closed_expr_set X e →
  dom stringset m1 = X →
  m1 ⊆ m2 →
  subst_map m1 e = subst_map m2 e.
Proof.
  intros HXe Hdom Hsub.
  eapply subst_map_agree_on_dom; eauto.
  eapply map_filter_strong_ext.
  rewrite -Hdom. intros i x.
  revert Hsub. rewrite map_subseteq_spec.
  rewrite elem_of_dom. set_unfold.
  intros Hh. split; first naive_solver.
  intros [[y Hy] Hx]. rewrite Hy. naive_solver.
Qed.

Lemma subst_map_fact_0 m1 m2 x y xv yv e :
  is_closed_expr_set ({[x]} ∪ dom stringset m1) e →
  m1 !! y = None →
  m2 !! y = None →
  subst_map (<[x:=xv]> m1) e = subst_map (<[x:=xv]>(<[y:=yv]> (m1 ∪ m2))) e.
Proof.
  intros Hcl Hy1 Hy2.
  eapply subst_map_agree_weaken; eauto.
  - by rewrite dom_insert_L.
  - eapply insert_mono. etrans; first by eapply map_union_subseteq_l.
    eapply insert_subseteq.
    eapply lookup_union_None. naive_solver.
Qed.

Lemma subst_map_fact_1 m1 m2 x y xv yv e :
  is_closed_expr_set ({[x]} ∪ dom stringset m2) e →
  m1 !! y = None →
  m2 !! y = None →
  m1 ##ₘ m2 →
  subst_map (<[x:=xv]> m2) e = subst_map (<[x:=xv]>(<[y:=yv]> (m1 ∪ m2))) e.
Proof.
  intros Hcl Hy1 Hy2 ?.
  eapply subst_map_agree_weaken; eauto.
  - by rewrite dom_insert_L.
  - eapply insert_mono. etrans; first by eapply map_union_subseteq_r.
    eapply insert_subseteq.
    eapply lookup_union_None. naive_solver.
Qed.

Lemma subst_map_fact_2 m1 m2 x y xv yv e :
  is_closed_expr_set ({[x;y]} ∪ dom stringset m2) e →
  m1 !! y = None →
  m2 !! y = None →
  m1 ##ₘ m2 →
  subst_map (<[x:=xv]> (<[y:=yv]>m2)) e = subst_map (<[x:=xv]>(<[y:=yv]> (m1 ∪ m2))) e.
Proof.
  intros Hcl Hy1 Hy2 ?.
  eapply subst_map_agree_weaken; eauto.
  - rewrite !dom_insert_L. set_solver.
  - do 2 eapply insert_mono. by eapply map_union_subseteq_r.
Qed.
