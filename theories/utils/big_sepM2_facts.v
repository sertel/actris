From stdpp Require Import countable fin_sets functions.
From iris.algebra Require Export big_op.
From iris.algebra Require Import list gmap.
From iris.bi Require Import derived_laws_later big_op.
From iris.proofmode Require Import tactics.
From iris.prelude Require Import options.
Import interface.bi derived_laws.bi derived_laws_later.bi.

Section big_op_lemma.
Context `{Countable K}.
Context {PROP : bi}.

Local Lemma owohelper {A B} (Φ : K → A → B → PROP)
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
  iDestruct "H2" as (n1 n2) "[Hn12 [H2 H3]]".
  iDestruct "Hn12" as %Hn12.
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

Lemma big_sepM2_union_l {A B} (Φ : K → A → B → PROP)
      (m1 m2 : gmap K A) (n : gmap K B) :
  m1 ##ₘ m2 →
  ([∗ map] k↦x;y ∈ (m1 ∪ m2);n, Φ k x y) ⊢
  (∃ n1 n2, ⌜n1 ##ₘ n2⌝ ∗ ⌜n = n1 ∪ n2⌝
                        ∗ ([∗ map] k↦x;y ∈ m1;n1, Φ k x y)
                        ∗ ([∗ map] k↦x;y ∈ m2;n2, Φ k x y)).
Proof.
  intros Hmm. rewrite owohelper; eauto.
  iDestruct 1 as (n1 n2) "[Hn12 [H1 H2]]".
  iDestruct "Hn12" as %->.
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
