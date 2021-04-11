(** This file defines a separation logic representation predicates [llist] for
mutable linked-lists. It comes with a small library of operations (head, pop,
lookup, length, append, prepend, snoc, split). *)
From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang Require Import assert.

(**  *)
Fixpoint llist `{heapGS Σ} {A} (I : A → val → iProp Σ)
    (l : loc) (xs : list A) : iProp Σ :=
  match xs with
  | [] => l ↦ NONEV
  | x :: xs => ∃ (v : val) (l' : loc), I x v ∗ l ↦ SOMEV (v,#l') ∗ llist I l' xs
  end%I.
Arguments llist : simpl never.

Definition lnil : val := λ: <>, ref NONE.
Definition lcons : val := λ: "x" "l", "l" <- SOME ("x", ref (!"l")).

Definition lisnil : val := λ: "l",
  match: !"l" with
    SOME "p" => #false
  | NONE => #true
  end.

Definition lhead : val := λ: "l",
  match: !"l" with
    SOME "p" => Fst "p"
  | NONE => assert: #false
  end.

Definition lpop : val := λ: "l",
  match: !"l" with
    SOME "p" => "l" <- !(Snd "p");; Fst "p"
  | NONE => assert: #false
  end.

Definition llookup : val :=
  rec: "go" "l" "n" :=
    if: "n" = #0 then lhead "l" else
    match: !"l" with
      SOME "p" => "go" (Snd "p") ("n" - #1)
    | NONE => assert: #false
    end.

Definition llength : val :=
  rec: "go" "l" :=
    match: !"l" with
      NONE => #0
    | SOME "p" => #1 + "go" (Snd "p")
    end.

Definition lapp : val :=
  rec: "go" "l" "k" :=
    match: !"l" with
      NONE => "l" <- !"k"
    | SOME "p" => "go" (Snd "p") "k"
    end.
Definition lprep : val := λ: "l" "k",
  lapp "k" "l";; "l" <- !"k".

Definition lsnoc : val :=
  rec: "go" "l" "x" :=
    match: !"l" with
      NONE => "l" <- SOME ("x", ref NONE)
    | SOME "p" => "go" (Snd "p") "x"
    end.

Definition lsplit_at : val :=
  rec: "go" "l" "n" :=
    if: "n" ≤ #0 then let: "k" := ref (! "l") in "l" <- NONE;; "k" else
    match: !"l" with
      NONE => ref NONE
    | SOME "p" => "go" (Snd "p") ("n" - #1)
    end.

Definition lsplit : val := λ: "l", lsplit_at "l" (llength "l" `quot` #2).

Definition lreverse_at : val :=
  rec: "go" "l" "acc" :=
    match: !"l" with
      NONE => "acc"
    | SOME "p" => (lcons (Fst "p") "acc");; "go" (Snd "p") "acc"
    end.

Definition lreverse : val :=
  λ: "l", let: "l'" := ref (!"l") in
          "l" <- !(lreverse_at "l'" (lnil #())).

Definition lmap : val :=
  rec: "go" "f" "l" :=
  match: !"l" with
    NONE => "l"
  | SOME "p" =>
    let: "x" := "f" (Fst "p") in
    let: "l'" := "go" "f" (Snd "p") in
    "l" <- SOME ("x", "l'");; "l"
  end.

Definition liter : val :=
  rec: "go" "f" "l" :=
  match: !"l" with
    NONE => #()
  | SOME "p" => "f" (Fst "p");; "go" "f" (Snd "p")
  end.

Section lists.
Context `{heapGS Σ}.
Implicit Types i : nat.
Implicit Types l : loc.
Local Arguments llist {_ _ _} _ _ !_ /.

Lemma cons_length_inv {A : Type} (xs : list A) n :
  length xs = S n → ∃ x xs', xs = x :: xs'.
Proof. intros Hlen. destruct xs; [ inversion Hlen | eauto ]. Qed.

Lemma list_app_comm {A} (xs ys zs : list A) :
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
Proof. induction xs; [ eauto | by simpl; f_equiv ]. Qed.

Lemma llist_fmap {A B} (I : A → val → iProp Σ)
      (J : B → val → iProp Σ) (f : A → B) l xs :
  □ (∀ x v, I x v -∗ J (f x) v) -∗
  llist I l xs -∗ llist J l (f <$> xs).
Proof.
  iIntros "#Hf Hll". iInduction xs as [|x xs] "IH" forall (l); csimpl; auto.
  iDestruct "Hll" as (v l') "(Hx & Hl & Hll)". iExists _, _. iFrame "Hl".
  iSplitL "Hx". by iApply "Hf". by iApply "IH".
Qed.

Lemma llist_out {A : Type} l (xs : list A) (I : A → val → iProp Σ) :
  (llist I l xs)%I -∗
  ∃ vs, (llist (λ x v, ⌜x = v⌝) l vs ∗
    [∗list] k↦x;v ∈ xs;vs, I x v)%I.
Proof.
  iIntros "Hl".
  iInduction xs as [|x xs] "IH" forall (l).
  - eauto.
  - iDestruct "Hl" as (v l') "[HI [Hl Hrec]]".
    iDestruct ("IH" with "Hrec") as (vs) "[Hxs HIs]".
    iExists (v::vs).
    iSplitR "HI HIs"; [ | by iFrame ].
    iExists v, l'.
    iSplit; [ done | ].
    by iFrame "Hl".
Qed.

Lemma llist_in {A : Type} l (xs : list A) (vs : list val) (I : A → val → iProp Σ) :
  (llist (λ x v, ⌜x = v⌝) l vs ∗
    [∗list] k↦x;v ∈ xs;vs, I x v)%I -∗
  (llist I l xs)%I.
Proof.
  iIntros "[Hl HIs]".
  iInduction xs as [|x xs] "IH" forall (l vs).
  - by iDestruct (big_sepL2_nil_inv_l with "HIs") as %->.
  - iDestruct (big_sepL2_cons_inv_l with "HIs") as (v vs' ->) "HIs".
    iDestruct "Hl" as (v' l' Hv) "[Hl Hrec]".
    iDestruct "HIs" as "[HI HIs]".
    iDestruct ("IH" with "Hrec HIs") as "Hxs".
    iExists v, l'.
    rewrite Hv.
    by iFrame "HI Hl".
Qed.

Lemma llist_unfold_vals {A : Type} l (xs : list A) (I : A → val → iProp Σ) :
  (llist I l xs)%I -∗
  ∃ vs, ⌜length vs = length xs⌝ ∗ (llist (λ x v, ⌜x.1 = v⌝ ∗ I x.2 v) l (zip vs xs)).
Proof.
  iIntros "Hl".
  iInduction xs as [|x xs] "IH" forall (l).
  - iExists []. eauto.
  - iDestruct "Hl" as (v l') "[HI [Hl Hrec]]".
    iDestruct ("IH" with "Hrec") as (vs Hlen) "HIs".
    iExists (v::vs).
    iSplit.
    { iPureIntro. simpl. by rewrite Hlen. }
    iExists v, l'.
    by iFrame.
Qed.

Lemma llist_fold_vals {A : Type} l (xs : list A) (I : A → val → iProp Σ) vs :
  length vs = length xs →
  (llist (λ x v, ⌜x.1 = v⌝ ∗ I x.2 v) l (zip vs xs)) -∗
  (llist I l xs)%I.
Proof.
  iIntros (Hlen) "Hl".
  iRevert (Hlen).
  iInduction xs as [|x xs] "IH" forall (l vs); iIntros (Hlen).
  - by rewrite (nil_length_inv vs).
  - destruct (cons_length_inv vs _ Hlen) as [v [vs' ->]].
    iDestruct "Hl" as (v' l') "[HI [Hl Hrec]]".
    iDestruct ("IH" with "Hrec []") as "HIs"; [ by eauto | ].
    iDestruct "HI" as (<-) "HI".
    iExists v, l'.
    by iFrame.
Qed.

Lemma llist_exists {A B : Type} l (xs : list A) (P : A → val → B → iProp Σ) :
  (llist (λ x v, ∃ y : B, P x v y) l xs)%I -∗
  (∃ ys : list B, llist (λ _ _, True) l xs ∗
    [∗list] k↦x;y ∈ xs;ys, ∃ v, P x v y)%I.
Proof.
  iIntros "Hl".
  iInduction xs as [|x xs] "IH" forall (l).
  - iExists []. eauto.
  - iDestruct "Hl" as (v l') "[HI [Hl Hrec]]".
    iDestruct "HI" as (y) "HP".
    iDestruct ("IH" with "Hrec") as (ys) "[Hxs Hys]".
    iExists (y::ys).
    iFrame "Hys".
    iSplitR "HP"; [ | eauto ].
    iExists v, l'.
    by iFrame.
Qed.

Lemma lnil_spec {A} (I : A → val → iProp Σ) :
  {{{ True }}} lnil #() {{{ l, RET #l; llist I l [] }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_alloc l. by iApply "HΦ". Qed.

Lemma lcons_spec {A} I l x (xs : list A) v :
  {{{ llist I l xs ∗ I x v }}} lcons v #l {{{ RET #(); llist I l (x :: xs) }}}.
Proof.
  iIntros (Φ) "[Hll Hx] HΦ". wp_lam. destruct xs as [|x' xs]; simpl; wp_pures.
  - wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (v' l') "(HIx' & Hl & Hll)".
    wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto 10 with iFrame.
Qed.

Lemma lisnil_spec {A} I l (xs : list A) :
  {{{ llist I l xs }}}
    lisnil #l
  {{{ RET #(if xs is [] then true else false); llist I l xs }}}.
Proof.
  iIntros (Φ) "Hll HΦ". wp_lam. destruct xs as [|x xs]; simpl; wp_pures.
  - wp_load; wp_pures. by iApply "HΦ".
  - iDestruct "Hll" as (v l') "(HIx & Hl & Hll)".
    wp_load; wp_pures. iApply "HΦ"; eauto with iFrame.
Qed.

(** Not the nicest spec, they leaks *)
Lemma lhead_spec_aux {A} I l x (xs : list A) :
  {{{ llist I l (x :: xs) }}}
    lhead #l
  {{{ v (l' : loc), RET v; I x v ∗ l ↦ SOMEV (v,#l') ∗ llist I l' xs }}}.
Proof.
  iIntros (Φ) "/=". iDestruct 1 as (v l') "(HIx & Hl & Hll)". iIntros "HΦ".
  wp_lam. wp_load; wp_pures. iApply "HΦ"; eauto with iFrame.
Qed.
Lemma lpop_spec_aux {A} I l l' v (xs : list A) :
  {{{ l ↦ SOMEV (v,#l') ∗ llist I l' xs }}} lpop #l {{{ RET v; llist I l xs }}}.
Proof.
  iIntros (Φ) "[Hl Hll] HΦ".
  wp_lam. wp_load. wp_pures. destruct xs as [|x' xs]; simpl; wp_pures.
  - wp_load. wp_store. wp_pures. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (v' l'') "(HIx' & Hl' & Hll)".
    wp_load. wp_store. wp_pures. iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lhead_spec {A} I l x (xs : list A) :
  {{{ llist I l (x :: xs) }}}
    lhead #l
  {{{ v, RET v; I x v ∗ (I x v -∗ llist I l (x :: xs)) }}}.
Proof.
  iIntros (Φ) "Hll HΦ". wp_smart_apply (lhead_spec_aux with "Hll").
  iIntros (v l') "(HIx&?&?)". iApply "HΦ". iIntros "{$HIx} HIx".
  simpl; eauto with iFrame.
Qed.

Lemma lpop_spec {A} I l x (xs : list A) :
  {{{ llist I l (x :: xs) }}} lpop #l {{{ v, RET v; I x v ∗ llist I l xs }}}.
Proof.
  iIntros (Φ) "/=". iDestruct 1 as (v l') "(HIx & Hl & Hll)". iIntros "HΦ".
  wp_smart_apply (lpop_spec_aux with "[$]"); iIntros "Hll". iApply "HΦ"; iFrame.
Qed.

Lemma llookup_spec {A} I l i (xs : list A) x :
  xs !! i = Some x →
  {{{ llist I l xs }}}
    llookup #l #i
  {{{ v, RET v; I x v ∗ (I x v -∗ llist I l xs) }}}.
Proof.
  iIntros (Hi Φ) "Hll HΦ".
  iInduction xs as [|x' xs] "IH" forall (l i x Hi Φ); [done|simpl; wp_rec; wp_pures].
  destruct i as [|i]; simplify_eq/=; wp_pures.
  - wp_smart_apply (lhead_spec with "Hll"); iIntros (v) "[HI Hll]".
    iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (v l') "(HIx' & Hl' & Hll)". wp_load; wp_pures.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_smart_apply ("IH" with "[//] Hll"); iIntros (v') "[HIx Hll]".
    iApply "HΦ". iIntros "{$HIx} HIx". iExists v, l'. iFrame. by iApply "Hll".
Qed.

Lemma llength_spec {A} I l (xs : list A) :
  {{{ llist I l xs }}} llength #l {{{ RET #(length xs); llist I l xs }}}.
Proof.
  iIntros (Φ) "Hll HΦ".
  iInduction xs as [|x xs] "IH" forall (l Φ); simpl; wp_rec; wp_pures.
  - wp_load; wp_pures. by iApply "HΦ".
  - iDestruct "Hll" as (v l') "(HIx & Hl' & Hll)". wp_load; wp_pures.
    wp_smart_apply ("IH" with "Hll"); iIntros "Hll". wp_pures.
    rewrite (Nat2Z.inj_add 1). iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lapp_spec {A} I l1 l2 (xs1 xs2 : list A) :
  {{{ llist I l1 xs1 ∗ llist I l2 xs2 }}}
    lapp #l1 #l2
  {{{ RET #(); llist I l1 (xs1 ++ xs2) ∗ (∃ v, l2 ↦ v) }}}.
Proof.
  iIntros (Φ) "[Hll1 Hll2] HΦ".
  iInduction xs1 as [|x1 xs1] "IH" forall (l1 Φ); simpl; wp_rec; wp_pures.
  - wp_load. wp_pures. destruct xs2 as [|x2 xs2]; simpl; wp_pures.
    + wp_load. wp_store. iApply "HΦ". eauto with iFrame.
    + iDestruct "Hll2" as (v2 l2') "(HIx2 & Hl2 & Hll2)". wp_load. wp_store.
      iApply "HΦ". iSplitR "Hl2"; eauto 10 with iFrame.
  - iDestruct "Hll1" as (v1 l') "(HIx1 & Hl1 & Hll1)". wp_load; wp_pures.
    wp_smart_apply ("IH" with "Hll1 Hll2"); iIntros "[Hll Hl2]".
    iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lprep_spec {A} I l1 l2 (xs1 xs2 : list A) :
  {{{ llist I l1 xs2 ∗ llist I l2 xs1 }}}
    lprep #l1 #l2
  {{{ RET #(); llist I l1 (xs1 ++ xs2) ∗ (∃ v, l2 ↦ v) }}}.
Proof.
  iIntros (Φ) "[Hll1 Hll2] HΦ". wp_lam.
  wp_smart_apply (lapp_spec with "[$Hll2 $Hll1]"); iIntros "[Hll2 Hl1]".
  iDestruct "Hl1" as (w) "Hl1". destruct (xs1 ++ xs2) as [|x xs]; simpl; wp_pures.
  - wp_load. wp_store. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll2" as (v l') "(HIx & Hl2 & Hll2)". wp_load. wp_store.
    iApply "HΦ"; iSplitR "Hl2"; eauto with iFrame.
Qed.

Lemma lsnoc_spec {A} I l (xs : list A) x v :
  {{{ llist I l xs ∗ I x v }}} lsnoc #l v {{{ RET #(); llist I l (xs ++ [x]) }}}.
Proof.
  iIntros (Φ) "[Hll HIx] HΦ".
  iInduction xs as [|x' xs] "IH" forall (l Φ); simpl; wp_rec; wp_pures.
  - wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (v' l') "(HIx' & Hl & Hll)". wp_load; wp_pures.
    wp_smart_apply ("IH" with "Hll HIx"); iIntros "Hll". iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lsplit_at_spec {A} I l (xs : list A) (n : nat) :
  {{{ llist I l xs }}}
    lsplit_at #l #n
  {{{ k, RET #k; llist I l (take n xs) ∗ llist I k (drop n xs) }}}.
Proof.
  iIntros (Φ) "Hll HΦ".
  iInduction xs as [|x xs] "IH" forall (l n Φ); simpl; wp_rec; wp_pures.
  - destruct n as [|n]; simpl; wp_pures.
    + wp_load. wp_alloc k. wp_store. iApply "HΦ"; by iFrame.
    + wp_load. wp_alloc k. iApply "HΦ"; by iFrame.
  - iDestruct "Hll" as (v l') "(HIx & Hl & Hll)". destruct n as [|n]; simpl; wp_pures.
    + wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
    + wp_load; wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
      wp_smart_apply ("IH" with "[$]"); iIntros (k) "[Hll Hlk]".
      iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lsplit_spec {A} I l (xs : list A) :
  {{{ llist I l xs }}}
    lsplit #l
  {{{ k xs1 xs2, RET #k; ⌜ xs = xs1 ++ xs2 ⌝ ∗ llist I l xs1 ∗ llist I k xs2 }}}.
Proof.
  iIntros (Φ) "Hl HΦ". wp_lam.
  wp_smart_apply (llength_spec with "Hl"); iIntros "Hl". wp_pures.
  rewrite Z.quot_div_nonneg; [|lia..]. rewrite -(Nat2Z_inj_div _ 2).
  wp_smart_apply (lsplit_at_spec with "Hl"); iIntros (k) "[Hl Hk]".
  iApply "HΦ". iFrame. by rewrite take_drop.
Qed.

Lemma lreverse_at_spec {A} I l (xs : list A) acc ys :
  {{{ llist I l xs ∗ llist I acc ys }}}
    lreverse_at #l #acc
  {{{ l', RET #l'; llist I l' (reverse xs ++ ys) }}}.
Proof.
  iIntros (Φ) "[Hl Hacc] HΦ".
  iInduction xs as [|x xs] "IH" forall (l acc Φ ys); simpl; wp_lam.
  - wp_load. wp_pures. iApply "HΦ". iApply "Hacc".
  - iDestruct "Hl" as (v l') "[HI [Hl Hl']]".
    wp_load. wp_smart_apply (lcons_spec with "[$Hacc $HI]").
    iIntros "Hacc". wp_smart_apply ("IH" with "Hl' Hacc").
    iIntros (l'') "Hl''". iApply "HΦ".
    rewrite reverse_cons -assoc_L. iApply "Hl''".
Qed.

Lemma lreverse_spec {A} I l (xs : list A) :
  {{{ llist I l xs }}}
    lreverse #l
  {{{ RET #(); llist I l (reverse xs) }}}.
Proof.
  iIntros (Φ) "Hl HΦ". wp_lam.
  destruct xs as [|x xs]; simpl.
  - wp_load. wp_alloc l' as "Hl'".
    wp_smart_apply (lnil_spec with "[//]").
    iIntros (lnil) "Hlnil".
    iAssert (llist I l' []) with "Hl'" as "Hl'".
    wp_smart_apply (lreverse_at_spec with "[$Hl' $Hlnil]").
    iIntros (l'') "Hl''".
    wp_load. wp_store. iApply "HΦ". rewrite right_id_L. iApply "Hl".
  - iDestruct "Hl" as (v lcons) "[HI [Hlcons Hrec]]".
    wp_load. wp_alloc l' as "Hl'".
    wp_smart_apply (lnil_spec with "[//]").
    iIntros (lnil) "Hlnil".
    wp_smart_apply (lreverse_at_spec _ _ (x :: xs) with "[Hl' HI Hrec $Hlnil]").
    { simpl; eauto with iFrame. }
    iIntros (l'') "Hl''". rewrite right_id_L. destruct (reverse _) as [|y ys].
    + wp_load. wp_store. by iApply "HΦ".
    + simpl. iDestruct "Hl''" as (v' lcons') "[HI [Hcons Hrec]]".
      wp_load. wp_store.
      iApply "HΦ". eauto with iFrame.
Qed.

Lemma lmap_fmap_spec {A B} (f : A → B) (fv : val) l (xs : list A)
      (I : A → val → iProp Σ) (J : B → val → iProp Σ) R :
  (∀ x v, {{{ I x v ∗ R }}} fv v {{{ w, RET w; J (f x) w ∗ R }}})%I -∗
  {{{ llist I l xs  ∗ R }}}
    lmap fv #l
  {{{ RET #l; llist J l (f <$> xs) ∗ R }}}.
Proof.
  iIntros "#Hf" (Φ) "!> [Hl HR] HΦ".
  iInduction xs as [|x xs] "IH" forall (l Φ); simpl; wp_lam.
  - wp_load. wp_pures. iApply "HΦ". by iFrame.
  - iDestruct "Hl" as (v lcons) "[HI [Hlcons Hrec]]".
    wp_load. wp_pures.
    wp_apply ("Hf" with "[$HI $HR]").
    iIntros (w) "[HJ HR]". wp_pures.
    wp_apply ("IH" with "Hrec HR").
    iIntros "[Hl HR]".
    wp_pures.
    wp_store.
    iIntros "!>".
    iApply "HΦ".
    eauto with iFrame.
Qed.

Lemma lmap_spec {A} (fv : val) l (xs : list A)
      (I : A → val → iProp Σ) (J : A → val → iProp Σ) R :
  (∀ x v, {{{ I x v ∗ R }}} fv v {{{ RET v; J x v ∗ R }}})%I -∗
  {{{ llist I l xs ∗ R }}}
    lmap fv #l
  {{{ RET #l; llist J l xs ∗ R }}}.
Proof.
  iIntros "#Hf" (Φ) "!> [Hl HR] HΦ".
  iInduction xs as [|x xs] "IH" forall (l Φ); simpl; wp_lam.
  - wp_load. wp_pures. iApply "HΦ". by iFrame.
  - iDestruct "Hl" as (v lcons) "[HI [Hlcons Hrec]]".
    wp_load. wp_pures.
    wp_apply ("Hf" with "[$HI $HR]").
    iIntros "[HJ HR]". wp_pures.
    wp_apply ("IH" with "Hrec HR").
    iIntros "[Hl HR]".
    wp_pures.
    wp_store.
    iIntros "!>".
    iApply "HΦ".
    iFrame.
    iExists _, _. iFrame.
Qed.

Lemma liter_spec_aux {A} (fv : val) l (xs ys : list A)
      (I : A → val → iProp Σ) (J : A → val → iProp Σ) R :
  (∀ xs x v, {{{ I x v ∗ R xs }}} fv v {{{ w, RET w; J x v ∗ R (xs ++ [x]) }}})%I -∗
  {{{ llist I l xs ∗ R ys }}}
    liter fv #l
  {{{ RET #(); llist J l xs ∗ R (ys ++ xs) }}}.
Proof.
  iIntros "#Hf" (Φ) "!> [Hl HR] HΦ".
  iInduction xs as [|x xs] "IH" forall (l ys Φ); simpl; wp_lam.
  - wp_load. wp_pures. iApply "HΦ". rewrite app_nil_r. by iFrame.
  - iDestruct "Hl" as (v lcons) "[HI [Hlcons Hrec]]".
    wp_load. wp_pures.
    wp_apply ("Hf" with "[$HI $HR]").
    iIntros (w) "[HJ HR]".
    wp_smart_apply ("IH" with "Hrec HR").
    iIntros "[Hl HR]".
    iApply "HΦ".
    rewrite list_app_comm.
    iFrame.
    iExists _, _. iFrame.
Qed.

Lemma liter_spec {A} (fv : val) l (xs : list A)
      (I : A → val → iProp Σ) (J : A → val → iProp Σ) R :
  (∀ xs x v, {{{ I x v ∗ R xs }}} fv v {{{ w, RET w; J x v ∗ R (xs ++ [x]) }}})%I -∗
  {{{ llist I l xs ∗ R [] }}}
    liter fv #l
  {{{ RET #(); llist J l xs ∗ R xs }}}.
Proof. iApply liter_spec_aux. Qed.

End lists.
