From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang Require Import assert.

(** Immutable ML-style functional lists *)
Fixpoint llist `{heapG Σ} (l : loc) (vs : list val) : iProp Σ :=
  match vs with
  | [] => l ↦ NONEV
  | v :: vs => ∃ l' : loc, l ↦ SOMEV (v,#l') ∗ llist l' vs
  end%I.
Arguments llist : simpl never.

Definition lnil : val := λ: <>, ref NONE.
Definition lcons : val := λ: "x" "l", "l" <- SOME ("x", ref (!"l"));; "l".

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

Section lists.
Context `{heapG Σ}.
Implicit Types i : nat.
Implicit Types v : val.
Implicit Types vs : list val.
Local Arguments llist {_ _} _ !_ /.

Lemma lnil_spec :
  {{{ True }}} lnil #() {{{ l, RET #l; llist l [] }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_alloc l. by iApply "HΦ". Qed.

Lemma lcons_spec l v vs :
  {{{ llist l vs }}} lcons v #l {{{ RET #l; llist l (v :: vs) }}}.
Proof.
  iIntros (Φ) "Hll HΦ". wp_lam. destruct vs as [|v' vs]; simpl; wp_pures.
  - wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (l') "[Hl Hll]".
    wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lisnil_spec l vs:
  {{{ llist l vs }}}
    lisnil #l
  {{{ RET #(if vs is [] then true else false); llist l vs }}}.
Proof.
  iIntros (Φ) "Hll HΦ". wp_lam. destruct vs as [|v' vs]; simpl; wp_pures.
  - wp_load; wp_pures. by iApply "HΦ".
  - iDestruct "Hll" as (l') "[Hl Hll]".
    wp_load; wp_pures. iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lhead_spec l v vs :
  {{{ llist l (v :: vs) }}} lhead #l {{{ RET v; llist l (v :: vs) }}}.
Proof.
  iIntros (Φ) "/=". iDestruct 1 as (l') "[Hl Hll]". iIntros "HΦ".
  wp_lam. wp_load; wp_pures. iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lpop_spec l v vs :
  {{{ llist l (v :: vs) }}} lpop #l {{{ RET v; llist l vs }}}.
Proof.
  iIntros (Φ) "/=". iDestruct 1 as (l') "[Hl Hll]". iIntros "HΦ".
  wp_lam. wp_load. wp_pures. destruct vs as [|v' vs]; simpl; wp_pures.
  - wp_load. wp_store. wp_pures. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (l'') "[Hl' Hll]".
    wp_load. wp_store. wp_pures. iApply "HΦ"; eauto with iFrame.
Qed.

Lemma llookup_spec l i vs v :
  vs !! i = Some v →
  {{{ llist l vs }}} llookup #l #i {{{ RET v; llist l vs }}}.
Proof.
  iIntros (Hi Φ) "Hll HΦ".
  iInduction vs as [|v' vs] "IH" forall (l i v Hi Φ); [done|simpl; wp_rec; wp_pures].
  destruct i as [|i]; simplify_eq/=; wp_pures.
  - wp_apply (lhead_spec with "Hll"); iIntros "Hll". by iApply "HΦ".
  - iDestruct "Hll" as (l') "[Hl' Hll]". wp_load; wp_pures.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply ("IH" with "[//] Hll"); iIntros "Hll". iApply "HΦ"; eauto with iFrame.
Qed.

Lemma llength_spec l vs :
  {{{ llist l vs }}} llength #l {{{ RET #(length vs); llist l vs }}}.
Proof.
  iIntros (Φ) "Hll HΦ".
  iInduction vs as [|v vs] "IH" forall (l Φ); simpl; wp_rec; wp_pures.
  - wp_load; wp_pures. by iApply "HΦ".
  - iDestruct "Hll" as (l') "[Hl' Hll]". wp_load; wp_pures.
    wp_apply ("IH" with "Hll"); iIntros "Hll". wp_pures.
    rewrite (Nat2Z.inj_add 1). iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lapp_spec l1 l2 vs1 vs2 :
  {{{ llist l1 vs1 ∗ llist l2 vs2 }}}
    lapp #l1 #l2
  {{{ RET #(); llist l1 (vs1 ++ vs2) ∗ l2 ↦ - }}}.
Proof.
  iIntros (Φ) "[Hll1 Hll2] HΦ".
  iInduction vs1 as [|v1 vs1] "IH" forall (l1 Φ); simpl; wp_rec; wp_pures.
  - wp_load. wp_pures. destruct vs2 as [|v2 vs2]; simpl; wp_pures.
    + wp_load. wp_store. iApply "HΦ". eauto with iFrame.
    + iDestruct "Hll2" as (l2') "[Hl2 Hll2]". wp_load. wp_store.
      iApply "HΦ". iSplitR "Hl2"; eauto 10 with iFrame.
  - iDestruct "Hll1" as (l') "[Hl1 Hll1]". wp_load; wp_pures.
    wp_apply ("IH" with "Hll1 Hll2"); iIntros "[Hll Hl2]".
    iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lprep_spec l1 l2 vs1 vs2 :
  {{{ llist l1 vs2 ∗ llist l2 vs1 }}}
    lprep #l1 #l2
  {{{ RET #(); llist l1 (vs1 ++ vs2) ∗ l2 ↦ - }}}.
Proof.
  iIntros (Φ) "[Hll1 Hll2] HΦ". wp_lam.
  wp_apply (lapp_spec with "[$Hll2 $Hll1]"); iIntros "[Hll2 Hl1]".
  iDestruct "Hl1" as (w) "Hl1". destruct (vs1 ++ vs2) as [|v vs]; simpl; wp_pures.
  - wp_load. wp_store. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll2" as (l') "[Hl2 Hll2]". wp_load. wp_store.
    iApply "HΦ"; iSplitR "Hl2"; eauto with iFrame.
Qed.

Lemma lsnoc_spec l vs v :
  {{{ llist l vs }}} lsnoc #l v {{{ RET #(); llist l (vs ++ [v]) }}}.
Proof.
  iIntros (Φ) "Hll HΦ".
  iInduction vs as [|v' vs] "IH" forall (l Φ); simpl; wp_rec; wp_pures.
  - wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (l') "[Hl Hll]". wp_load; wp_pures.
    wp_apply ("IH" with "Hll"); iIntros "Hll". iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lsplit_at_spec l vs (n : nat) :
  {{{ llist l vs }}}
    lsplit_at #l #n
  {{{ k, RET #k; llist l (take n vs) ∗ llist k (drop n vs) }}}.
Proof.
  iIntros (Φ) "Hll HΦ".
  iInduction vs as [|v vs] "IH" forall (l n Φ); simpl; wp_rec; wp_pures.
  - destruct n as [|n]; simpl; wp_pures.
    + wp_load. wp_alloc k. wp_store. iApply "HΦ"; iFrame.
    + wp_load. wp_alloc k. iApply "HΦ"; iFrame.
  - iDestruct "Hll" as (l') "[Hl Hll]". destruct n as [|n]; simpl; wp_pures.
    + wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
    + wp_load; wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
      wp_apply ("IH" with "[$]"); iIntros (k) "[Hll Hlk]".
      iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lsplit_spec l vs :
  {{{ llist l vs }}}
    lsplit #l
  {{{ k ws1 ws2, RET #k; ⌜ vs = ws1 ++ ws2 ⌝ ∗ llist l ws1 ∗ llist k ws2 }}}.
Proof.
  iIntros (Φ) "Hl HΦ". wp_lam.
  wp_apply (llength_spec with "Hl"); iIntros "Hl". wp_pures.
  rewrite Z.quot_div_nonneg; [|lia..]. rewrite -(Z2Nat_inj_div _ 2).
  wp_apply (lsplit_at_spec with "Hl"); iIntros (k) "[Hl Hk]".
  iApply "HΦ". iFrame. by rewrite take_drop.
Qed.
End lists.
