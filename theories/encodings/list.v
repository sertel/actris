From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang Require Import assert.

(** Immutable ML-style functional lists *)
Fixpoint is_list (hd : val) (xs : list val) : Prop :=
  match xs with
  | [] => hd = NONEV
  | x :: xs => ∃ hd', hd = SOMEV (x,hd') ∧ is_list hd' xs
  end.

Definition lnil : val := λ: <>, NONEV.
Definition lcons : val := λ: "x" "l", SOME ("x", "l").

Definition lhead : val := λ: "l",
  match: "l" with
    SOME "p" => Fst "p"
  | NONE => assert: #false
  end.
Definition ltail : val := λ: "l",
  match: "l" with
    SOME "p" => Snd "p"
  | NONE => assert: #false
  end.

Definition llookup : val :=
  rec: "go" "n" "l" :=
    if: "n" = #0 then lhead "l" else
    let: "l" := ltail "l" in "go" ("n" - #1) "l".

Definition linsert : val :=
  rec: "go" "n" "x" "l" :=
    if: "n" = #0 then let: "l" := ltail "l" in lcons "x" "l" else
    let: "k" := ltail "l" in
    let: "k" := "go" ("n" - #1) "x" "k" in
    lcons (lhead "l") "k".

Definition lreplicate : val :=
  rec: "go" "n" "x" :=
    if: "n" = #0 then lnil #() else
    let: "l" := "go" ("n" - #1) "x" in lcons "x" "l".

Definition llist_member : val :=
  rec: "go" "x" "l" :=
    match: "l" with
      NONE => #false
    | SOME "p" =>
      if: Fst "p" = "x" then #true
      else let: "l" := (Snd "p")  in "go" "x" "l"
    end.

Definition llength : val :=
  rec: "go" "l" :=
    match: "l" with
      NONE => #0
    | SOME "p" => #1 + "go" (Snd "p")
    end.

Definition lsnoc : val :=
  rec: "go" "l" "x" :=
    match: "l" with
      SOME "p" => (lcons (Fst "p") ("go" (Snd "p") "x"))
    | NONE => lcons "x" NONE
    end.

Section lists.
Context `{heapG Σ}.
Implicit Types i : nat.
Implicit Types v : val.

Lemma lnil_spec :
  {{{ True }}}
    lnil #()
  {{{ hd, RET hd; ⌜ is_list hd [] ⌝ }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. by iApply "HΦ". Qed.

Lemma lcons_spec hd vs v :
  {{{ ⌜ is_list hd vs ⌝ }}}
    lcons v hd
  {{{ hd', RET hd'; ⌜ is_list hd' (v :: vs) ⌝ }}}.
Proof.
  iIntros (Φ ?) "HΦ". wp_lam. wp_pures.
  iApply "HΦ". simpl; eauto.
Qed.

Lemma lhead_spec hd vs v :
  {{{ ⌜ is_list hd (v :: vs) ⌝ }}}
    lhead hd
  {{{ RET v; True }}}.
Proof. iIntros (Φ (hd'&->&?)) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma ltail_spec hd vs v :
  {{{ ⌜ is_list hd (v :: vs) ⌝ }}}
    ltail hd
  {{{ hd', RET hd'; ⌜ is_list hd' vs ⌝ }}}.
Proof. iIntros (Φ (hd'&->&?)) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma llookup_spec i hd vs v :
  vs !! i = Some v →
  {{{ ⌜ is_list hd vs ⌝ }}}
    llookup #i hd
  {{{ RET v; True }}}.
Proof.
  iIntros (Hi Φ Hl) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (hd i Hi Hl);
    destruct i as [|i]=> //; simplify_eq/=.
  { wp_lam. wp_pures. by iApply (lhead_spec with "[//]"). }
  wp_lam. wp_pures.
  wp_apply (ltail_spec with "[//]"); iIntros (hd' ?). wp_let.
  wp_op. rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l. by iApply "IH".
Qed.

Lemma linsert_spec i hd vs v :
  is_Some (vs !! i) →
  {{{ ⌜ is_list hd vs ⌝ }}}
    linsert #i v hd
  {{{ hd', RET hd'; ⌜ is_list hd' (<[i:=v]> vs) ⌝ }}}.
Proof.
  iIntros ([w Hi] Φ Hl) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (hd i Hi Hl Φ);
    destruct i as [|i]=> //; simplify_eq/=.
  { wp_lam. wp_pures. wp_apply (ltail_spec with "[//]"). iIntros (hd' ?).
    wp_let. by iApply (lcons_spec with "[//]"). }
  wp_lam; wp_pures.
  wp_apply (ltail_spec with "[//]"); iIntros (hd' ?). wp_let.
  wp_op. rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l.
  wp_apply ("IH" with "[//] [//]"). iIntros (hd'' ?). wp_let.
  wp_apply (lhead_spec with "[//]"); iIntros "_".
  by wp_apply (lcons_spec with "[//]").
Qed.

Lemma llist_member_spec hd vs v :
  {{{ ⌜ is_list hd vs ⌝ }}}
    llist_member v hd
  {{{ RET #(bool_decide (v ∈ vs)); True }}}.
Proof.
  iIntros (Φ Hl) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (hd Hl); simplify_eq/=.
  { wp_lam; wp_pures. by iApply "HΦ". }
  destruct Hl as (hd'&->&?). wp_lam; wp_pures.
  destruct (bool_decide_reflect (v' = v)) as [->|?]; wp_if.
  { rewrite (bool_decide_true (_ ∈ _ :: _)); last by left. by iApply "HΦ". }
  wp_proj. wp_let. iApply ("IH" with "[//]").
  destruct (bool_decide_reflect (v ∈ vs)).
  - by rewrite bool_decide_true; last by right.
  - by rewrite bool_decide_false ?elem_of_cons; last naive_solver.
Qed.

Lemma lreplicate_spec i v :
  {{{ True }}}
    lreplicate #i v
  {{{ hd, RET hd; ⌜ is_list hd (replicate i v) ⌝ }}}.
Proof.
  iIntros (Φ _) "HΦ". iInduction i as [|i] "IH" forall (Φ); simpl.
  { wp_lam; wp_pures.
    iApply (lnil_spec with "[//]"). iApply "HΦ". }
  wp_lam; wp_pures.
  rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l.
  wp_apply "IH"; iIntros (hd' Hl). wp_let. by iApply (lcons_spec with "[//]").
Qed.

Lemma llength_spec hd vs :
  {{{ ⌜ is_list hd vs ⌝ }}} llength hd {{{ RET #(length vs); True }}}.
Proof.
  iIntros (Φ Hl) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (hd Hl Φ); simplify_eq/=.
  { wp_lam. wp_match. by iApply "HΦ". }
  destruct Hl as (hd'&->&?). wp_lam. wp_match. wp_proj.
  wp_apply ("IH" $! hd' with "[//]"); iIntros "_ /=". wp_op.
  rewrite (Nat2Z.inj_add 1). by iApply "HΦ".
Qed.

Lemma lsnoc_spec hd vs v :
  {{{ ⌜ is_list hd vs ⌝ }}}
    lsnoc hd v
  {{{ hd', RET hd'; ⌜ is_list hd' (vs++[v]) ⌝ }}}.
Proof.
  iIntros (Φ Hvs) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (hd Hvs Φ).
  - simplify_eq/=.
    wp_rec.
    wp_pures.
    wp_lam.
    wp_pures.
    iApply "HΦ". simpl. eauto.
  - destruct Hvs as [vs' [-> Hvs']].
    wp_rec.
    wp_pures.
    wp_bind (lsnoc vs' v).
    iApply "IH".
    eauto.
    iNext.
    iIntros (hd' Hhd').
    wp_pures.
    iApply lcons_spec.
    eauto.
    iApply "HΦ".
Qed.
End lists.