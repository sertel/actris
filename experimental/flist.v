From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang Require Import assert.

(** Immutable ML-style functional lists *)
Fixpoint flist (vs : list val) : val :=
  match vs with
  | [] => NONEV
  | v :: vs => SOMEV (v,flist vs)
  end%V.
Arguments flist : simpl never.

Definition fnil : val := λ: <>, NONEV.
Definition fcons : val := λ: "x" "l", SOME ("x", "l").

Definition fisnil : val := λ: "l",
  match: "l" with
    SOME "p" => #false
  | NONE => #true
  end.

Definition fhead : val := λ: "l",
  match: "l" with
    SOME "p" => Fst "p"
  | NONE => assert: #false
  end.

Definition ftail : val := λ: "l",
  match: "l" with
    SOME "p" => Snd "p"
  | NONE => assert: #false
  end.

Definition flookup : val :=
  rec: "go" "n" "l" :=
    if: "n" = #0 then fhead "l" else
    let: "l" := ftail "l" in "go" ("n" - #1) "l".

Definition finsert : val :=
  rec: "go" "n" "x" "l" :=
    if: "n" = #0 then let: "l" := ftail "l" in fcons "x" "l" else
    let: "k" := ftail "l" in
    let: "k" := "go" ("n" - #1) "x" "k" in
    fcons (fhead "l") "k".

Definition freplicate : val :=
  rec: "go" "n" "x" :=
    if: "n" = #0 then fnil #() else
    let: "l" := "go" ("n" - #1) "x" in fcons "x" "l".

Definition flength : val :=
  rec: "go" "l" :=
    match: "l" with
      NONE => #0
    | SOME "p" => #1 + "go" (Snd "p")
    end.

Definition fapp : val :=
  rec: "go" "l" "k" :=
    match: "l" with
      NONE => "k"
    | SOME "p" => fcons (Fst "p") ("go" (Snd "p") "k")
    end.

Definition fsnoc : val := λ: "l" "x", fapp "l" (fcons "x" (fnil #())).

Definition ftake : val :=
  rec: "go" "l" "n" :=
    if: "n" ≤ #0 then NONEV else
    match: "l" with
      NONE => NONEV
    | SOME "l" => fcons (Fst "l") ("go" (Snd "l") ("n"-#1))
    end.

Definition fdrop : val :=
  rec: "go" "l" "n" :=
    if: "n" ≤ #0 then "l" else
    match: "l" with
      NONE => NONEV
    | SOME "l" => "go" (Snd "l") ("n"-#1)
    end.

Definition fsplit_at : val := λ: "l" "n", (ftake "l" "n", fdrop "l" "n").

Definition fsplit : val := λ: "l", fsplit_at "l" (flength "l" `quot` #2).

Section lists.
Context `{heapG Σ}.
Implicit Types i : nat.
Implicit Types v : val.
Implicit Types vs : list val.

Lemma fnil_spec :
  {{{ True }}} fnil #() {{{ RET flist []; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. by iApply "HΦ". Qed.

Lemma fcons_spec v vs :
  {{{ True }}} fcons v (flist vs) {{{ RET flist (v :: vs); True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma fisnil_spec vs:
  {{{ True }}}
    fisnil (flist vs)
  {{{ RET #(if vs is [] then true else false); True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. destruct vs; wp_pures; by iApply "HΦ". Qed.

Lemma fhead_spec v vs :
  {{{ True }}} fhead (flist (v :: vs)) {{{ RET v; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma ftail_spec v vs :
  {{{ True }}} ftail (flist (v :: vs)) {{{ RET flist vs; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma flookup_spec i vs v :
  vs !! i = Some v →
  {{{ True }}} flookup #i (flist vs) {{{ RET v; True }}}.
Proof.
  iIntros (Hi Φ _) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (i Hi);
    destruct i as [|i]=> //; simplify_eq/=.
  { wp_lam. wp_pures. by iApply (fhead_spec with "[//]"). }
  wp_lam. wp_pures.
  wp_apply (ftail_spec with "[//]"); iIntros (_). wp_let.
  wp_op. rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l. by iApply "IH".
Qed.

Lemma finsert_spec i vs v :
  is_Some (vs !! i) →
  {{{ True }}} finsert #i v (flist vs) {{{ RET flist (<[i:=v]>vs); True }}}.
Proof.
  iIntros ([w Hi] Φ _) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (i Hi Φ);
    destruct i as [|i]=> //; simplify_eq/=.
  { wp_lam. wp_pures. wp_apply (ftail_spec with "[//]"); iIntros (_).
    wp_let. by iApply (fcons_spec with "[//]"). }
  wp_lam; wp_pures.
  wp_apply (ftail_spec with "[//]"); iIntros (_). wp_let.
  wp_op. rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l.
  wp_apply ("IH" with "[//]"); iIntros (_).
  wp_apply (fhead_spec with "[//]"); iIntros "_".
  by wp_apply (fcons_spec with "[//]").
Qed.

Lemma freplicate_spec i v :
  {{{ True }}} freplicate #i v {{{ RET flist (replicate i v); True }}}.
Proof.
  iIntros (Φ _) "HΦ". iInduction i as [|i] "IH" forall (Φ); simpl.
  { wp_lam; wp_pures. iApply (fnil_spec with "[//]"); auto. }
  wp_lam; wp_pures.
  rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l.
  wp_apply "IH"; iIntros (_). wp_let. by iApply (fcons_spec with "[//]").
Qed.

Lemma flength_spec vs :
  {{{ True }}} flength (flist vs) {{{ RET #(length vs); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (Φ); simplify_eq/=.
  { wp_lam. wp_match. by iApply "HΦ". }
  wp_lam. wp_match. wp_proj.
  wp_apply "IH"; iIntros "_ /=". wp_op.
  rewrite (Nat2Z.inj_add 1). by iApply "HΦ".
Qed.

Lemma fapp_spec vs1 vs2 :
  {{{ True }}} fapp (flist vs1) (flist vs2) {{{ RET (flist (vs1 ++ vs2)); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction vs1 as [|v1 vs1] "IH" forall (Φ); simpl.
  { wp_rec. wp_pures. by iApply "HΦ". }
  wp_rec. wp_pures. wp_apply "IH". iIntros (_). by wp_apply fcons_spec.
Qed.

Lemma fsnoc_spec vs v :
  {{{ True }}} fsnoc (flist vs) v {{{ RET (flist (vs ++ [v])); True }}}.
Proof.
  iIntros (Φ _) "HΦ". wp_lam. wp_apply (fnil_spec with "[//]"); iIntros (_).
  wp_apply (fcons_spec with "[//]"); iIntros (_).
  wp_apply (fapp_spec with "[//]"); iIntros (_). by iApply "HΦ".
Qed.

Lemma ftake_spec vs (n : nat) :
  {{{ True }}} ftake (flist vs) #n {{{ RET flist (take n vs); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction vs as [|x' vs] "IH" forall (n Φ).
  - wp_rec. wp_pures.
    destruct (bool_decide (n ≤ 0)); wp_pures; rewrite take_nil; by iApply "HΦ".
  - wp_rec; destruct n as [|n]; wp_pures; first by iApply "HΦ".
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply "IH"; iIntros (_).
    wp_apply (fcons_spec with "[//]"); iIntros (_). by iApply "HΦ".
Qed.

Lemma fdrop_spec vs (n : nat) :
  {{{ True }}} fdrop (flist vs) #n {{{ RET flist (drop n vs); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction vs as [|x' vs] "IH" forall (n Φ).
  - wp_rec. wp_pures.
    destruct (bool_decide (n ≤ 0)); wp_pures; rewrite drop_nil; by iApply "HΦ".
  - wp_rec; destruct n as [|n]; wp_pures; first by iApply "HΦ".
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply "IH"; iIntros (_). by iApply "HΦ".
Qed.

Lemma fsplit_at_spec vs (n : nat) :
  {{{ True }}}
    fsplit_at (flist vs) #n
  {{{ RET (flist (take n vs), flist (drop n vs)); True }}}.
Proof.
  iIntros (Φ _) "HΦ". wp_lam.
  wp_apply (fdrop_spec with "[//]"); iIntros (_).
  wp_apply (ftake_spec with "[//]"); iIntros (_).
  wp_pures. by iApply "HΦ".
Qed.

Lemma fsplit_spec vs :
  {{{ True }}}
    fsplit (flist vs)
  {{{ ws1 ws2, RET (flist ws1, flist ws2); ⌜ vs = ws1 ++ ws2 ⌝ }}}.
Proof.
  iIntros (Φ _) "HΦ". wp_lam.
  wp_apply (flength_spec with "[//]"); iIntros (_). wp_pures.
  rewrite Z.quot_div_nonneg; [|lia..]. rewrite -(Z2Nat_inj_div _ 2).
  wp_apply (fsplit_at_spec with "[//]"); iIntros (_).
  iApply "HΦ". by rewrite take_drop.
Qed.
End lists.
