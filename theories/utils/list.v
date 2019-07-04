From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang Require Import assert.

(** Immutable ML-style functional lists *)
Fixpoint llist (vs : list val) : val :=
  match vs with
  | [] => NONEV
  | v :: vs => SOMEV (v,llist vs)
  end%V.
Arguments llist : simpl never.

Definition lnil : val := λ: <>, NONEV.
Definition lcons : val := λ: "x" "l", SOME ("x", "l").

Definition lisnil : val := λ: "l",
  match: "l" with
    SOME "p" => #false
  | NONE => #true
  end.

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

Definition ltake : val :=
  rec: "go" "l" "n" :=
  if: "n" ≤ #0
  then NONEV
  else match: "l" with
         SOME "l" => lcons (Fst "l") ("go" (Snd "l") ("n"-#1))
       | NONE => NONEV
       end.

Definition ldrop : val :=
  rec: "go" "l" "n" :=
    if: "n" ≤ #0 then "l"
    else match: "l" with
         SOME "l" => "go" (Snd "l") ("n"-#1)
       | NONE => NONEV
         end.

Definition lsplit_at : val :=
  λ: "l" "n",
  (ltake "l" "n", ldrop "l" "n").

Definition lsplit : val :=
  λ: "l", lsplit_at "l" ((llength "l") `quot` #2).

Section lists.
Context `{heapG Σ}.
Implicit Types i : nat.
Implicit Types v : val.
Implicit Types vs : list val.

Lemma lnil_spec :
  {{{ True }}} lnil #() {{{ RET llist []; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. by iApply "HΦ". Qed.

Lemma lcons_spec v vs :
  {{{ True }}} lcons v (llist vs) {{{ RET llist (v :: vs); True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma lisnil_spec vs:
  {{{ True }}}
    lisnil (llist vs)
  {{{ RET #(if vs is [] then true else false); True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. destruct vs; wp_pures; by iApply "HΦ". Qed.

Lemma lhead_spec v vs :
  {{{ True }}} lhead (llist (v :: vs)) {{{ RET v; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma ltail_spec v vs :
  {{{ True }}} ltail (llist (v :: vs)) {{{ RET llist vs; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma llookup_spec i vs v :
  vs !! i = Some v →
  {{{ True }}} llookup #i (llist vs) {{{ RET v; True }}}.
Proof.
  iIntros (Hi Φ _) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (i Hi);
    destruct i as [|i]=> //; simplify_eq/=.
  { wp_lam. wp_pures. by iApply (lhead_spec with "[//]"). }
  wp_lam. wp_pures.
  wp_apply (ltail_spec with "[//]"); iIntros (_). wp_let.
  wp_op. rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l. by iApply "IH".
Qed.

Lemma linsert_spec i vs v :
  is_Some (vs !! i) →
  {{{ True }}} linsert #i v (llist vs) {{{ RET llist (<[i:=v]>vs); True }}}.
Proof.
  iIntros ([w Hi] Φ _) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (i Hi Φ);
    destruct i as [|i]=> //; simplify_eq/=.
  { wp_lam. wp_pures. wp_apply (ltail_spec with "[//]"); iIntros (_).
    wp_let. by iApply (lcons_spec with "[//]"). }
  wp_lam; wp_pures.
  wp_apply (ltail_spec with "[//]"); iIntros (_). wp_let.
  wp_op. rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l.
  wp_apply ("IH" with "[//]"); iIntros (_).
  wp_apply (lhead_spec with "[//]"); iIntros "_".
  by wp_apply (lcons_spec with "[//]").
Qed.

Lemma lreplicate_spec i v :
  {{{ True }}} lreplicate #i v {{{ RET llist (replicate i v); True }}}.
Proof.
  iIntros (Φ _) "HΦ". iInduction i as [|i] "IH" forall (Φ); simpl.
  { wp_lam; wp_pures. iApply (lnil_spec with "[//]"); auto. }
  wp_lam; wp_pures.
  rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l.
  wp_apply "IH"; iIntros (_). wp_let. by iApply (lcons_spec with "[//]").
Qed.

Lemma llength_spec vs :
  {{{ True }}} llength (llist vs) {{{ RET #(length vs); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (Φ); simplify_eq/=.
  { wp_lam. wp_match. by iApply "HΦ". }
  wp_lam. wp_match. wp_proj.
  wp_apply "IH"; iIntros "_ /=". wp_op.
  rewrite (Nat2Z.inj_add 1). by iApply "HΦ".
Qed.

Lemma lsnoc_spec vs v :
  {{{ True }}} lsnoc (llist vs) v {{{ RET (llist (vs ++ [v])); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction vs as [|v' vs] "IH" forall (Φ).
  { wp_rec. wp_pures. wp_lam. wp_pures. by iApply "HΦ". }
  wp_rec. wp_apply "IH"; iIntros (_). by wp_apply lcons_spec=> //.
Qed.

Lemma ltake_spec vs (n : nat) :
  {{{ True }}} ltake (llist vs) #n {{{ RET llist (take n vs); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction vs as [|x' vs] "IH" forall (n Φ).
  - wp_rec. wp_pures.
    destruct (bool_decide (n ≤ 0)); wp_pures; rewrite take_nil; by iApply "HΦ".
  - wp_rec; destruct n as [|n]; wp_pures; first by iApply "HΦ".
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply "IH"; iIntros (_).
    wp_apply (lcons_spec with "[//]"); iIntros (_). by iApply "HΦ".
Qed.

Lemma ldrop_spec vs (n : nat) :
  {{{ True }}} ldrop (llist vs) #n {{{ RET llist (drop n vs); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction vs as [|x' vs] "IH" forall (n Φ).
  - wp_rec. wp_pures.
    destruct (bool_decide (n ≤ 0)); wp_pures; rewrite drop_nil; by iApply "HΦ".
  - wp_rec; destruct n as [|n]; wp_pures; first by iApply "HΦ".
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply "IH"; iIntros (_). by iApply "HΦ".
Qed.

Lemma lsplit_at_spec vs (n : nat) :
  {{{ True }}}
    lsplit_at (llist vs) #n
  {{{ RET (llist (take n vs), llist (drop n vs)); True }}}.
Proof.
  iIntros (Φ _) "HΦ". wp_lam.
  wp_apply (ldrop_spec with "[//]"); iIntros (_).
  wp_apply (ltake_spec with "[//]"); iIntros (_).
  wp_pures. by iApply "HΦ".
Qed.

Lemma lsplit_spec vs :
  {{{ True }}}
    lsplit (llist vs)
  {{{ ws1 ws2, RET (llist ws1, llist ws2); ⌜ vs = ws1 ++ ws2 ⌝ }}}.
Proof.
  iIntros (Φ _) "HΦ". wp_lam.
  wp_apply (llength_spec with "[//]"); iIntros (_). wp_pures.
  rewrite Z.quot_div_nonneg; [|lia..]. rewrite -(Z2Nat_inj_div _ 2).
  wp_apply (lsplit_at_spec with "[//]"); iIntros (_).
  iApply "HΦ". by rewrite take_drop.
Qed.
End lists.
