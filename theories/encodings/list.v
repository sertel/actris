From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang Require Import assert.
From osiris Require Export encodable.

(** Immutable ML-style functional lists *)
Instance pair_encodable `{Encodable A, Encodable B} : Encodable (A * B) :=
  λ p, (encode p.1, encode p.2)%V.

Instance option_encodable `{Encodable A} : Encodable (option A) := λ mx,
  match mx with Some x => SOMEV (encode x) | None => NONEV end%V.

Instance list_encodable `{Encodable A} : Encodable (list A) :=
  fix go xs :=
  let _ : Encodable _ := @go in
  match xs with
  | [] => encode None
  | x :: xs => encode (Some (x,xs))
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
Context `{EncDec T}.
Implicit Types x : T.
Implicit Types xs : list T.

Lemma lnil_spec :
  {{{ True }}} lnil #() {{{ RET encode []; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. by iApply "HΦ". Qed.

Lemma lcons_spec x xs :
  {{{ True }}} lcons (encode x) (encode xs) {{{ RET (encode (x :: xs)); True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma lhead_spec x xs:
  {{{ True }}} lhead (encode (x::xs)) {{{ RET encode x; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma ltail_spec x xs :
  {{{ True }}} ltail (encode (x::xs)) {{{ RET encode xs; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma llookup_spec i xs x:
  xs !! i = Some x →
  {{{ True }}}
    llookup #i (encode xs)
  {{{ RET encode x; True }}}.
Proof.
  iIntros (Hi Φ Hl) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (i Hi Hl);
    destruct i as [|i]=> //; simplify_eq/=.
  { wp_lam. wp_pures. by iApply (lhead_spec with "[//]"). }
  wp_lam. wp_pures.
  wp_apply (ltail_spec with "[//]"); iIntros (?). wp_let.
  wp_op. rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l. by iApply "IH".
Qed.

Lemma linsert_spec i xs x :
  is_Some (xs !! i) →
  {{{ True }}}
    linsert #i (encode x) (encode xs)
  {{{ RET encode (<[i:=x]>xs); True }}}.
Proof.
  iIntros ([w Hi] Φ Hl) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (i Hi Hl Φ);
    destruct i as [|i]=> //; simplify_eq/=.
  { wp_lam. wp_pures. wp_apply (ltail_spec with "[//]"). iIntros (?).
    wp_let. by iApply (lcons_spec with "[//]"). }
  wp_lam; wp_pures.
  wp_apply (ltail_spec with "[//]"); iIntros (?). wp_let.
  wp_op. rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l.
  wp_apply ("IH" with "[//] [//]"). iIntros (?). wp_let.
  wp_apply (lhead_spec with "[//]"); iIntros "_".
  by wp_apply (lcons_spec with "[//]").
Qed.

Lemma llist_member_spec `{EqDecision T} (xs : list T) (x : T) :
  {{{ True }}}
    llist_member (encode x) (encode xs)
  {{{ RET #(bool_decide (x ∈ xs)); True }}}.
Proof.
  iIntros (Φ Hl) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (Hl); simplify_eq/=.
  { wp_lam; wp_pures. by iApply "HΦ". }
  wp_lam; wp_pures.
  destruct (bool_decide_reflect (encode x' = encode x)) as [Heq|?]; wp_if.
  { apply enc_inj in Heq. rewrite Heq. rewrite (bool_decide_true (_ ∈ _ :: _)). by iApply "HΦ". by left. }
  wp_proj. wp_let. iApply ("IH" with "[//]").
  destruct (bool_decide_reflect (x ∈ xs)).
  - by rewrite bool_decide_true; last by right.
  - by rewrite bool_decide_false ?elem_of_cons; last naive_solver.
Qed.

Lemma lreplicate_spec i x :
  {{{ True }}}
    lreplicate #i (encode x)
  {{{ RET encode (replicate i x); True }}}.
Proof.
  iIntros (Φ _) "HΦ". iInduction i as [|i] "IH" forall (Φ); simpl.
  { wp_lam; wp_pures.
    iApply (lnil_spec with "[//]"). iApply "HΦ". }
  wp_lam; wp_pures.
  rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l.
  wp_apply "IH"; iIntros (Hl). wp_let. by iApply (lcons_spec with "[//]").
Qed.

Lemma llength_spec xs :
  {{{ True }}} llength (encode xs) {{{ RET #(length xs); True }}}.
Proof.
  iIntros (Φ Hl) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (Hl Φ); simplify_eq/=.
  { wp_lam. wp_match. by iApply "HΦ". }
wp_lam. wp_match. wp_proj.
  wp_apply ("IH" with "[//]"); iIntros "_ /=". wp_op.
  rewrite (Nat2Z.inj_add 1). by iApply "HΦ".
Qed.

Lemma lsnoc_spec xs x :
  {{{ True }}} lsnoc (encode xs) (encode x) {{{ RET (encode (xs++[x])); True }}}.
Proof.
  iIntros (Φ Hvs) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (Hvs Φ).
  { wp_rec. wp_pures. wp_lam. wp_pures. by iApply "HΦ". }
  wp_rec.
  wp_apply "IH"=> //.
  iIntros (_). by wp_apply lcons_spec=> //.
Qed.

End lists.