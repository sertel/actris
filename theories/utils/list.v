From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang Require Import assert.
From osiris.utils Require Export encodable.

(** Immutable ML-style functional lists *)
Instance list_val_enc `{ValEnc A} : ValEnc (list A) :=
  fix go xs :=
  let _ : ValEnc _ := @go in
  match xs with
  | [] => val_encode None
  | x :: xs => val_encode (Some (x,xs))
  end.

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
Context `{heapG Σ} `{ValEncDec A}.
Implicit Types i : nat.
Implicit Types x : A.
Implicit Types xs : list A.

Lemma lnil_spec :
  {{{ True }}} lnil #() {{{ RET val_encode []; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. by iApply "HΦ". Qed.

Lemma lcons_spec x xs :
  {{{ True }}}
    lcons (val_encode x) (val_encode xs)
  {{{ RET val_encode (x :: xs); True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma lisnil_spec xs:
  {{{ True }}}
    lisnil (val_encode xs)
  {{{ RET #(if xs is [] then true else false); True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. destruct xs; wp_pures; by iApply "HΦ". Qed.

Lemma lhead_spec x xs:
  {{{ True }}} lhead (val_encode (x::xs)) {{{ RET val_encode x; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma ltail_spec x xs :
  {{{ True }}} ltail (val_encode (x::xs)) {{{ RET val_encode xs; True }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_pures. by iApply "HΦ". Qed.

Lemma llookup_spec i xs x:
  xs !! i = Some x →
  {{{ True }}}
    llookup #i (val_encode xs)
  {{{ RET val_encode x; True }}}.
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
    linsert #i (val_encode x) (val_encode xs)
  {{{ RET val_encode (<[i:=x]>xs); True }}}.
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

(*
Lemma llist_member_spec `{EqDecision A} (xs : list A) (x : A) :
  {{{ True }}}
    llist_member (val_encode x) (val_encode xs)
  {{{ RET #(bool_decide (x ∈ xs)); True }}}.
Proof.
  iIntros (Φ Hl) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (Hl); simplify_eq/=.
  { wp_lam; wp_pures. by iApply "HΦ". }
  wp_lam; wp_pures.
  destruct (bool_decide_reflect (val_encode x' = val_encode x)); simplify_eq/=; wp_if.
  { rewrite (bool_decide_true (_ ∈ _ :: _)); last by left. by iApply "HΦ". }
  wp_proj. wp_let. iApply ("IH" with "[//]").
  destruct (bool_decide_reflect (x ∈ xs)).
  - by rewrite bool_decide_true; last by right.
  - by rewrite bool_decide_false ?elem_of_cons; last naive_solver.
Qed.
*)

Lemma lreplicate_spec i x :
  {{{ True }}}
    lreplicate #i (val_encode x)
  {{{ RET val_encode (replicate i x); True }}}.
Proof.
  iIntros (Φ _) "HΦ". iInduction i as [|i] "IH" forall (Φ); simpl.
  { wp_lam; wp_pures.
    iApply (lnil_spec with "[//]"). iApply "HΦ". }
  wp_lam; wp_pures.
  rewrite Nat2Z.inj_succ -Z.add_1_l Z.add_simpl_l.
  wp_apply "IH"; iIntros (Hl). wp_let. by iApply (lcons_spec with "[//]").
Qed.

Lemma llength_spec xs :
  {{{ True }}} llength (val_encode xs) {{{ RET #(length xs); True }}}.
Proof.
  iIntros (Φ Hl) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (Hl Φ); simplify_eq/=.
  { wp_lam. wp_match. by iApply "HΦ". }
  wp_lam. wp_match. wp_proj.
  wp_apply ("IH" with "[//]"); iIntros "_ /=". wp_op.
  rewrite (Nat2Z.inj_add 1). by iApply "HΦ".
Qed.

Lemma lsnoc_spec xs x :
  {{{ True }}}
    lsnoc (val_encode xs) (val_encode x)
  {{{ RET (val_encode (xs++[x])); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (Φ).
  { wp_rec. wp_pures. wp_lam. wp_pures. by iApply "HΦ". }
  wp_rec.
  wp_apply "IH"=> //.
  iIntros (_). by wp_apply lcons_spec=> //.
Qed.

Lemma ltake_spec xs (n:Z) :
  {{{ True }}}
    ltake (val_encode xs) #n
  {{{ RET val_encode (take (Z.to_nat n) xs); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (n Φ).
  - wp_rec. wp_pures. destruct (bool_decide (n ≤ 0)); wp_pures;
      rewrite take_nil; by iApply "HΦ".
  - wp_rec. wp_pures.
    destruct (decide (n ≤ 0)).
    + rewrite bool_decide_true=> //. wp_pures.
      rewrite Z_to_nat_nonpos=> //.
      rewrite firstn_O. by iApply "HΦ".
    + rewrite bool_decide_false=> //.
      wp_apply ("IH"); iIntros (_).
      wp_apply (lcons_spec)=> //; iIntros (_).
      rewrite -firstn_cons.
      rewrite -Z2Nat.inj_succ; last lia.
      rewrite Z.succ_pred.
      by iApply "HΦ".
Qed.

Lemma ldrop_spec xs (n:Z) :
  {{{ True }}}
    ldrop (val_encode xs) #n
  {{{ RET val_encode (drop (Z.to_nat n) xs); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  iInduction xs as [|x' xs] "IH" forall (n Φ).
  - wp_rec.
    wp_pures. destruct (bool_decide (n ≤ 0)); wp_pures;
      rewrite drop_nil; by iApply "HΦ".
  - wp_rec. wp_pures.
    destruct (decide (n ≤ 0)).
    + rewrite bool_decide_true=> //. wp_pures.
      rewrite Z_to_nat_nonpos=> //. rewrite drop_0.
      by iApply "HΦ".
    + rewrite bool_decide_false=> //.
      wp_apply "IH"; iIntros (_).
      rewrite -{1}(Z.succ_pred n) Z2Nat.inj_succ /= -Z.sub_1_r; last lia.
      by iApply "HΦ".
Qed.

Lemma lsplit_at_spec xs n :
  {{{ True }}}
    lsplit_at (val_encode (xs)) #n
  {{{ RET val_encode (val_encode (take (Z.to_nat n) xs),
          val_encode (drop (Z.to_nat n) xs)); True }}}.
Proof.
  iIntros (Φ _) "HΦ".
  wp_lam.
  wp_apply (ldrop_spec)=> //; iIntros (_).
  wp_apply (ltake_spec)=> //; iIntros (_).
  wp_pures.
  by iApply "HΦ".
Qed.

Lemma lsplit_spec xs :
  {{{ True }}}
    lsplit (val_encode xs)
  {{{ ys zs, RET (val_encode ys, val_encode zs); ⌜ ys++zs = xs ⌝ }}}.
Proof.
  iIntros (Φ _) "HΦ".
  wp_lam.
  wp_apply (llength_spec)=>//; iIntros (_).
  wp_apply (lsplit_at_spec)=>//; iIntros (_).
  wp_pures.
  iApply "HΦ".
  iPureIntro.
  apply take_drop.
Qed.
End lists.
