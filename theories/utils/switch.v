From stdpp Require Import pretty.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import metatheory proofmode notation assert.
Set Default Proof Using "Type".

Fixpoint switch_body (y : string) (i : nat) (xs : list Z)
    (edef : expr) (ecase : nat → expr) : expr :=
  match xs with
  | [] => edef
  | x :: xs => if: y = #x then ecase i
               else switch_body y (S i) xs edef ecase
  end.
Fixpoint switch_lams (y : string) (i : nat) (n : nat) (e : expr) : expr :=
  match n with
  | O => e
  | S n => λ: (y +:+ pretty i), switch_lams y (S i) n e
  end.
Definition switch_fail (xs : list Z) : val := λ: "y",
  switch_lams "f" 0 (length xs) $
    switch_body "y" 0 xs (assert: #false) $ λ i, ("f" +:+ pretty i) #().

Fixpoint map_string_seq {A}
    (s : string) (start : nat) (xs : list A) : gmap string A :=
  match xs with
  | [] => ∅
  | x :: xs => <[s+:+pretty start:=x]> (map_string_seq s (S start) xs)
  end.

Lemma lookup_map_string_seq_Some {A} (j i : nat) (xs : list A) :
  map_string_seq "f" j xs !! ("f" +:+ pretty (i + j)) = xs !! i.
Proof.
  revert i j. induction xs as [|x xs IH]=> -[|i] j //=.
  - by rewrite lookup_insert.
  - rewrite lookup_insert_ne; last (intros ?; simplify_eq/=; lia).
    by rewrite -Nat.add_succ_r IH.
Qed.

Lemma lookup_map_string_seq_None {A} y j z (vs : list A) :
  (∀ i : nat, y +:+ pretty i ≠ z) →
  map_string_seq y j vs !! z = None.
Proof.
  intros. revert j. induction vs as [|v vs IH]=> j //=.
  by rewrite lookup_insert_ne.
Qed.

Lemma lookup_map_string_seq_None_lt {A} y i j (xs : list A) :
  i < j → map_string_seq y j xs !! (y +:+ pretty i) = None.
Proof.
  revert j. induction xs as [|x xs IH]=> j ? //=.
  rewrite lookup_insert_ne; last (intros ?; simplify_eq/=; lia).
  apply IH. lia.
Qed.

Lemma switch_lams_spec `{heapGS Σ} y i n ws vs e Φ :
  length vs = n →
  WP subst_map (map_string_seq y i vs ∪ ws) e {{ Φ }} -∗
  WP subst_map ws (switch_lams y i n e) {{ w, WP fill (AppLCtx <$> vs) w {{ Φ }} }}.
Proof.
  iIntros (<-) "H".
  iInduction vs as [|v vs] "IH" forall (i ws); csimpl.
  { rewrite left_id_L.
    iApply (wp_wand with "H"); iIntros (v) "H". by iApply wp_value. }
  pose proof @pure_exec_fill.
  wp_pures. iApply wp_bind.
  iEval (rewrite -subst_map_insert insert_union_singleton_l).
  iApply "IH". rewrite assoc_L insert_union_singleton_r //
    lookup_map_string_seq_None_lt; auto with lia.
Qed.

Lemma switch_body_spec `{heapGS Σ} y xs i j ws (x : Z) edef ecase Φ :
  fst <$> list_find (x =.) xs = Some i →
  ws !! y = Some #x →
  WP subst_map ws (ecase (i + j)%nat) {{ Φ }} -∗
  WP subst_map ws (switch_body y j xs edef ecase) {{ Φ }}.
Proof.
  iIntros (Hi Hy) "H".
  iInduction xs as [|x' xs] "IH" forall (i j Hi); simplify_eq/=.
  rewrite Hy. case_decide; simplify_eq/=; wp_pures.
  { rewrite bool_decide_true; last congruence. by wp_pures. }
  move: Hi=> /fmap_Some [[??] [/fmap_Some [[i' x''] [??]] ?]]; simplify_eq/=.
  rewrite bool_decide_false; last congruence. wp_pures.
  iApply ("IH" $! i'). by simplify_option_eq. by rewrite Nat.add_succ_r.
Qed.

Lemma switch_fail_spec `{heapGS Σ} vfs xs i (x : Z) (vf : val) Φ :
  length vfs = length xs →
  fst <$> list_find (x =.) xs = Some i →
  vfs !! i = Some vf →
  ▷ WP vf #() {{ Φ }} -∗
  WP fill (AppLCtx <$> vfs) (switch_fail xs #x) {{ Φ }}.
Proof.
  iIntros (???) "H". iApply wp_bind. wp_lam.
  rewrite -subst_map_singleton. iApply switch_lams_spec; first done.
  iApply switch_body_spec; [done|..].
  - by rewrite lookup_union_r ?lookup_singleton // lookup_map_string_seq_None.
  - by rewrite /= (lookup_union_Some_l _ _ _ vf) // lookup_map_string_seq_Some.
Qed.
