From iris.bi Require Import big_op.
From iris.heap_lang Require Export primitive_laws notation proofmode.

Definition new_matrix : val :=
  λ: "m" "n" "v", (AllocN ("m"*"n") "v","m","n").

Definition pos (n i j : nat) : nat := i * n + j.
Definition vpos : val := λ: "n" "i" "j", "i"*"n" + "j".

Definition matrix_get : val :=
  λ: "m" "i" "j",
    let: "l" := Fst (Fst "m") in
    let: "n" := Snd "m" in
    "l" +ₗ vpos "n" "i" "j".

Section with_Σ.
  Context `{heapGS Σ}.

  Definition is_matrix (v : val) (m n : nat)
             (P : nat → nat → loc → iProp Σ) : iProp Σ :=
    ∃ (l:loc),
      ⌜v = PairV (PairV #l #m) #n⌝ ∗
      [∗ list] i ↦ _ ∈ replicate m (),
        [∗ list] j ↦ _ ∈ replicate n (),
          P i j (l +ₗ pos n i j).

  Lemma array_to_matrix_pre l n m v :
    l ↦∗ replicate (n * m) v -∗
    [∗ list] i ↦ _ ∈ replicate n (), (l +ₗ i*m) ↦∗ replicate m v.
  Proof.
    iIntros "Hl".
    iInduction n as [|n] "IHn"; [done|].
    replace (S n) with (n + 1) by lia.
    replace ((n + 1) * m) with (n * m + m) by lia.
    rewrite !replicate_add /= array_app=> /=.
    iDestruct "Hl" as "[Hl Hls]".
    iDestruct ("IHn" with "Hl") as "Hl".
    iFrame=> /=.
    rewrite Nat.add_0_r !replicate_length.
    replace (Z.of_nat (n * m)) with (Z.of_nat n * Z.of_nat m)%Z by lia.
    by iFrame.
  Qed.

  Lemma big_sepL_replicate_type {A B} n (x1 : A) (x2 : B) (P : nat → iProp Σ) :
    ([∗ list] i ↦ _ ∈ replicate n x1, P i) ⊢
    ([∗ list] i ↦ _ ∈ replicate n x2, P i).
  Proof.
    iIntros "H".
    iInduction n as [|n] "IHn"; [done|].
    replace (S n) with (n + 1) by lia.
    rewrite !replicate_add /=. iDestruct "H" as "[H1 H2]".
    iSplitL "H1"; [by iApply "IHn"|]=> /=.
    by rewrite !replicate_length.
  Qed.

  Lemma array_to_matrix l m n v :
    l ↦∗ replicate (m * n) v -∗
    [∗ list] i ↦ _ ∈ replicate m (),
      [∗ list] j ↦ _ ∈ replicate n (),
        (l +ₗ pos n i j) ↦ v.
  Proof.
    iIntros "Hl".
    iDestruct (array_to_matrix_pre with "Hl") as "Hl".
    iApply (big_sepL_impl with "Hl").
    iIntros "!>" (i ? _) "Hl".
    iApply big_sepL_replicate_type.
    iApply (big_sepL_impl with "Hl").
    iIntros "!>" (j ? HSome) "Hl".
    rewrite Loc.add_assoc.
    replace (Z.of_nat i * Z.of_nat n + Z.of_nat j)%Z with
      (Z.of_nat (i * n + j))%Z by lia.
    by apply lookup_replicate in HSome as [-> _].
  Qed.

  Lemma new_matrix_spec E m n v P :
    0 < m → 0 < n →
    {{{ [∗ list] i ↦ _ ∈ replicate m (), [∗ list] j ↦ _ ∈ replicate n (),
  ∀ l, l ↦ v ={E}=∗ P i j l }}}
      new_matrix #m #n v @ E
    {{{ mat, RET mat; is_matrix mat m n P }}}.
  Proof.
    iIntros (Hm Hn Φ) "HP HΦ".
    wp_lam. wp_pures.
    wp_smart_apply wp_allocN; [lia|done|].
    iIntros (l) "[Hl _]".
    wp_pures. iApply "HΦ".
    iExists _. iSplitR; [done|].
    replace (Z.to_nat (Z.of_nat m * Z.of_nat n)) with (m * n) by lia.
    iDestruct (array_to_matrix with "Hl") as "Hl".
    iCombine "HP Hl" as "HPl".
    rewrite -big_sepL_sep.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "HPl").
    iIntros "!>" (k x Hin) "H".
    rewrite -big_sepL_sep.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "H").
    iIntros "!>" (k' x' Hin') "[HP Hl]".
    by iApply "HP".
  Qed.

  Lemma matrix_sep m n l (P : _ → _ → _ → iProp Σ) i j :
    i < m → j < n →
    ([∗ list] i ↦ _ ∈ replicate m (),
        [∗ list] j ↦ _ ∈ replicate n (),
          P i j (l +ₗ pos n i j)) -∗
    (P i j (l +ₗ pos n i j) ∗
    (P i j (l +ₗ pos n i j) -∗
    ([∗ list] i ↦ _ ∈ replicate m (),
        [∗ list] j ↦ _ ∈ replicate n (),
          P i j (l +ₗ pos n i j)))).
  Proof.
    iIntros (Hm Hn) "Hm".
    iDestruct (big_sepL_impl with "Hm []") as "Hm".
    { iIntros "!>" (k x HIn).
      iApply (big_sepL_lookup_acc _ _ j ()).
      by apply lookup_replicate. }
    rewrite {1}(big_sepL_lookup_acc _ (replicate m ()) i ());
      [|by apply lookup_replicate].
    iDestruct "Hm" as "[[Hij Hi] Hm]".
    iFrame.
    iIntros "HP".
    iDestruct ("Hm" with "[$Hi $HP]") as "Hm".
    iApply (big_sepL_impl with "Hm").
    iIntros "!>" (k x Hin).
    iIntros "[Hm Hm']". iApply "Hm'". done.
  Qed.

  Lemma vpos_spec (n i j : nat) :
    {{{ True }}} vpos #n #i #j {{{ RET #(pos n i j); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam. wp_pures. rewrite /pos.
    replace (Z.of_nat i * Z.of_nat n + Z.of_nat j)%Z with
      (Z.of_nat (i * n + j)) by lia.
    by iApply "HΦ".
  Qed.

  Lemma matrix_get_spec m n i j v P :
    i < m → j < n →
    {{{ is_matrix v m n P }}}
      matrix_get v #i #j
    {{{ l, RET #l; P i j l ∗ (P i j l -∗ is_matrix v m n P) }}}.
  Proof.
    iIntros (Hm Hn Φ) "Hm HΦ".
    wp_lam.
    iDestruct "Hm" as (l ->) "Hm".
    wp_pures.
    wp_smart_apply vpos_spec; [done|].
    iIntros "_".
    wp_pures.
    iApply "HΦ".
    iModIntro.
    iDestruct (matrix_sep _ _ _ _ i j with "Hm") as "[$ Hm]"; [lia|lia|].
    iIntros "H".
    iDestruct ("Hm" with "H") as "Hm".
    iExists _. iSplit; [done|]. iFrame.
  Qed.

End with_Σ.
