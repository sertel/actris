From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang Require Import assert.

Fixpoint llist `{heapGS Σ} (l : loc) (vs : list val) : iProp Σ :=
  match vs with
  | [] => l ↦ NONEV
  | v :: vs => ∃ (l' : loc), l ↦ SOMEV (v,#l') ∗ llist l' vs
  end.

Definition lnil : val := λ: <>, ref NONE.

Definition lisnil : val := λ: "l",
  match: !"l" with SOME "p" => #false | NONE => #true end.

Definition lpop : val := λ: "l",
  match: !"l" with
    SOME "p" => "l" <- !(Snd "p");; Fst "p"
  | NONE => assert: #false
  end.

Definition lsnoc : val := rec: "go" "l" "x" :=
  match: !"l" with
    NONE => "l" <- SOME ("x", ref NONE)
  | SOME "p" => "go" (Snd "p") "x"
  end.

Section lists.
  Context `{heapGS Σ}.
  Implicit Types i : nat.
  Implicit Types l : loc.

  Lemma lnil_spec :
    {{{ True }}} lnil #() {{{ l, RET #l; llist l [] }}}.
  Proof. iIntros (Φ _) "HΦ". wp_lam. wp_alloc l. by iApply "HΦ". Qed.

  Lemma lisnil_spec l vs:
    {{{ llist l vs }}}
      lisnil #l
    {{{ RET #(if vs is [] then true else false); llist l vs }}}.
  Proof.
    iIntros (Φ) "Hll HΦ". wp_lam. destruct vs as [|v vs]; simpl; wp_pures.
    - wp_load; wp_pures. by iApply "HΦ".
    - iDestruct "Hll" as (l') "(Hl & Hll)".
      wp_load; wp_pures. iApply "HΦ"; eauto with iFrame.
  Qed.

  Lemma lpop_spec l v vs :
    {{{ llist l (v :: vs) }}} lpop #l {{{ RET v; llist l vs }}}.
  Proof.
    iIntros (Φ) "/= (%l' & Hl & Hll) HΦ". wp_lam; wp_load. wp_pures.
    destruct vs as [|x' vs]; simpl; wp_pures.
    - wp_load. wp_store. wp_pures. iApply "HΦ"; eauto with iFrame.
    - iDestruct "Hll" as (l'') "[Hl' Hll]".
      wp_load. wp_store. wp_pures. iApply "HΦ"; eauto with iFrame.
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
End lists.

Opaque llist.
