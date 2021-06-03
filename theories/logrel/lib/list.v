From actris.utils Require Import llist.
From actris.channel Require Import proofmode.
From actris.logrel Require Import term_types.

Definition lty_list_aux `{!heapGS Σ} (A : ltty Σ) (X : ltty Σ) : ltty Σ :=
  ref_uniq (() + (A * X)).
Instance lty_list_aux_contractive `{!heapGS Σ} A :
  Contractive (@lty_list_aux Σ _ A).
Proof. solve_proto_contractive. Qed.
Definition lty_list `{!heapGS Σ} (A : ltty Σ) : ltty Σ := lty_rec (lty_list_aux A).

Notation "'list' A" := (lty_list A) (at level 10) : lty_scope.

Section with_Σ.
  Context `{!heapGS Σ}.

  Lemma list_type_loc A v :
    ltty_car (list A) v -∗ ∃ (l : loc) , ⌜v = #l⌝.
  Proof.
    iIntros "Hv". rewrite /lty_list /lty_rec fixpoint_unfold.
    iDestruct "Hv" as (l v' Heq) "Hv". by iExists l.
  Qed.

  Definition llist_type_pred (A : ltty Σ) : val → val → iProp Σ :=
    (λ v w : val, ⌜v = w⌝ ∗ ltty_car A v)%I.

  Lemma llist_lty_list lys ys A :
    llist (llist_type_pred A) lys ys -∗ ltty_car (lty_list A) #lys.
  Proof.
    iIntros "Hlys".
    iInduction ys as [|y ys] "IH" forall (lys).
    - rewrite /lty_list /lty_rec fixpoint_unfold.
      iExists lys, NONEV. rewrite /llist. iFrame "Hlys".
      iSplit; [ done | ].
      iLeft. eauto.
    - iDestruct "Hlys" as (vb l'') "[[-> HB] [Hl' Hrec]]".
      iEval (rewrite /lty_list /lty_rec fixpoint_unfold).
      iExists lys, _. iFrame "Hl'".
      iSplit; [ done | ].
      rewrite /lty_list /lty_rec.
      iRight. iExists _. iSplit; [ done | ]. iExists _, _. iSplit; [ done | ].
      iFrame "HB". by iApply ("IH" with "Hrec").
  Qed.

  Lemma llength_spec A (l : loc) :
    {{{ ltty_car (list A) #l }}} llength #l
    {{{ xs (n:Z), RET #n; ⌜Z.of_nat (length xs) = n⌝ ∗
                          llist (llist_type_pred A) l xs }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    iLöb as "IH" forall (l Φ).
    wp_lam.
    rewrite {2}/lty_list /lty_rec /lty_list_aux fixpoint_unfold.
    iDestruct "Hl" as (ltmp l' [=<-]) "[Hl [ Hl' | Hl' ]]".
    - wp_load. iDestruct "Hl'" as (xs ->) "Hl'". wp_pures.
      iAssert (llist (llist_type_pred A) l [])%I with "[Hl Hl']" as "Hl".
      { rewrite /llist. iDestruct "Hl'" as %->. iApply "Hl". }
      iApply "HΦ". eauto with iFrame.
    - wp_load. iDestruct "Hl'" as (xs ->) "Hl'". wp_pures.
      iDestruct "Hl'" as (x vl' ->) "[HA Hl']".
      wp_pures.
      rewrite fixpoint_unfold.
      iDestruct "Hl'" as (l' xs ->) "[Hl' Hl'']".
      wp_smart_apply ("IH" with "[Hl' Hl'']").
      { rewrite /lty_list /lty_rec.
        iEval (rewrite fixpoint_unfold).
        iExists _, _. iFrame "Hl' Hl''". done. }
      iIntros (ys n) "[<- H]".
      iAssert (llist (llist_type_pred A) l (x :: ys))%I with "[Hl HA H]" as "Hl".
      { iExists x, l'. eauto with iFrame. }
      wp_pures. iApply "HΦ". iFrame "Hl". by rewrite (Nat2Z.inj_add 1).
  Qed.

End with_Σ.
