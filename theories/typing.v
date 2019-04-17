From iris.heap_lang Require Export lang.
From iris.algebra Require Export cmra.
From stdpp Require Export list.
From iris.base_logic Require Import base_logic.
From iris.algebra Require Import updates local_updates.
From iris.heap_lang Require Import proofmode notation.
Set Default Proof Using "Type".

Class Involutive {A} (R : relation A) (f : A → A) :=
  involutive x : R (f (f x)) x.

Inductive side := Left | Right.
Instance side_inhabited : Inhabited side := populate Left.
Definition dual_side (s : side) : side :=
  match s with Left => Right | Right => Left end.
Instance dual_side_involutive : Involutive (=) dual_side.
Proof. by intros []. Qed.

Inductive action := Send | Receive.
Instance action_inhabited : Inhabited action := populate Send.
Definition dual_action (a : action) : action :=
  match a with Send => Receive | Receive => Send end.
Instance dual_action_involutive : Involutive (=) dual_action.
Proof. by intros []. Qed.

Inductive stype (A : Type) :=
  | TEnd
  | TSR (a : action) (P : val → A) (st : val → stype A).
Arguments TEnd {_}.
Arguments TSR {_} _ _ _.
Instance: Params (@TSR) 2.

Instance stype_inhabited A : Inhabited (stype A) := populate TEnd.

Fixpoint dual_stype {A} (st : stype A) :=
  match st with
  | TEnd => TEnd
  | TSR a P st => TSR (dual_action a) P (λ v, dual_stype (st v))
  end.
Instance: Params (@dual_stype) 1.

Section stype_ofe.
  Context {A : ofeT}.

  Inductive stype_equiv : Equiv (stype A) :=
    | TEnd_equiv : TEnd ≡ TEnd
    | TSR_equiv a P1 P2 st1 st2 :
       pointwise_relation val (≡) P1 P2 →
       pointwise_relation val (≡) st1 st2 →
       TSR a P1 st1 ≡ TSR a P2 st2.
  Existing Instance stype_equiv.

  Inductive stype_dist' (n : nat) : relation (stype A) :=
    | TEnd_dist : stype_dist' n TEnd TEnd
    | TSR_dist a P1 P2 st1 st2 :
       pointwise_relation val (dist n) P1 P2 →
       pointwise_relation val (stype_dist' n) st1 st2 →
       stype_dist' n (TSR a P1 st1) (TSR a P2 st2).
  Instance stype_dist : Dist (stype A) := stype_dist'.

  Definition stype_ofe_mixin : OfeMixin (stype A).
  Proof.
    split.
    - intros st1 st2. rewrite /dist /stype_dist. split.
      + intros Hst n. induction Hst as [|a P1 P2 st1 st2 HP Hst IH]; constructor.
        * intros v. apply equiv_dist, HP.
        * intros v. apply IH.
      + revert st2. induction st1 as [|a P1 st1 IH]; intros [|a' P2 st2] Hst.
        * constructor.
        * feed inversion (Hst O).
        * feed inversion (Hst O).
        * feed inversion (Hst O); subst.
          constructor.
          ** intros v. apply equiv_dist=> n. feed inversion (Hst n); subst; auto.
          ** intros v. apply IH=> n. feed inversion (Hst n); subst; auto.
    - rewrite /dist /stype_dist. split.
      + intros st. induction st; constructor; repeat intro; auto.
      + intros st1 st2. induction 1; constructor; repeat intro; auto.
        symmetry; auto.
      + intros st1 st2 st3 H1 H2.
        revert H2. revert st3.
        induction H1 as [| a P1 P2 st1 st2 HP Hst12 IH]=> //.
        inversion 1. subst. constructor.
        ** by transitivity P2.
        ** intros v. by apply IH. 
    - intros n st1 st2. induction 1; constructor.
      + intros v. apply dist_S. apply H.
      + intros v. apply H1.
  Qed.
  Canonical Structure stypeC : ofeT := OfeT (stype A) stype_ofe_mixin.

  Global Instance TSR_stype_ne a n :
    Proper (pointwise_relation _ (dist n) ==> pointwise_relation _ (dist n) ==> dist n) (TSR a).
  Proof. 
    intros P1 P2 HP st1 st2 Hst.
    constructor.
    - apply HP.
    - intros v. apply Hst.
  Qed.
  Global Instance TSR_stype_proper a :
    Proper (pointwise_relation _ (≡) ==> pointwise_relation _ (≡) ==> (≡)) (TSR a).
  Proof.
    intros P1 P2 HP st1 st2 Hst. apply equiv_dist=> n.
    by f_equiv; intros v; apply equiv_dist.
  Qed.

  Global Instance dual_stype_ne : NonExpansive dual_stype.
  Proof.
    intros n. induction 1 as [| a P1 P2 st1 st2 HP Hst IH].
    - constructor.
    - constructor. apply HP. intros v. apply IH.
  Qed.
  Global Instance dual_stype_proper : Proper ((≡) ==> (≡)) dual_stype.
  Proof. apply (ne_proper _). Qed.

  Global Instance dual_stype_involutive : Involutive (≡) dual_stype.
  Proof.
    intros st.
    induction st.
    - constructor.
    - rewrite /= (involutive (f:=dual_action)).
      constructor. reflexivity. intros v. apply H.
  Qed.
  
  Lemma stype_equivI {M} st1 st2 :
    st1 ≡ st2 ⊣⊢@{uPredI M}
        match st1, st2 with
        | TEnd, TEnd => True
        | TSR a1 P1 st1, TSR a2 P2 st2 =>
          ⌜ a1 = a2 ⌝ ∧ (∀ v, P1 v ≡ P2 v) ∧ (∀ v, st1 v ≡ st2 v)
        | _, _ => False
        end.
  Proof.
    uPred.unseal; constructor=> n x ?. split; first by destruct 1.
    destruct st1, st2=> //=; [constructor|].
    by intros [[= ->] [??]]; constructor.
  Qed.

  Lemma dual_stype_flip {M} st1 st2 :
    dual_stype st1 ≡ st2 ⊣⊢@{uPredI M} st1 ≡ dual_stype st2.
  Proof.
    iSplit.
    - iIntros "Heq". iRewrite -"Heq". by rewrite dual_stype_involutive.
    - iIntros "Heq". iRewrite "Heq". by rewrite dual_stype_involutive.
  Qed.

End stype_ofe.
Arguments stypeC : clear implicits.

Fixpoint stype_map {A B} (f : A → B) (st : stype A) : stype B :=
  match st with
  | TEnd => TEnd
  | TSR a P st => TSR a (λ v, f (P v)) (λ v, stype_map f (st v))
  end.
Lemma stype_map_ext_ne {A} {B : ofeT} (f g : A → B) (st : stype A) n :
  (∀ x, f x ≡{n}≡ g x) → stype_map f st ≡{n}≡ stype_map g st.
Proof.
  intros Hf. induction st as [| a P st IH]; constructor.
  - intros v. apply Hf.
  - intros v. apply IH.
Qed.
Lemma stype_map_ext {A} {B : ofeT} (f g : A → B) (st : stype A) :
  (∀ x, f x ≡ g x) → stype_map f st ≡ stype_map g st.
Proof.
  intros Hf. apply equiv_dist.
  intros n. apply stype_map_ext_ne.
  intros x. apply equiv_dist.
  apply Hf.
Qed.
Instance stype_map_ne {A B : ofeT} (f : A → B) n:
  Proper (dist n ==> dist n) f → Proper (dist n ==> dist n) (stype_map f).
Proof.
  intros Hf st1 st2. induction 1 as [| a P1 P2 st1 st2 HP Hst IH]; constructor.
  - intros v. f_equiv. apply HP.
  - intros v. apply IH.
Qed.
Lemma stype_fmap_id {A : ofeT} (st : stype A) : stype_map id st ≡ st.
Proof.
  induction st as [| a P st IH]; constructor.
  - intros v. reflexivity.
  - intros v. apply IH.
Qed.
Lemma stype_fmap_compose {A B C : ofeT} (f : A → B) (g : B → C) st :
  stype_map (g ∘ f) st ≡ stype_map g (stype_map f st).
Proof.
  induction st as [| a P st IH]; constructor.
  - intros v. reflexivity.
  - intros v. apply IH.
Qed.

Definition stypeC_map {A B} (f : A -n> B) : stypeC A -n> stypeC B :=
  CofeMor (stype_map f : stypeC A → stypeC B).
Instance stypeC_map_ne A B : NonExpansive (@stypeC_map A B).
Proof. intros n f g ? st. by apply stype_map_ext_ne. Qed.

Program Definition stypeCF (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := stypeC (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := stypeC_map (cFunctor_map F fg)
|}.
Next Obligation.
  by intros F A1 A2 B1 B2 n f g Hfg; apply stypeC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros F A B x. rewrite /= -{2}(stype_fmap_id x).
  apply stype_map_ext=>y. apply cFunctor_id.
Qed.
Next Obligation.
  intros F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -stype_fmap_compose.
  apply stype_map_ext=>y; apply cFunctor_compose.
Qed.

Instance stypeCF_contractive F :
  cFunctorContractive F → cFunctorContractive (stypeCF F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply stypeC_map_ne, cFunctor_contractive.
Qed.

