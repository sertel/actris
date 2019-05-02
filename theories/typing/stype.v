From iris.heap_lang Require Export lang.
From iris.algebra Require Export cmra.
From stdpp Require Export list.
From iris.base_logic Require Import base_logic.
From iris.algebra Require Import updates local_updates.
From iris.heap_lang Require Import proofmode notation.
From osiris.typing Require Import involutive.
Set Default Proof Using "Type".

Inductive action := Send | Receive.
Instance action_inhabited : Inhabited action := populate Send.
Definition dual_action (a : action) : action :=
  match a with Send => Receive | Receive => Send end.
Instance dual_action_involutive : Involutive (=) dual_action.
Proof. by intros []. Qed.

Inductive stype (V A : Type) :=
  | TEnd
  | TSR (a : action) (P : V → A) (st : V → stype V A).
Arguments TEnd {_ _}.
Arguments TSR {_ _} _ _ _.
Instance: Params (@TSR) 3.

Instance stype_inhabited V A : Inhabited (stype V A) := populate TEnd.

Fixpoint dual_stype {V A} (st : stype V A) :=
  match st with
  | TEnd => TEnd
  | TSR a P st => TSR (dual_action a) P (λ v, dual_stype (st v))
  end.
Instance: Params (@dual_stype) 2.

Delimit Scope stype_scope with stype.
Bind Scope stype_scope with stype.

Notation "<!> x @ P , st" :=
  (TSR Send (λ x, P%I) (λ x, st%stype))
  (at level 200, x pattern, st at level 200) : stype_scope.
Notation "<?> x @ P , st" :=
  (TSR Receive (λ x, P%I) (λ x, st%stype))
  (at level 200, x pattern, st at level 200) : stype_scope.
Notation "<!> x , st" := (<!> x @ True, st%stype)%stype
  (at level 200, x pattern, st at level 200) : stype_scope.
Notation "<?> x , st" := (<?> x @ True, st%stype)%stype
  (at level 200, x pattern, st at level 200) : stype_scope.
Notation "<!> @ P , st" := (<!> x @ P x, st x)%stype
  (at level 200, st at level 200) : stype_scope.
Notation "<?> @ P , st" := (<?> x @ P x, st x)%stype
  (at level 200, st at level 200) : stype_scope.

Section stype_ofe.
  Context {V : Type}.
  Context {A : ofeT}.

  Inductive stype_equiv : Equiv (stype V A) :=
    | TEnd_equiv : TEnd ≡ TEnd
    | TSR_equiv a P1 P2 st1 st2 :
       pointwise_relation V (≡) P1 P2 →
       pointwise_relation V (≡) st1 st2 →
       TSR a P1 st1 ≡ TSR a P2 st2.
  Existing Instance stype_equiv.

  Inductive stype_dist' (n : nat) : relation (stype V A) :=
    | TEnd_dist : stype_dist' n TEnd TEnd
    | TSR_dist a P1 P2 st1 st2 :
       pointwise_relation V (dist n) P1 P2 →
       pointwise_relation V (stype_dist' n) st1 st2 →
       stype_dist' n (TSR a P1 st1) (TSR a P2 st2).
  Instance stype_dist : Dist (stype V A) := stype_dist'.

  Definition stype_ofe_mixin : OfeMixin (stype V A).
  Proof.
    split.
    - intros st1 st2. rewrite /dist /stype_dist. split.
      + intros Hst n.
        induction Hst as [|a P1 P2 st1 st2 HP Hst IH]; constructor; intros v.
        * apply equiv_dist, HP.
        * apply IH.
      + revert st2. induction st1 as [|a P1 st1 IH]; intros [|a' P2 st2] Hst.
        * constructor.
        * feed inversion (Hst O).
        * feed inversion (Hst O).
        * feed inversion (Hst O); subst.
          constructor; intros v.
          ** apply equiv_dist=> n. feed inversion (Hst n); subst; auto.
          ** apply IH=> n. feed inversion (Hst n); subst; auto.
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
  Canonical Structure stypeC : ofeT := OfeT (stype V A) stype_ofe_mixin.

  Global Instance TSR_stype_ne a n :
    Proper (pointwise_relation _ (dist n) ==>
            pointwise_relation _ (dist n) ==> dist n) (TSR a).
  Proof.
    intros P1 P2 HP st1 st2 Hst.
    constructor.
    - apply HP.
    - intros v. apply Hst.
  Qed.
  Global Instance TSR_stype_proper a :
    Proper (pointwise_relation _ (≡) ==>
            pointwise_relation _ (≡) ==> (≡)) (TSR a).
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

Fixpoint stype_map {V A B} (f : A → B) (st : stype V A) : stype V B :=
  match st with
  | TEnd => TEnd
  | TSR a P st => TSR a (λ v, f (P v)) (λ v, stype_map f (st v))
  end.
Lemma stype_map_ext_ne {V A} {B : ofeT} (f g : A → B) (st : stype V A) n :
  (∀ x, f x ≡{n}≡ g x) → stype_map f st ≡{n}≡ stype_map g st.
Proof.
  intros Hf. induction st as [| a P st IH]; constructor.
  - intros v. apply Hf.
  - intros v. apply IH.
Qed.
Lemma stype_map_ext {V A} {B : ofeT} (f g : A → B) (st : stype V A) :
  (∀ x, f x ≡ g x) → stype_map f st ≡ stype_map g st.
Proof.
  intros Hf. apply equiv_dist.
  intros n. apply stype_map_ext_ne.
  intros x. apply equiv_dist.
  apply Hf.
Qed.
Instance stype_map_ne {V : Type} {A B : ofeT} (f : A → B) n :
  Proper (dist n ==> dist n) f →
  Proper (dist n ==> dist n) (@stype_map V _ _ f).
Proof.
  intros Hf st1 st2. induction 1 as [| a P1 P2 st1 st2 HP Hst IH]; constructor.
  - intros v. f_equiv. apply HP.
  - intros v. apply IH.
Qed.
Lemma stype_map_equiv {A B : ofeT} (f g : A -n> B) (st st' : stype val A) :
  (∀ x, f x ≡ g x) → st ≡ st' → stype_map f st ≡ stype_map g st'.
Proof. intros Feq. induction 1=>//. constructor=>//. by repeat f_equiv. Qed.
Lemma stype_fmap_id {V : Type} {A : ofeT} (st : stype V A) :
  stype_map id st ≡ st.
Proof.
  induction st as [| a P st IH]; constructor.
  - intros v. reflexivity.
  - intros v. apply IH.
Qed.
Lemma stype_fmap_compose {V : Type} {A B C : ofeT} (f : A → B) (g : B → C) st :
  stype_map (g ∘ f) st ≡ stype_map g (@stype_map V _ _ f st).
Proof.
  induction st as [| a P st IH]; constructor.
  - intros v. reflexivity.
  - intros v. apply IH.
Qed.

Definition stypeC_map {V A B} (f : A -n> B) : stypeC V A -n> stypeC V B :=
  CofeMor (stype_map f : stypeC V A → stypeC V B).
Instance stypeC_map_ne {V} A B : NonExpansive (@stypeC_map V A B).
Proof. intros n f g ? st. by apply stype_map_ext_ne. Qed.

Program Definition stypeCF {V} (F : cFunctor) : cFunctor := {|
  cFunctor_car A B := stypeC V (cFunctor_car F A B);
  cFunctor_map A1 A2 B1 B2 fg := stypeC_map (cFunctor_map F fg)
|}.
Next Obligation.
  by intros V F A1 A2 B1 B2 n f g Hfg; apply stypeC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros V F A B x. rewrite /= -{2}(stype_fmap_id x).
  apply stype_map_ext=>y. apply cFunctor_id.
Qed.
Next Obligation.
  intros V F A1 A2 A3 B1 B2 B3 f g f' g' x. rewrite /= -stype_fmap_compose.
  apply stype_map_ext=>y; apply cFunctor_compose.
Qed.

Instance stypeCF_contractive {V} F :
  cFunctorContractive F → cFunctorContractive (@stypeCF V F).
Proof.
  by intros ? A1 A2 B1 B2 n f g Hfg; apply stypeC_map_ne, cFunctor_contractive.
Qed.

Class IsDualAction (a1 a2 : action) :=
  is_dual_action : dual_action a1 = a2.
Instance is_dual_action_default : IsDualAction a (dual_action a) | 100.
Proof. done. Qed.
Instance is_dual_action_Send : IsDualAction Send Receive.
Proof. done. Qed.
Instance is_dual_action_Receive : IsDualAction Receive Send.
Proof. done. Qed.

Section DualStype.
  Context {V : Type} {A : ofeT}.

  Class IsDualStype (st1 st2 : stype V A) :=
  is_dual_stype : dual_stype st1 ≡ st2.

  Global Instance is_dual_default (st : stype V A) :
    IsDualStype st (dual_stype st) | 100.
  Proof. by rewrite /IsDualStype. Qed.

  Global Instance is_dual_end : IsDualStype (TEnd : stype V A) TEnd.
  Proof. constructor. Qed.

  Global Instance is_dual_tsr a1 a2 P (st1 st2 : V → stype V A) :
    IsDualAction a1 a2 →
    (∀ x, IsDualStype (st1 x) (st2 x)) →
    IsDualStype (TSR a1 P st1) (TSR a2 P st2).
  Proof.
    rewrite /IsDualAction /IsDualStype. intros <- Hst.
    by constructor=> x.
  Qed.

End DualStype.