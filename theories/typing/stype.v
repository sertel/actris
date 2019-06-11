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

CoInductive stype (V A : Type) :=
  | TEnd
  | TSR (a : action) (P : V → A) (st : V → stype V A).
Arguments TEnd {_ _}.
Arguments TSR {_ _} _ _ _.
Instance: Params (@TSR) 3.

Instance stype_inhabited V A : Inhabited (stype V A) := populate TEnd.

CoFixpoint dual_stype {V A} (st : stype V A) : stype V A :=
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

  CoInductive stype_equiv : Equiv (stype V A) :=
    | TEnd_equiv : TEnd ≡ TEnd
    | TSR_equiv a P1 P2 st1 st2 :
       pointwise_relation V (≡) P1 P2 →
       pointwise_relation V (≡) st1 st2 →
       TSR a P1 st1 ≡ TSR a P2 st2.
  Existing Instance stype_equiv.

  CoInductive stype_dist : Dist (stype V A) :=
    | TEnd_dist n : TEnd ≡{n}≡ TEnd
    | TSR_dist_0 a P1 P2 st1 st2 :
       pointwise_relation V (dist 0) P1 P2 →
       TSR a P1 st1 ≡{0}≡ TSR a P2 st2
    | TSR_dist_S n a P1 P2 st1 st2 :
       pointwise_relation V (dist (S n)) P1 P2 →
       pointwise_relation V (dist n) st1 st2 →
       TSR a P1 st1 ≡{S n}≡ TSR a P2 st2.
  Existing Instance stype_dist.

  Lemma TSR_dist n a P1 P2 st1 st2 :
    pointwise_relation V (dist n) P1 P2 →
    pointwise_relation V (dist_later n) st1 st2 →
    TSR a P1 st1 ≡{n}≡ TSR a P2 st2.
  Proof. destruct n; by constructor. Defined.

  Definition stype_ofe_mixin : OfeMixin (stype V A).
  Proof.
    split.
    - intros st1 st2. split.
      + revert st1 st2. cofix IH; destruct 1 as [|a P1 P2 st1' st2' HP]=> n.
        { constructor. }
        destruct n as [|n].
        * constructor=> v. apply equiv_dist, HP.
        * constructor=> v. apply equiv_dist, HP. by apply IH.
      + revert st1 st2. cofix IH=> -[|a1 P1 st1] -[|a2 P2 st2] Hst;
          feed inversion (Hst O); subst; constructor=> v.
        * apply equiv_dist=> n. feed inversion (Hst n); auto.
        * apply IH=> n. feed inversion (Hst (S n)); auto.
    - intros n. split.
      + revert n. cofix IH=> -[|n] [|a P st]; constructor=> v; auto.
      + revert n. cofix IH; destruct 1; constructor=> v; symmetry; auto.
      + revert n. cofix IH; destruct 1; inversion 1; constructor=> v; etrans; eauto.
    - cofix IH=> -[|n]; inversion 1; constructor=> v; try apply dist_S; auto.
  Qed.
  Canonical Structure stypeC : ofeT := OfeT (stype V A) stype_ofe_mixin.

  Definition stype_head (d : V -c> A) (st : stype V A) : V -c> A :=
    match st with TEnd => d | TSR a P st => P end.
  Definition stype_tail (v : V) (st : stypeC) : later stypeC :=
    match st with TEnd => Next TEnd | TSR a P st => Next (st v) end.
  Global Instance stype_head_ne d : NonExpansive (stype_head d).
  Proof. by destruct 1. Qed.
  Global Instance stype_tail_ne v : NonExpansive (stype_tail v).
  Proof. destruct 1; naive_solver. Qed.

  Definition stype_force (st : stype V A) : stype V A :=
    match st with
    | TEnd => TEnd
    | TSR a P st => TSR a P st
    end.
  Lemma stype_force_eq st : stype_force st = st.
  Proof. by destruct st. Defined.

  CoFixpoint stype_compl_go `{!Cofe A} (c : chain stypeC) : stypeC :=
    match c O with
    | TEnd => TEnd
    | TSR a P st => TSR a
       (compl (chain_map (stype_head P) c) : V → A)
       (λ v, stype_compl_go (later_chain (chain_map (stype_tail v) c)))
    end.

  Global Program Instance stype_cofe `{!Cofe A} : Cofe stypeC :=
    {| compl c := stype_compl_go c |}.
  Next Obligation.
    intros ? n c; rewrite /compl. revert c n. cofix IH=> c n.
    rewrite -(stype_force_eq (stype_compl_go c)) /=.
    destruct (c O) as [|a P st'] eqn:Hc0.
    - assert (c n ≡{0}≡ TEnd) as Hcn.
      { rewrite -Hc0 -(chain_cauchy c 0 n) //. lia. }
      by inversion Hcn.
    - assert (c n ≡{0}≡ TSR a P st') as Hcn.
      { rewrite -Hc0 -(chain_cauchy c 0 n) //. lia. }
      inversion Hcn as [|? P' ? st'' ? HP|]; subst.
      destruct n as [|n]; constructor.
      + intros v. by rewrite (conv_compl 0 (chain_map (stype_head P) c) v) /= -H.
      + intros v. by rewrite (conv_compl _ (chain_map (stype_head P) c) v) /= -H.
      + intros v. assert (st'' v = later_car (stype_tail v (c (S n)))) as ->.
        { by rewrite -H /=. }
        apply IH.
  Qed.

  Global Instance TSR_stype_contractive a n :
    Proper (pointwise_relation _ (dist n) ==>
            pointwise_relation _ (dist_later n) ==> dist n) (TSR a).
  Proof. destruct n; by constructor. Qed.
  Global Instance TSR_stype_ne a n :
    Proper (pointwise_relation _ (dist n) ==>
            pointwise_relation _ (dist n) ==> dist n) (TSR a).
  Proof.
    intros P1 P2 HP st1 st2 Hst. apply TSR_stype_contractive=> //.
    destruct n as [|n]=> // v /=. by apply dist_S.
  Qed.
  Global Instance TSR_stype_proper a :
    Proper (pointwise_relation _ (≡) ==>
            pointwise_relation _ (≡) ==> (≡)) (TSR a).
  Proof. by constructor. Qed.

  Global Instance dual_stype_ne : NonExpansive dual_stype.
  Proof.
    cofix IH=> n st1 st2 Hst.
    rewrite -(stype_force_eq (dual_stype st1)) -(stype_force_eq (dual_stype st2)).
    destruct Hst; constructor=> v; auto; by apply IH.
  Qed.
  Global Instance dual_stype_proper : Proper ((≡) ==> (≡)) dual_stype.
  Proof. apply (ne_proper _). Qed.

  Global Instance dual_stype_involutive : Involutive (≡) dual_stype.
  Proof.
    cofix IH=> st. rewrite -(stype_force_eq (dual_stype (dual_stype _))).
    destruct st as [|a P st]; first done.
    rewrite /= involutive. constructor=> v; auto.
  Qed.

  Lemma stype_equivI {M} st1 st2 :
    st1 ≡ st2 ⊣⊢@{uPredI M}
        match st1, st2 with
        | TEnd, TEnd => True
        | TSR a1 P1 st1, TSR a2 P2 st2 =>
          ⌜ a1 = a2 ⌝ ∧ (∀ v, P1 v ≡ P2 v) ∧ ▷ (∀ v, st1 v ≡ st2 v)
        | _, _ => False
        end.
  Proof.
    uPred.unseal; constructor=> n x ?. split; first by destruct 1.
    destruct st1, st2=> //=; [constructor|].
    by intros [[= ->] [??]]; destruct n; constructor.
  Qed.

  Lemma stype_later_equiv M st a P2 st2 :
    ▷ (st ≡ TSR a P2 st2) -∗
    ◇ (∃ P1 st1, st ≡ TSR a P1 st1 ∗
                 ▷ (∀ v, P1 v ≡ P2 v) ∗
                 ▷ ▷ (∀ v, st1 v ≡ st2 v) : uPred M).
  Proof.
    iIntros "Heq". destruct st as [|a' P1 st1].
    - iDestruct (stype_equivI with "Heq") as ">[]".
    - iDestruct (stype_equivI with "Heq") as "(>-> & HPeq & Hsteq)".
      iExists P1, st1. auto.
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

CoFixpoint stype_map {V A B} (f : A → B) (st : stype V A) : stype V B :=
  match st with
  | TEnd => TEnd
  | TSR a P st => TSR a (λ v, f (P v)) (λ v, stype_map f (st v))
  end.
Lemma stype_map_ext_ne {V A} {B : ofeT} (f g : A → B) (st : stype V A) n :
  (∀ x, f x ≡{n}≡ g x) → stype_map f st ≡{n}≡ stype_map g st.
Proof.
  revert n st. cofix IH=> n st Hf.
  rewrite -(stype_force_eq (stype_map f st)) -(stype_force_eq (stype_map g st)).
  destruct st as [|a P st], n as [|n]; constructor=> v //. apply IH; auto using dist_S.
Qed.
Lemma stype_map_ext {V A} {B : ofeT} (f g : A → B) (st : stype V A) :
  (∀ x, f x ≡ g x) → stype_map f st ≡ stype_map g st.
Proof.
  intros Hf. apply equiv_dist=> n. apply stype_map_ext_ne=> v.
  apply equiv_dist, Hf.
Qed.
Instance stype_map_ne {V : Type} {A B : ofeT} (f : A → B) n :
  (∀ n, Proper (dist n ==> dist n) f) →
  Proper (dist n ==> dist n) (@stype_map V _ _ f).
Proof.
  intros Hf. revert n. cofix IH=> n st1 st2 Hst.
  rewrite -(stype_force_eq (stype_map _ st1)) -(stype_force_eq (stype_map _ st2)).
  destruct Hst; constructor=> v; apply Hf || apply IH; auto.
Qed.
Lemma stype_fmap_id {V : Type} {A : ofeT} (st : stype V A) :
  stype_map id st ≡ st.
Proof.
  revert st. cofix IH=> st. rewrite -(stype_force_eq (stype_map _ _)).
  destruct st; constructor=> v; auto.
Qed.
Lemma stype_fmap_compose {V : Type} {A B C : ofeT} (f : A → B) (g : B → C) st :
  stype_map (g ∘ f) st ≡ stype_map g (@stype_map V _ _ f st).
Proof.
  revert st. cofix IH=> st.
  rewrite -(stype_force_eq (stype_map _ _)) -(stype_force_eq (stype_map g _)).
  destruct st; constructor=> v; auto.
Qed.

Definition stypeC_map {V A B} (f : A -n> B) : stypeC V A -n> stypeC V B :=
  CofeMor (stype_map f : stypeC V A → stypeC V B).
Instance stypeC_map_ne {V} A B : NonExpansive (@stypeC_map V A B).
Proof. intros n f g ? st. by apply stype_map_ext_ne. Qed.

Program Definition stypeCF {V} (F : cFunctor) : cFunctor := {|
  cFunctor_car A _ B _ := stypeC V (cFunctor_car F A _ B _);
  cFunctor_map A1 _ A2 _ B1 _ B2 _ fg := stypeC_map (cFunctor_map F fg)
|}.
Next Obligation. done. Qed.
Next Obligation.
  by intros V F A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply stypeC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros V F A ? B ? x. rewrite /= -{2}(stype_fmap_id x).
  apply stype_map_ext=>y. apply cFunctor_id.
Qed.
Next Obligation.
  intros V F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x.
  rewrite /= -stype_fmap_compose.
  apply stype_map_ext=>y; apply cFunctor_compose.
Qed.

Instance stypeCF_contractive {V} F :
  cFunctorContractive F → cFunctorContractive (@stypeCF V F).
Proof.
  by intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg;
  apply stypeC_map_ne, cFunctor_contractive.
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
  Proof. by rewrite /IsDualStype -(stype_force_eq (dual_stype _)). Qed.

  Global Instance is_dual_tsr a1 a2 P (st1 st2 : V → stype V A) :
    IsDualAction a1 a2 →
    (∀ x, IsDualStype (st1 x) (st2 x)) →
    IsDualStype (TSR a1 P st1) (TSR a2 P st2).
  Proof.
    rewrite /IsDualAction /IsDualStype. intros <- Hst.
    rewrite /IsDualStype -(stype_force_eq (dual_stype _)) /=.
    by constructor=> v.
  Qed.
End DualStype.
