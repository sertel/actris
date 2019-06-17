From iris.base_logic Require Import base_logic.
From osiris.proto Require Import involutive.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Inductive action := Send | Receive.
Instance action_inhabited : Inhabited action := populate Send.
Definition dual_action (a : action) : action :=
  match a with Send => Receive | Receive => Send end.
Instance dual_action_involutive : Involutive (=) dual_action.
Proof. by intros []. Qed.

CoInductive proto (V PROP : Type) :=
  | TEnd
  | TSR (a : action) (P : V → PROP) (prot : V → proto V PROP).
Arguments TEnd {_ _}.
Arguments TSR {_ _} _ _ _.
Instance: Params (@TSR) 3.

Instance proto_inhabited V PROP : Inhabited (proto V PROP) := populate TEnd.

CoFixpoint dual_proto {V PROP} (prot : proto V PROP) : proto V PROP :=
  match prot with
  | TEnd => TEnd
  | TSR a Φ prot => TSR (dual_action a) Φ (λ v, dual_proto (prot v))
  end.
Instance: Params (@dual_proto) 2.

Delimit Scope proto_scope with proto.
Bind Scope proto_scope with proto.

Notation "<!> x @ P , prot" :=
  (TSR Send (λ x, P%I) (λ x, prot%proto))
  (at level 200, x pattern, prot at level 200) : proto_scope.
Notation "<?> x @ P , prot" :=
  (TSR Receive (λ x, P%I) (λ x, prot%proto))
  (at level 200, x pattern, prot at level 200) : proto_scope.
Notation "<!> x , prot" := (<!> x @ True, prot%proto)%proto
  (at level 200, x pattern, prot at level 200) : proto_scope.
Notation "<?> x , prot" := (<?> x @ True, prot%proto)%proto
  (at level 200, x pattern, prot at level 200) : proto_scope.
Notation "<!> @ Φ , prot" := (TSR Send Φ prot)%proto
  (at level 200, prot at level 200) : proto_scope.
Notation "<?> @ Φ , prot" := (TSR Receive Φ prot)%proto
  (at level 200, prot at level 200) : proto_scope.

Section proto_ofe.
  Context {V : Type}.
  Context {PROP : ofeT}.

  CoInductive proto_equiv : Equiv (proto V PROP) :=
    | TEnd_equiv : TEnd ≡ TEnd
    | TSR_equiv a Φ1 Φ2 prot1 prot2 :
       pointwise_relation V (≡) Φ1 Φ2 →
       pointwise_relation V (≡) prot1 prot2 →
       TSR a Φ1 prot1 ≡ TSR a Φ2 prot2.
  Existing Instance proto_equiv.

  CoInductive proto_dist : Dist (proto V PROP) :=
    | TEnd_dist n : TEnd ≡{n}≡ TEnd
    | TSR_dist_0 a Φ1 Φ2 prot1 prot2 :
       pointwise_relation V (dist 0) Φ1 Φ2 →
       TSR a Φ1 prot1 ≡{0}≡ TSR a Φ2 prot2
    | TSR_dist_S n a Φ1 Φ2 prot1 prot2 :
       pointwise_relation V (dist (S n)) Φ1 Φ2 →
       pointwise_relation V (dist n) prot1 prot2 →
       TSR a Φ1 prot1 ≡{S n}≡ TSR a Φ2 prot2.
  Existing Instance proto_dist.

  Lemma TSR_dist n a Φ1 Φ2 prot1 prot2 :
    pointwise_relation V (dist n) Φ1 Φ2 →
    pointwise_relation V (dist_later n) prot1 prot2 →
    TSR a Φ1 prot1 ≡{n}≡ TSR a Φ2 prot2.
  Proof. destruct n; by constructor. Defined.

  Definition proto_ofe_mixin : OfeMixin (proto V PROP).
  Proof.
    split.
    - intros prot1 prot2. split.
      + revert prot1 prot2. cofix IH; destruct 1 as [|a Φ1 Φ2 prot1' prot2' HΦ]=> n.
        { constructor. }
        destruct n as [|n].
        * constructor=> v. apply equiv_dist, HΦ.
        * constructor=> v. apply equiv_dist, HΦ. by apply IH.
      + revert prot1 prot2. cofix IH=> -[|a1 Φ1 prot1] -[|a2 Φ2 prot2] Hprot;
          feed inversion (Hprot O); subst; constructor=> v.
        * apply equiv_dist=> n. feed inversion (Hprot n); auto.
        * apply IH=> n. feed inversion (Hprot (S n)); auto.
    - intros n. split.
      + revert n. cofix IH=> -[|n] [|a Φ prot]; constructor=> v; auto.
      + revert n. cofix IH; destruct 1; constructor=> v; symmetry; auto.
      + revert n. cofix IH; destruct 1; inversion 1; constructor=> v; etrans; eauto.
    - cofix IH=> -[|n]; inversion 1; constructor=> v; try apply dist_S; auto.
  Qed.
  Canonical Structure protoC : ofeT := OfeT (proto V PROP) proto_ofe_mixin.

  Definition proto_head (dΦ : V -c> PROP) (prot : proto V PROP) : V -c> PROP :=
    match prot with TEnd => dΦ | TSR a Φ prot => Φ end.
  Definition proto_tail (v : V) (prot : protoC) : later protoC :=
    match prot with TEnd => Next TEnd | TSR a P prot => Next (prot v) end.
  Global Instance proto_head_ne d : NonExpansive (proto_head d).
  Proof. by destruct 1. Qed.
  Global Instance proto_tail_ne v : NonExpansive (proto_tail v).
  Proof. destruct 1; naive_solver. Qed.

  Definition proto_force (prot : proto V PROP) : proto V PROP :=
    match prot with
    | TEnd => TEnd
    | TSR a Φ prot => TSR a Φ prot
    end.
  Lemma proto_force_eq prot : proto_force prot = prot.
  Proof. by destruct prot. Defined.

  CoFixpoint proto_compl_go `{!Cofe PROP} (c : chain protoC) : protoC :=
    match c O with
    | TEnd => TEnd
    | TSR a Φ prot => TSR a
       (compl (chain_map (proto_head Φ) c) : V → PROP)
       (λ v, proto_compl_go (later_chain (chain_map (proto_tail v) c)))
    end.

  Global Program Instance proto_cofe `{!Cofe PROP} : Cofe protoC :=
    {| compl c := proto_compl_go c |}.
  Next Obligation.
    intros ? n c; rewrite /compl. revert c n. cofix IH=> c n.
    rewrite -(proto_force_eq (proto_compl_go c)) /=.
    destruct (c O) as [|a Φ prot'] eqn:Hc0.
    - assert (c n ≡{0}≡ TEnd) as Hcn.
      { rewrite -Hc0 -(chain_cauchy c 0 n) //. lia. }
      by inversion Hcn.
    - assert (c n ≡{0}≡ TSR a Φ prot') as Hcn.
      { rewrite -Hc0 -(chain_cauchy c 0 n) //. lia. }
      inversion Hcn as [|? P' ? prot'' ? HΦ|]; subst.
      destruct n as [|n]; constructor.
      + intros v. by rewrite (conv_compl 0 (chain_map (proto_head Φ) c) v) /= -H.
      + intros v. by rewrite (conv_compl _ (chain_map (proto_head Φ) c) v) /= -H.
      + intros v. assert (prot'' v = later_car (proto_tail v (c (S n)))) as ->.
        { by rewrite -H /=. }
        apply IH.
  Qed.

  Global Instance TSR_proto_contractive a n :
    Proper (pointwise_relation _ (dist n) ==>
            pointwise_relation _ (dist_later n) ==> dist n) (TSR a).
  Proof. destruct n; by constructor. Qed.
  Global Instance TSR_proto_ne a n :
    Proper (pointwise_relation _ (dist n) ==>
            pointwise_relation _ (dist n) ==> dist n) (TSR a).
  Proof.
    intros Φ1 Φ2 HΦ prot1 prot2 Hst. apply TSR_proto_contractive=> //.
    destruct n as [|n]=> // v /=. by apply dist_S.
  Qed.
  Global Instance TSR_proto_proper a :
    Proper (pointwise_relation _ (≡) ==>
            pointwise_relation _ (≡) ==> (≡)) (TSR a).
  Proof. by constructor. Qed.

  Global Instance dual_proto_ne : NonExpansive dual_proto.
  Proof.
    cofix IH=> n prot1 prot2 Hst.
    rewrite -(proto_force_eq (dual_proto prot1)) -(proto_force_eq (dual_proto prot2)).
    destruct Hst; constructor=> v; auto; by apply IH.
  Qed.
  Global Instance dual_proto_proper : Proper ((≡) ==> (≡)) dual_proto.
  Proof. apply (ne_proper _). Qed.

  Global Instance dual_proto_involutive : Involutive (≡) dual_proto.
  Proof.
    cofix IH=> prot. rewrite -(proto_force_eq (dual_proto (dual_proto _))).
    destruct prot as [|a P prot]; first done.
    rewrite /= involutive. constructor=> v; auto.
  Qed.

  Lemma proto_equivI {M} prot1 prot2 :
    prot1 ≡ prot2 ⊣⊢@{uPredI M}
        match prot1, prot2 with
        | TEnd, TEnd => True
        | TSR a1 Φ1 prot1, TSR a2 Φ2 prot2 =>
          ⌜ a1 = a2 ⌝ ∧ (∀ v, Φ1 v ≡ Φ2 v) ∧ ▷ (∀ v, prot1 v ≡ prot2 v)
        | _, _ => False
        end.
  Proof.
    uPred.unseal; constructor=> n x ?. split; first by destruct 1.
    destruct prot1, prot2=> //=; [constructor|].
    by intros [[= ->] [??]]; destruct n; constructor.
  Qed.

  Lemma proto_later_equiv M prot a Φ2 prot2 :
    ▷ (prot ≡ TSR a Φ2 prot2) -∗
    ◇ (∃ Φ1 prot1, prot ≡ TSR a Φ1 prot1 ∗
                 ▷ (∀ v, Φ1 v ≡ Φ2 v) ∗
                 ▷ ▷ (∀ v, prot1 v ≡ prot2 v) : uPred M).
  Proof.
    iIntros "Heq". destruct prot as [|a' Φ1 prot1].
    - iDestruct (proto_equivI with "Heq") as ">[]".
    - iDestruct (proto_equivI with "Heq") as "(>-> & HΦeq & Hsteq)".
      iExists Φ1, prot1. auto.
  Qed.

  Lemma dual_proto_flip {M} prot1 prot2 :
    dual_proto prot1 ≡ prot2 ⊣⊢@{uPredI M} prot1 ≡ dual_proto prot2.
  Proof.
    iSplit.
    - iIntros "Heq". iRewrite -"Heq". by rewrite dual_proto_involutive.
    - iIntros "Heq". iRewrite "Heq". by rewrite dual_proto_involutive.
  Qed.
End proto_ofe.

Arguments protoC : clear implicits.

CoFixpoint proto_map {V PROP PROP'} (f : PROP → PROP')
    (prot : proto V PROP) : proto V PROP' :=
  match prot with
  | TEnd => TEnd
  | TSR a Φ prot => TSR a (λ v, f (Φ v)) (λ v, proto_map f (prot v))
  end.
Lemma proto_map_ext_ne {V PROP} {PROP' : ofeT}
    (f g : PROP → PROP') (prot : proto V PROP) n :
  (∀ x, f x ≡{n}≡ g x) → proto_map f prot ≡{n}≡ proto_map g prot.
Proof.
  revert n prot. cofix IH=> n prot Hf.
  rewrite -(proto_force_eq (proto_map f prot)) -(proto_force_eq (proto_map g prot)).
  destruct prot as [|a Φ prot], n as [|n]; constructor=> v //. apply IH; auto using dist_S.
Qed.
Lemma proto_map_ext {V PROP} {B : ofeT} (f g : PROP → B) (prot : proto V PROP) :
  (∀ x, f x ≡ g x) → proto_map f prot ≡ proto_map g prot.
Proof.
  intros Hf. apply equiv_dist=> n. apply proto_map_ext_ne=> v.
  apply equiv_dist, Hf.
Qed.
Instance proto_map_ne {V} {PROP PROP' : ofeT} (f : PROP → PROP') n :
  (∀ n, Proper (dist n ==> dist n) f) →
  Proper (dist n ==> dist n) (@proto_map V _ _ f).
Proof.
  intros Hf. revert n. cofix IH=> n prot1 prot2 Hst.
  rewrite -(proto_force_eq (proto_map _ prot1)) -(proto_force_eq (proto_map _ prot2)).
  destruct Hst; constructor=> v; apply Hf || apply IH; auto.
Qed.
Lemma proto_fmap_id {V} {PROP : ofeT} (prot : proto V PROP) :
  proto_map id prot ≡ prot.
Proof.
  revert prot. cofix IH=> prot. rewrite -(proto_force_eq (proto_map _ _)).
  destruct prot; constructor=> v; auto.
Qed.
Lemma proto_fmap_compose {V} {PROP PROP' PROP'' : ofeT}
    (f : PROP → PROP') (g : PROP' → PROP'') prot :
  proto_map (g ∘ f) prot ≡ proto_map g (@proto_map V _ _ f prot).
Proof.
  revert prot. cofix IH=> prot.
  rewrite -(proto_force_eq (proto_map _ _)) -(proto_force_eq (proto_map g _)).
  destruct prot; constructor=> v; auto.
Qed.

Definition protoC_map {V PROP PROP'}
    (f : PROP -n> PROP') : protoC V PROP -n> protoC V PROP' :=
  CofeMor (proto_map f : protoC V PROP → protoC V PROP').
Instance protoC_map_ne {V} PROP B : NonExpansive (@protoC_map V PROP B).
Proof. intros n f g ? prot. by apply proto_map_ext_ne. Qed.

Program Definition protoCF {V} (F : cFunctor) : cFunctor := {|
  cFunctor_car PROP _ B _ := protoC V (cFunctor_car F PROP _ B _);
  cFunctor_map PROP1 _ PROP2 _ PROP1' _ PROP2' _ fg := protoC_map (cFunctor_map F fg)
|}.
Next Obligation. done. Qed.
Next Obligation.
  intros V F PROP1 ? PROP2 ? PROP1' ? PROP2' ? n f g Hfg.
  by apply protoC_map_ne, cFunctor_ne.
Qed.
Next Obligation.
  intros V F PROP ? PROP' ? x. rewrite /= -{2}(proto_fmap_id x).
  apply proto_map_ext=>y. apply cFunctor_id.
Qed.
Next Obligation.
  intros V F PROP1 ? PROP2 ? PROP3 ? PROP1' ? PROP2' ? PROP3' ? f g f' g' x.
  rewrite /= -proto_fmap_compose.
  apply proto_map_ext=>y; apply cFunctor_compose.
Qed.

Instance protoCF_contractive {V} F :
  cFunctorContractive F → cFunctorContractive (@protoCF V F).
Proof.
  intros ? PROP1 ? PROP2 ? PROP1' ? PROP2' ? n f g Hfg.
  by apply protoC_map_ne, cFunctor_contractive.
Qed.

Class IsDualAction (a1 a2 : action) :=
  is_dual_action : dual_action a1 = a2.
Instance is_dual_action_default : IsDualAction a (dual_action a) | 100.
Proof. done. Qed.
Instance is_dual_action_Send : IsDualAction Send Receive.
Proof. done. Qed.
Instance is_dual_action_Receive : IsDualAction Receive Send.
Proof. done. Qed.

Section DualProto.
  Context {V : Type} {PROP : ofeT}.

  Class IsDualProto (prot1 prot2 : proto V PROP) :=
  is_dual_proto : dual_proto prot1 ≡ prot2.

  Global Instance is_dual_default (prot : proto V PROP) :
    IsDualProto prot (dual_proto prot) | 100.
  Proof. by rewrite /IsDualProto. Qed.

  Global Instance is_dual_end : IsDualProto (TEnd : proto V PROP) TEnd.
  Proof. by rewrite /IsDualProto -(proto_force_eq (dual_proto _)). Qed.

  Global Instance is_dual_tsr a1 a2 Φ (prot1 prot2 : V → proto V PROP) :
    IsDualAction a1 a2 →
    (∀ x, IsDualProto (prot1 x) (prot2 x)) →
    IsDualProto (TSR a1 Φ prot1) (TSR a2 Φ prot2).
  Proof.
    rewrite /IsDualAction /IsDualProto. intros <- Hst.
    rewrite /IsDualProto -(proto_force_eq (dual_proto _)) /=.
    by constructor=> v.
  Qed.
End DualProto.
