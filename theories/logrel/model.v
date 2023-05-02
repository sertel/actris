(** This file contains the definition of what semantic term types and semantic
session types are. A semantic term type is a unary (Iris) predicate on values
[val → iProp], as is customary in a logical relation for type soundness.
A semantic session type is an Actris protocol [iProto].

There is a single kinded variant [lty Σ k], which contains either a term type or a
session type, depending on the kind [k]. The reason for having a single type
containing both term types and session types is that it allows for uniform
definitions of polymorphic binders for term types and session types, instead of
having duplicated definitions.

This file also defines a COFE structure on semantic term types and session
types, which is required in order to define recursive term types and session
types. *)
From iris.algebra Require Export ofe.
From actris.channel Require Export channel.

Inductive kind := tty_kind | sty_kind.
Global Instance kind_eq_dec : EqDecision kind.
Proof. solve_decision. Defined.
Global Instance kind_inhabited : Inhabited kind := populate tty_kind.

(** Use [Variant] to suppress generation of induction schemes *)
Variant lty Σ : kind → Type :=
  | Ltty : (val → iProp Σ) → lty Σ tty_kind
  | Lsty : iProto Σ → lty Σ sty_kind.
Arguments Ltty {_} _%I.
Arguments Lsty {_} _%proto.

Declare Scope lty_scope.
Bind Scope lty_scope with lty.
Delimit Scope lty_scope with lty.

Notation ltty Σ := (lty Σ tty_kind).
Notation lsty Σ := (lty Σ sty_kind).

Definition ltty_car {Σ} (A : ltty Σ) : val → iProp Σ :=
  match A with Ltty A => A | Lsty _ => () end.
Definition lsty_car {Σ} (p : lsty Σ) : iProto Σ :=
  match p with Ltty _ => () | Lsty p => p end.
Arguments ltty_car {_} _ _ : simpl never.
Arguments lsty_car {_} _ : simpl never.

Global Instance lty_inhabited Σ k : Inhabited (lty Σ k) := populate $
  match k with
  | tty_kind => Ltty inhabitant
  | sty_kind => Lsty inhabitant
  end.

Section lty_ofe.
  Context {Σ : gFunctors}.

  Instance lty_equiv k : Equiv (lty Σ k) :=
    match k with
    | tty_kind => λ A B, ∀ w, ltty_car A w ≡ ltty_car B w
    | sty_kind => λ S T, lsty_car S ≡ lsty_car T
    end.
  Instance lty_dist k : Dist (lty Σ k) :=
    match k with
    | tty_kind => λ n A B, ∀ w, ltty_car A w ≡{n}≡ ltty_car B w
    | sty_kind => λ n S T, lsty_car S ≡{n}≡ lsty_car T
    end.

  Lemma lty_ofe_mixin k : OfeMixin (lty Σ k).
  Proof.
    destruct k.
    - by apply (iso_ofe_mixin (ltty_car : _ → val -d> _)).
    - by apply (iso_ofe_mixin (lsty_car : _ → iProto _)).
  Qed.
  Canonical Structure ltyO k := Ofe (lty Σ k) (lty_ofe_mixin k).

  Global Instance lty_cofe k : Cofe (ltyO k).
  Proof.
    destruct k.
    - by apply (iso_cofe (Ltty : (val -d> _) → _) ltty_car).
    - by apply (iso_cofe Lsty lsty_car).
  Qed.

  Global Instance ltty_car_ne n : Proper (dist n ==> (=) ==> dist n) ltty_car.
  Proof. by intros A A' ? w ? <-. Qed.
  Global Instance ltty_car_proper : Proper ((≡) ==> (=) ==> (≡)) ltty_car.
  Proof. by intros A A' ? w ? <-. Qed.
  Global Instance lsty_car_ne : NonExpansive lsty_car.
  Proof. intros n A A' H. exact H. Qed.
  Global Instance lsty_car_proper : Proper ((≡) ==> (≡)) lsty_car.
  Proof. intros A A' H. exact H. Qed.

  Global Instance Ltty_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) Ltty.
  Proof. by intros ???. Qed.
  Global Instance Ltty_proper : Proper (pointwise_relation _ (≡) ==> (≡)) Ltty.
  Proof. by intros ???. Qed.
  Global Instance Lsty_ne : NonExpansive Lsty.
  Proof. solve_proper. Qed.
  Global Instance Lsty_proper : Proper ((≡) ==> (≡)) Lsty.
  Proof. solve_proper. Qed.
End lty_ofe.

Arguments ltyO : clear implicits.
Notation lttyO Σ := (ltyO Σ tty_kind).
Notation lstyO Σ := (ltyO Σ sty_kind).

Definition lty_rec {Σ k} (C : lty Σ k → lty Σ k) `{!Contractive C} : lty Σ k :=
  fixpoint C.
