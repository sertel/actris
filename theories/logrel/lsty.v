From actris.logrel Require Export ltyping.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import proto proofmode.

Record lsty Σ := Lsty {
  lsty_car :> iProto Σ;
}.
Arguments Lsty {_} _%proto.
Arguments lsty_car {_} _ : simpl never.
Bind Scope lsty_scope with lsty.
Delimit Scope lsty_scope with lsty.

Section lsty_ofe.
  Context `{Σ : gFunctors}.

  Instance lsty_equiv : Equiv (lsty Σ) :=
    λ P Q, lsty_car P ≡ lsty_car Q.
  Instance lsty_dist : Dist (lsty Σ) :=
    λ n P Q, lsty_car P ≡{n}≡ lsty_car Q.

  Lemma lsty_ofe_mixin : OfeMixin (lsty Σ).
  Proof. by apply (iso_ofe_mixin (lsty_car : _ → iProto _)). Qed.
  Canonical Structure lstyO := OfeT (lsty Σ) lsty_ofe_mixin.

  Global Instance lsty_cofe : Cofe lstyO.
  Proof. by apply (iso_cofe (@Lsty _ : _ → lstyO) lsty_car). Qed.

  Global Instance lsty_inhabited : Inhabited (lsty Σ) :=
    populate (Lsty inhabitant).

  Global Instance lsty_car_ne : NonExpansive lsty_car.
  Proof. intros n A A' H. exact H. Qed.

  Global Instance lsty_car_proper : Proper ((≡) ==> (≡)) lsty_car.
  Proof. intros A A' H. exact H. Qed.

  Global Instance Lsty_ne : NonExpansive Lsty.
  Proof. solve_proper. Qed.

  Global Instance Lsty_proper : Proper ((≡) ==> (≡)) Lsty.
  Proof. solve_proper. Qed.
End lsty_ofe.

Arguments lstyO : clear implicits.
