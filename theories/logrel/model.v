From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import proto proofmode.

Record lty_raw Σ := Lty {
  lty_car :> val → iProp Σ;
}.
Arguments Lty {_} _%I.
Arguments lty_car {_} _ _ : simpl never.

(* The COFE structure on semantic types *)
Section lty_ofe.
  Context `{Σ : gFunctors}.

  (* Equality of semantic types is extensional equality *)
  Instance lty_equiv : Equiv (lty_raw Σ) := λ A B, ∀ w, A w ≡ B w.
  Instance lty_dist : Dist (lty_raw Σ) := λ n A B, ∀ w, A w ≡{n}≡ B w.

  (* OFE and COFE structure is taken from isomorphism with val -d> iProp Σ *)
  Lemma lty_ofe_mixin : OfeMixin (lty_raw Σ).
  Proof. by apply (iso_ofe_mixin (lty_car : _ → val -d> _)). Qed.
  Canonical Structure lty_rawO := OfeT (lty_raw Σ) lty_ofe_mixin.

  Global Instance lty_cofe : Cofe lty_rawO.
  Proof. by apply (iso_cofe (@Lty _ : (val -d> _) → lty_rawO) lty_car). Qed.

  Global Instance lty_inhabited : Inhabited (lty_raw Σ) := populate (Lty inhabitant).

  Global Instance lty_car_ne n : Proper (dist n ==> (=) ==> dist n) lty_car.
  Proof. by intros A A' ? w ? <-. Qed.
  Global Instance lty_car_proper : Proper ((≡) ==> (=) ==> (≡)) lty_car.
  Proof. by intros A A' ? w ? <-. Qed.

  Global Instance lty_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) Lty.
  Proof. by intros ???. Qed.
  Global Instance lty_proper : Proper (pointwise_relation _ (≡) ==> (≡)) Lty.
  Proof. by intros ???. Qed.
End lty_ofe.

Arguments lty_rawO : clear implicits.

Record lsty_raw Σ := Lsty {
  lsty_car :> iProto Σ;
}.
Arguments Lsty {_} _%proto.
Arguments lsty_car {_} _ : simpl never.

Section lsty_ofe.
  Context `{Σ : gFunctors}.

  Instance lsty_equiv : Equiv (lsty_raw Σ) :=
    λ P Q, lsty_car P ≡ lsty_car Q.
  Instance lsty_dist : Dist (lsty_raw Σ) :=
    λ n P Q, lsty_car P ≡{n}≡ lsty_car Q.

  Lemma lsty_ofe_mixin : OfeMixin (lsty_raw Σ).
  Proof. by apply (iso_ofe_mixin (lsty_car : _ → iProto _)). Qed.
  Canonical Structure lsty_rawO := OfeT (lsty_raw Σ) lsty_ofe_mixin.

  Global Instance lsty_cofe : Cofe lsty_rawO.
  Proof. by apply (iso_cofe (@Lsty _ : _ → lsty_rawO) lsty_car). Qed.

  Global Instance lsty_inhabited : Inhabited (lsty_raw Σ) :=
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

Arguments lsty_rawO : clear implicits.

Inductive kind :=
  | ty_kind | sty_kind.

Definition kind_interp (k : kind) Σ : Type :=
  match k with
  | ty_kind => lty_raw Σ
  | sty_kind => lsty_raw Σ
  end.

Notation lty Σ := (kind_interp ty_kind Σ).
Notation lsty Σ := (kind_interp sty_kind Σ).
Bind Scope kind_scope with kind_interp.
Delimit Scope kind_scope with kind.

(* The COFE structure on semantic types *)
Section lty_ofe.
  Context `{Σ : gFunctors}.

  Instance kind_interp_equiv k : Equiv (kind_interp k Σ) :=
    match k with
    | ty_kind => λ A B, ∀ w, A w ≡ B w
    | lty_kind => λ S T, lsty_car S ≡ lsty_car T
    end.
  Instance kind_interp_dist k : Dist (kind_interp k Σ) :=
    match k with
    | ty_kind =>  λ n A B, ∀ w, A w ≡{n}≡ B w
    | lty_kind => λ n S T, lsty_car S ≡{n}≡ lsty_car T
    end.

  Lemma kind_interp_mixin k : OfeMixin (kind_interp k Σ).
  Proof.
    destruct k.
    - by apply (iso_ofe_mixin (lty_car : _ → val -d> _)).
    - by apply (iso_ofe_mixin (lsty_car : _ → iProto _)).
  Qed.
  Canonical Structure kind_interpO k :=
    OfeT (kind_interp k Σ) (kind_interp_mixin k).

  Global Instance kind_interp_cofe k : Cofe (kind_interpO k).
  Proof.
    destruct k.
    - by apply (iso_cofe (@Lty _ : (val -d> _) → (kind_interpO ty_kind)) lty_car).
    - by apply (iso_cofe (@Lsty _ : _ → (kind_interpO sty_kind)) lsty_car).
  Qed.

  Global Instance kind_interp_inhabited k : Inhabited (kind_interp k Σ).
  Proof.
    destruct k.
    - apply (populate (Lty inhabitant)).
    - apply (populate (Lsty inhabitant)).
  Qed.

End lty_ofe.

Arguments kind_interpO : clear implicits.

Notation ltyO Σ := (kind_interpO Σ ty_kind).
Notation lstyO Σ := (kind_interpO Σ sty_kind).

(* Typing for operators *)
Class LTyUnboxed {Σ} (A : lty Σ) :=
  lty_unboxed v : A v -∗ ⌜ val_is_unboxed v ⌝.

Class LTyUnOp {Σ} (op : un_op) (A B : lty Σ) :=
  lty_un_op v : A v -∗ ∃ w, ⌜ un_op_eval op v = Some w ⌝ ∗ B w.

Class LTyBinOp {Σ} (op : bin_op) (A1 A2 B : lty Σ) :=
  lty_bin_op v1 v2 : A1 v1 -∗ A2 v2 -∗ ∃ w, ⌜ bin_op_eval op v1 v2 = Some w ⌝ ∗ B w.
