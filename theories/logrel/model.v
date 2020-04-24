From iris.algebra Require Export ofe.
From actris.channel Require Export channel.

Inductive kind := tty_kind | sty_kind.
Instance kind_eq_dec : EqDecision kind.
Proof. solve_decision. Defined.
Instance kind_inhabited : Inhabited kind := populate tty_kind.

(** Use [Variant] to supress generation of induction schemes *)
Variant lty Σ : kind → Type :=
  | Ltty : (val → iProp Σ) → lty Σ tty_kind
  | Lsty : iProto Σ → lty Σ sty_kind.
Arguments Ltty {_} _%I.
Arguments Lsty {_} _%proto.

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

Instance lty_inhabited Σ k : Inhabited (lty Σ k) := populate $
  match k with
  | tty_kind => Ltty inhabitant
  | lty_kind => Lsty inhabitant
  end.

Section lty_ofe.
  Context {Σ : gFunctors}.

  Instance lty_equiv k : Equiv (lty Σ k) :=
    match k with
    | tty_kind => λ A B, ∀ w, ltty_car A w ≡ ltty_car B w
    | lty_kind => λ S T, lsty_car S ≡ lsty_car T
    end.
  Instance lty_dist k : Dist (lty Σ k) :=
    match k with
    | tty_kind => λ n A B, ∀ w, ltty_car A w ≡{n}≡ ltty_car B w
    | lty_kind => λ n S T, lsty_car S ≡{n}≡ lsty_car T
    end.

  Lemma lty_mixin k : OfeMixin (lty Σ k).
  Proof.
    destruct k.
    - by apply (iso_ofe_mixin (ltty_car : _ → val -d> _)).
    - by apply (iso_ofe_mixin (lsty_car : _ → iProto _)).
  Qed.
  Canonical Structure ltyO k := OfeT (lty Σ k) (lty_mixin k).

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
