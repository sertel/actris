(** This file defines kinded telescopes, which are used for representing binders
in session types. *)
From stdpp Require Import base tactics telescopes.
From actris.logrel Require Import model.
Set Default Proof Using "Type".

(** NB: This is overkill for the current setting, as there are no
dependencies between binders, hence we might have just used a list of [kind]
but might be needed for future extensions, such as for bounded polymorphism *)
(** Type Telescopes *)
Inductive ktele {Σ} :=
  | KTeleO : ktele
  | KTeleS {k} (binder : lty Σ k → ktele) : ktele.

Arguments ktele : clear implicits.

(** The telescope version of kind types *)
Fixpoint ktele_fun {Σ} (kt : ktele Σ) (T : Type) :=
  match kt with
  | KTeleO => T
  | KTeleS b => ∀ K, ktele_fun (b K) T
  end.

Notation "kt -k> A" :=
  (ktele_fun kt A) (at level 99, A at level 200, right associativity).

(** An eliminator for elements of [ktele_fun]. *)
Definition ktele_fold {Σ X Y kt}
    (step : ∀ {k}, (lty Σ k → Y) → Y) (base : X → Y) : (kt -k> X) → Y :=
  (fix rec {kt} : (kt -k> X) → Y :=
     match kt as kt return (kt -k> X) → Y with
     | KTeleO => λ x : X, base x
     | KTeleS b => λ f, step (λ x, rec (f x))
     end) kt.
Arguments ktele_fold {_ _ _ !_} _ _ _ /.

(** A sigma-like type for an "element" of a telescope, i.e. the data it *)
(*   takes to get a [T] from a [kt -t> T]. *)
Inductive ltys {Σ} : ktele Σ → Type :=
  | LTysO : ltys KTeleO
  (* the [X] is the only relevant data here *)
  | LTysS {k} {binder} (K : lty Σ k) :
     ltys (binder K) →
     ltys (KTeleS binder).
Arguments ltys : clear implicits.

Definition ktele_app {Σ kt T} (f : kt -k> T) : ltys Σ kt → T :=
  λ Ks, (fix rec {kt} (Ks : ltys Σ kt) : (kt -k> T) → T :=
     match Ks in ltys _ kt return (kt -k> T) → T with
     | LTysO => λ t : T, t
     | LTysS K Ks => λ f, rec Ks (f K)
     end) kt Ks f.
Arguments ktele_app {_} {!_ _} _ !_ /.

(** Inversion lemma for [tele_arg] *)
Lemma ltys_inv {Σ kt} (Ks : ltys Σ kt) :
  match kt as kt return ltys _ kt → Prop with
  | KTeleO => λ Ks, Ks = LTysO
  | KTeleS f => λ Ks, ∃ K Ks', Ks = LTysS K Ks'
  end Ks.
Proof. induction Ks; eauto. Qed.
Lemma ltys_O_inv {Σ} (Ks : ltys Σ KTeleO) : Ks = LTysO.
Proof. exact (ltys_inv Ks). Qed.
Lemma ltys_S_inv {Σ X} {f : lty Σ X → ktele Σ} (Ks : ltys Σ (KTeleS f)) :
  ∃ K Ks', Ks = LTysS K Ks'.
Proof. exact (ltys_inv Ks). Qed.

(** Operate below [tele_fun]s with argument telescope [kt]. *)
Fixpoint ktele_bind {Σ U kt} : (ltys Σ kt → U) → kt -k> U :=
  match kt as kt return (ltys _ kt → U) → kt -k> U with
  | KTeleO => λ F, F LTysO
  | @KTeleS _ k b => λ (F : ltys Σ (KTeleS b) → U) (K : lty Σ k), (* b x -t> U *)
                  ktele_bind (λ Ks, F (LTysS K Ks))
  end.
Arguments ktele_bind {_} {_ !_} _ /.

(* Show that tele_app ∘ tele_bind is the identity. *)
Lemma ktele_app_bind {Σ U kt} (f : ltys Σ kt → U) K :
  ktele_app (ktele_bind f) K = f K.
Proof.
  induction kt as [|k b IH]; simpl in *.
  - rewrite (ltys_O_inv K). done.
  - destruct (ltys_S_inv K) as [K' [Ks' ->]]. simpl.
    rewrite IH. done.
Qed.
