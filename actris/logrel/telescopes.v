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
  | KTeleS {k} : (lty Σ k → ktele) → ktele.
Arguments ktele : clear implicits.

(** The telescope version of kind types *)
Fixpoint ktele_fun {Σ} (kt : ktele Σ) (A : Type) :=
  match kt with
  | KTeleO => A
  | KTeleS b => ∀ K, ktele_fun (b K) A
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

(** A sigma-like type for an "element" of a telescope, i.e., the data it *)
Inductive ltys {Σ} : ktele Σ → Type :=
  | LTysO : ltys KTeleO
  | LTysS {k b} : ∀ K : lty Σ k, ltys (b K) → ltys (KTeleS b).
Arguments ltys : clear implicits.

(** Inversion lemmas for [ltys] *)
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

Definition ktele_app {Σ kt T} (f : kt -k> T) (Ks : ltys Σ kt) : T :=
  (fix rec {kt} (Ks : ltys Σ kt) : (kt -k> T) → T :=
    match Ks in ltys _ kt return (kt -k> T) → T with
    | LTysO => λ t : T, t
    | LTysS K Ks => λ f, rec Ks (f K)
    end) kt Ks f.
Arguments ktele_app {_} {!_ _} _ !_ /.

Fixpoint ktele_bind {Σ U kt} : (ltys Σ kt → U) → kt -k> U :=
  match kt as kt return (ltys _ kt → U) → kt -k> U with
  | KTeleO => λ F, F LTysO
  | @KTeleS _ k b => λ (F : ltys Σ (KTeleS b) → U) (K : lty Σ k), (* b x -t> U *)
                  ktele_bind (λ Ks, F (LTysS K Ks))
  end.
Arguments ktele_bind {_} {_ !_} _ /.

Lemma ktele_app_bind {Σ U kt} (f : ltys Σ kt → U) K :
  ktele_app (ktele_bind f) K = f K.
Proof.
  induction kt as [|k b IH]; simpl in *.
  - by rewrite (ltys_O_inv K).
  - destruct (ltys_S_inv K) as [K' [Ks' ->]]; simpl. by rewrite IH.
Qed.
