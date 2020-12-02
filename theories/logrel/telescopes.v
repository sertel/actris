(** This file defines kinded telescopes, which are used for representing binders
in session types. *)
From stdpp Require Import base tactics.
From iris.proofmode Require Import tactics.
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

Definition ktforall {Σ} {kt : ktele Σ} (Ψ : ltys Σ kt -> iProp Σ) : iProp Σ :=
  ktele_fold
    (λ (k : kind) (b : lty Σ k → iProp Σ), ∀ x : lty Σ k, b x)%I
    (λ x, x) (ktele_bind Ψ).
Arguments ktforall {_ !_} _ /.
Notation "'∀k..' x .. y , P" := (ktforall (λ x, .. (ktforall (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
   format "∀k..  x  ..  y ,  P").

Definition ktexist {Σ} {kt : ktele Σ} (Ψ : ltys Σ kt -> iProp Σ) : iProp Σ :=
  ktele_fold (λ (k : kind) (b : lty Σ k → iProp Σ), ∃ x : lty Σ k, b x)%I (λ x, x) (ktele_bind Ψ).
Arguments ktexist {_ !_} _ /.
Notation "'∃k..' x .. y , P" := (ktexist (λ x, .. (ktexist (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
   format "∃k..  x  ..  y ,  P").

Lemma ktforall_forall {Σ} {kt : ktele Σ} (Ψ : ltys Σ kt → iProp Σ) :
  ⊢ ktforall Ψ ∗-∗ (∀ x, Ψ x).
Proof.
  rewrite /ktforall. iInduction kt as [|X ft] "IH".
  - simpl. iSplit.
    + iIntros "H" (x). by rewrite (ltys_O_inv x).
    + by iIntros "H".
  - simpl. iSplit; iIntros "Hx" (x).
    + destruct (ltys_S_inv x) as [y [pf ->]].
      iRevert (pf). iApply "IH". eauto.
    + iApply "IH". eauto.
Qed.
Lemma ktexist_exist {Σ} {kt : ktele Σ} (Ψ : ltys Σ kt → iProp Σ) :
  ⊢ ktexist Ψ ∗-∗ (∃ x, Ψ x).
Proof.
  rewrite /ktexist. iInduction kt as [|X ft] "IH".
  - simpl. iSplit.
    + eauto.
    + iDestruct 1 as (x) "H". by rewrite (ltys_O_inv x).
  - simpl. iSplit; iDestruct 1 as (x) "Hx".
    + iDestruct ("IH" with "Hx") as (y) "Hx". eauto.
    + destruct (ltys_S_inv x) as [y [pf ->]].
      iExists y. iApply "IH". eauto.
Qed.

(* Teach typeclass resolution how to make progress on these binders *)
Typeclasses Opaque ktforall ktexist.
Hint Extern 1 (ktforall _) =>
  progress cbn [ktforall ktele_fold ktele_bind ktele_app] : typeclass_instances.
Hint Extern 1 (ktexist _) =>
  progress cbn [ktexist ktele_fold ktele_bind ktele_app] : typeclass_instances.
