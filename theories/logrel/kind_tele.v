From stdpp Require Import base tactics telescopes.
From actris.logrel Require Import model.
Set Default Proof Using "Type".

(** NB: This is overkill for the current setting, as there are no
dependencies between binders, hence we might have just used a list of [kind]
but might be needed for future extensions, such as for bounded polymorphism *)
(** Type Telescopes *)
Inductive ktele {Σ} : Type :=
  | KTeleO : ktele
  | KTeleS {k} (binder : lty Σ k → ktele) : ktele.

Arguments ktele : clear implicits.

(** The telescope version of kind types *)
Fixpoint ktele_fun {Σ} (kt : ktele Σ) (T : Type) : Type :=
  match kt with
  | KTeleO => T
  | KTeleS b => ∀ K, ktele_fun (b K) T
  end.

Notation "kt -k> A" :=
  (ktele_fun kt A) (at level 99, A at level 200, right associativity).

(** An eliminator for elements of [ktele_fun].
    We use a [fix] because, for some reason, that makes stuff print nicer
    in the proofs in iris:bi/lib/telescopes.v *)
Definition ktele_fold {Σ X Y} {kt : ktele Σ}
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

Definition ktele_app {Σ} {kt : ktele Σ} {T} (f : kt -k> T) : ltys kt → T :=
  λ Ks, (fix rec {kt} (Ks : ltys kt) : (kt -k> T) → T :=
     match Ks in ltys kt return (kt -k> T) → T with
     | LTysO => λ t : T, t
     | LTysS K Ks => λ f, rec Ks (f K)
     end) kt Ks f.
Arguments ktele_app {_} {!_ _} _ !_ /.

(* Coercion ltys : ktele >-> Sortclass. *)
(* This is a local coercion because otherwise, the "λ.." notation stops working. *)
(* Local Coercion ktele_app : ktele_fun >-> Funclass. *)

(** Inversion lemma for [tele_arg] *)
Lemma ltys_inv {Σ} {kt : ktele Σ} (Ks : ltys kt) :
  match kt as kt return ltys kt → Prop with
  | KTeleO => λ Ks, Ks = LTysO
  | KTeleS f => λ Ks, ∃ K Ks', Ks = LTysS K Ks'
  end Ks.
Proof. induction Ks; eauto. Qed.
Lemma ltys_O_inv {Σ} (Ks : ltys (@KTeleO Σ)) : Ks = LTysO.
Proof. exact (ltys_inv Ks). Qed.
Lemma ltys_S_inv {Σ} {X} {f : lty Σ X → ktele Σ} (Ks : ltys (KTeleS f)) :
  ∃ K Ks', Ks = LTysS K Ks'.
Proof. exact (ltys_inv Ks). Qed.
(*
(** Map below a tele_fun *)
Fixpoint ktele_map {Σ} {T U} {kt : ktele Σ} : (T → U) → (kt -k> T) → kt -k> U :=
  match kt as kt return (T → U) → (kt -k> T) → kt -k> U with
  | KTeleO => λ F : T → U, F
  | @KTeleS _ X b => λ (F : T → U) (f : KTeleS b -k> T) (x : lty Σ X),
                  ktele_map F (f x)
  end.
Arguments ktele_map {_} {_ _ !_} _ _ /.
Lemma ktele_map_app {Σ} {T U} {kt : ktele Σ} (F : T → U) (t : kt -k> T) (x : kt) :
  (ktele_map F t) x = F (t x).
Proof.
  induction kt as [|X f IH]; simpl in *.
  - rewrite (ltys_O_inv x). done.
  - destruct (ltys_S_inv x) as [x' [a' ->]]. simpl.
    rewrite <-IH. done.
Qed.

Global Instance ktele_fmap {Σ} {kt : ktele Σ} : FMap (ktele_fun kt) :=
  λ T U, ktele_map.

Lemma ktele_fmap_app {Σ} {T U} {kt : ktele Σ} (F : T → U) (t : kt -k> T) (x : kt) :
  (F <$> t) x = F (t x).
Proof. apply ktele_map_app. Qed.
*)
(** Operate below [tele_fun]s with argument telescope [kt]. *)
Fixpoint ktele_bind {Σ} {U} {kt : ktele Σ} : (ltys kt → U) → kt -k> U :=
  match kt as kt return (ltys kt → U) → kt -k> U with
  | KTeleO => λ F, F LTysO
  | @KTeleS _ k b => λ (F : ltys (KTeleS b) → U) (K : lty Σ k), (* b x -t> U *)
                  ktele_bind (λ Ks, F (LTysS K Ks))
  end.
Arguments ktele_bind {_} {_ !_} _ /.

(* Show that tele_app ∘ tele_bind is the identity. *)
Lemma ktele_app_bind {Σ} {U} {kt : ktele Σ} (f : ltys kt → U) K :
  ktele_app (ktele_bind f) K = f K.
Proof.
  induction kt as [|k b IH]; simpl in *.
  - rewrite (ltys_O_inv K). done.
  - destruct (ltys_S_inv K) as [K' [Ks' ->]]. simpl.
    rewrite IH. done.
Qed.

Fixpoint ktele_to_tele {Σ} (kt : ktele Σ) : tele :=
  match kt with
  | KTeleO => TeleO
  | KTeleS b => TeleS (λ x, ktele_to_tele (b x))
  end.

(*

(** We can define the identity function and composition of the [-t>] function *)
(* space. *)
Definition ktele_fun_id {Σ} {kt : ktele Σ} : kt -k> kt := ktele_bind id.

Lemma ktele_fun_id_eq {Σ} {kt : ktele Σ} (x : kt) :
  ktele_fun_id x = x.
Proof. unfold ktele_fun_id. rewrite ktele_app_bind. done. Qed.

Definition ktele_fun_compose {Σ} {kt1 kt2 kt3 : ktele Σ} :
  (kt2 -k> kt3) → (kt1 -k> kt2) → (kt1 -k> kt3) :=
  λ t1 t2, ktele_bind (compose (ktele_app t1) (ktele_app t2)).

Lemma ktele_fun_compose_eq {Σ} {kt1 kt2 kt3 : ktele Σ} (f : kt2 -k> kt3) (g : kt1 -k> kt2) x :
  ktele_fun_compose f g $ x = (f ∘ g) x.
Proof. unfold ktele_fun_compose. rewrite ktele_app_bind. done. Qed.
*)

(*
(** Notation-compatible telescope mapping *)
(* This adds (tele_app ∘ tele_bind), which is an identity function, around every *)
(*    binder so that, after simplifying, this matches the way we typically write *)
(*    notations involving telescopes. *)
Notation "'λ..' x .. y , e" :=
  (ktele_app (ktele_bind (λ x, .. (ktele_app (ktele_bind (λ y, e))) .. )))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' 'λ..'  x  ..  y ']' ,  e") : stdpp_scope.


(** Telescopic quantifiers *)
Definition ktforall {Σ} {kt : ktele Σ} (Ψ : kt → Prop) : Prop :=
  ktele_fold (λ (T : kind), λ (b : (lty Σ T) → Prop), (∀ x : (lty Σ T), b x)) (λ x, x) (ktele_bind Ψ).
Arguments ktforall {_ !_} _ /.

Notation "'∀..' x .. y , P" := (ktforall (λ x, .. (ktforall (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∀..  x  ..  y ,  P") : stdpp_scope.

Lemma ktforall_forall {Σ} {kt : ktele Σ} (Ψ : kt → Prop) :
  ktforall Ψ ↔ (∀ x, Ψ x).
Proof.
  symmetry. unfold ktforall. induction kt as [|X ft IH].
  - simpl. split.
    + done.
    + intros ? p. rewrite (ltys_O_inv p). done.
  - simpl. split; intros Hx a.
    + rewrite <-IH. done.
    + destruct (ltys_S_inv a) as [x [pf ->]].
      revert pf. setoid_rewrite IH. done.
Qed.

(* Teach typeclass resolution how to make progress on these binders *)
Typeclasses Opaque ktforall.
Hint Extern 1 (ktforall _) =>
  progress cbn [ttforall ktele_fold ktele_bind ktele_app] : typeclass_instances.
*)
