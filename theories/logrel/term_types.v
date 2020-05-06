(** This file contains the definitions of the semantic interpretations of the
term type formers of the type system. The semantic interpretation of a type
(former) is a unary Iris predicate on values [val → iProp], which determines
when a value belongs to a certain type.

The following types are defined:

- [unit], [bool], [int]: basic types for unit, boolean and integer values,
  respectively.
- [any]: inhabited by all values.
- [A ⊸ B]: the type of affine functions from [A] to [B]. Affine functions can
  only be invoked once, since they might have captured affine resources.
- [A → B]: the type of non-affine (copyable) functions from [A] to [B]. These
  can be invoked any number of times. This is simply syntactic sugar for [copy
  (A ⊸ B)].
- [A * B], [A + B], [∀ X, A], [∃ X, A]: products, sums, universal types,
  existential types.
- [copy A]: inhabited by those values in the type [A] which are copyable. In the
  case of functions, for instance, functions (closures) which capture affine
  resources are not copyable, whereas functions that do not capture resources
  are.
- [copy- A]: acts as a kind of "inverse" to [copy A]. More precisely, we have
  that [copy- (copy A) <:> A]. This type is used to indicate the results of
  operations that might consume a resource, but do not always do so, depending
  on whether the type [A] is copyable. Such operations result in a [copy- A],
  which can be turned into an [A] using subtyping when [A] is copyable.
- [ref_uniq A]: the type of uniquely-owned mutable references to a value of type [A].
  Since the reference is guaranteed to be unique, it's possible for the type [A]
  contained in the reference to change to a different type [B] by assigning to
  the reference.
- [ref_shr A]: the type of shared mutable references to a value of type [A].
- [chan P]: the type of channels, governed by the session type [P].

In addition, some important properties, such as contractivity and
non-expansiveness of these type formers is proved. This is important in order to
use these type formers to define recursive types. *)
From iris.bi.lib Require Import core.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Export spin_lock.
From actris.logrel Require Export model kind_tele.
From actris.channel Require Export channel.

Definition lty_unit {Σ} : ltty Σ := Ltty (λ w, ⌜ w = #() ⌝%I).
Definition lty_bool {Σ} : ltty Σ := Ltty (λ w, ∃ b : bool, ⌜ w = #b ⌝)%I.
Definition lty_int {Σ} : ltty Σ := Ltty (λ w, ∃ n : Z, ⌜ w = #n ⌝)%I.
Definition lty_any {Σ} : ltty Σ := Ltty (λ w, True%I).

Definition lty_arr `{heapG Σ} (A1 A2 : ltty Σ) : ltty Σ := Ltty (λ w,
  ∀ v, ▷ ltty_car A1 v -∗ WP w v {{ ltty_car A2 }})%I.
(* TODO: Make a non-linear version of prod, using ∧ *)
Definition lty_prod {Σ} (A1 A2 : ltty Σ) : ltty Σ := Ltty (λ w,
  ∃ w1 w2, ⌜w = (w1,w2)%V⌝ ∗ ▷ ltty_car A1 w1 ∗ ▷ ltty_car A2 w2)%I.
Definition lty_sum {Σ} (A1 A2 : ltty Σ) : ltty Σ := Ltty (λ w,
  (∃ w1, ⌜w = InjLV w1⌝ ∗ ▷ ltty_car A1 w1) ∨
  (∃ w2, ⌜w = InjRV w2⌝ ∗ ▷ ltty_car A2 w2))%I.

Definition lty_forall `{heapG Σ} {k} (C : lty Σ k → ltty Σ) : ltty Σ :=
  Ltty (λ w, ∀ A, WP w #() {{ ltty_car (C A) }})%I.
Definition lty_exist {Σ k} (C : lty Σ k → ltty Σ) : ltty Σ :=
  Ltty (λ w, ∃ A, ▷ ltty_car (C A) w)%I.

Definition lty_copy {Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w, □ ltty_car A w)%I.
Definition lty_copy_minus {Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w, coreP (ltty_car A w)).

Definition lty_ref_uniq `{heapG Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w,
  ∃ (l : loc) (v : val), ⌜w = #l⌝ ∗ l ↦ v ∗ ▷ ltty_car A v)%I.
Definition ref_shrN := nroot .@ "shr_ref".
Definition lty_ref_shr `{heapG Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w,
  ∃ l : loc, ⌜w = #l⌝ ∗ inv (ref_shrN .@ l) (∃ v, l ↦ v ∗ □ ltty_car A v))%I.

Definition lty_chan `{heapG Σ, chanG Σ} (P : lsty Σ) : ltty Σ :=
  Ltty (λ w, w ↣ lsty_car P)%I.

Instance: Params (@lty_copy) 1 := {}.
Instance: Params (@lty_copy_minus) 1 := {}.
Instance: Params (@lty_arr) 2 := {}.
Instance: Params (@lty_prod) 1 := {}.
Instance: Params (@lty_sum) 1 := {}.
Instance: Params (@lty_forall) 2 := {}.
Instance: Params (@lty_sum) 1 := {}.
Instance: Params (@lty_ref_uniq) 2 := {}.
Instance: Params (@lty_ref_shr) 2 := {}.
Instance: Params (@lty_chan) 3 := {}.

Notation any := lty_any.
Notation "()" := lty_unit : lty_scope.
Notation "'copy' A" := (lty_copy A) (at level 10) : lty_scope.
Notation "'copy-' A" := (lty_copy_minus A) (at level 10) : lty_scope.

Notation "A ⊸ B" := (lty_arr A B)
  (at level 99, B at level 200, right associativity) : lty_scope.
Notation "A → B" := (lty_copy (lty_arr A B)) : lty_scope.
Infix "*" := lty_prod : lty_scope.
Infix "+" := lty_sum : lty_scope.

Notation "∀ A1 .. An , C" :=
  (lty_forall (λ A1, .. (lty_forall (λ An, C%lty)) ..)) : lty_scope.
Notation "∃ A1 .. An , C" :=
  (lty_exist (λ A1, .. (lty_exist (λ An, C%lty)) ..)) : lty_scope.

Notation "'ref_uniq' A" := (lty_ref_uniq A) (at level 10) : lty_scope.
Notation "'ref_shr' A" := (lty_ref_shr A) (at level 10) : lty_scope.

Notation "'chan' A" := (lty_chan A) (at level 10) : lty_scope.

Section term_types.
  Context {Σ : gFunctors}.
  Implicit Types A : ltty Σ.

  Global Instance lty_copy_ne : NonExpansive (@lty_copy Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_copy_minus_ne : NonExpansive (@lty_copy_minus Σ).
  Proof. solve_proper. Qed.

  Global Instance lty_arr_contractive `{heapG Σ} n :
    Proper (dist_later n ==> dist_later n ==> dist n) lty_arr.
  Proof.
    intros A A' ? B B' ?. apply Ltty_ne=> v. f_equiv=> w.
    f_equiv; [by f_contractive|].
    apply (wp_contractive _ _ _ _ _)=> v'. destruct n=> //=; by f_equiv.
  Qed.
  Global Instance lty_arr_ne `{heapG Σ} : NonExpansive2 lty_arr.
  Proof. solve_proper. Qed.
  Global Instance lty_prod_contractive n:
    Proper (dist_later n ==> dist_later n ==> dist n) (@lty_prod Σ).
  Proof. solve_contractive. Qed.
  Global Instance lty_prod_ne : NonExpansive2 (@lty_prod Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_sum_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lty_sum Σ).
  Proof. solve_contractive. Qed.
  Global Instance lty_sum_ne : NonExpansive2 (@lty_sum Σ).
  Proof. solve_proper. Qed.

  Global Instance lty_forall_contractive `{heapG Σ} k n :
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (@lty_forall Σ _ k).
  Proof.
    intros F F' A. apply Ltty_ne=> w. f_equiv=> B.
    apply (wp_contractive _ _ _ _ _)=> u. specialize (A B).
    by destruct n as [|n]; simpl.
  Qed.
  Global Instance lty_forall_ne `{heapG Σ} k n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_forall Σ _ k).
  Proof. solve_proper. Qed.
  Global Instance lty_exist_contractive k n :
    Proper (pointwise_relation _ (dist_later n) ==> dist n) (@lty_exist Σ k).
  Proof. solve_contractive. Qed.
  Global Instance lty_exist_ne k n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_exist Σ k).
  Proof. solve_proper. Qed.

  Global Instance lty_ref_uniq_contractive `{heapG Σ} : Contractive lty_ref_uniq.
  Proof. solve_contractive. Qed.
  Global Instance lty_ref_uniq_ne `{heapG Σ} : NonExpansive lty_ref_uniq.
  Proof. solve_proper. Qed.

  Global Instance lty_ref_shr_contractive `{heapG Σ} : Contractive lty_ref_shr.
  Proof. solve_contractive. Qed.
  Global Instance lty_ref_shr_ne `{heapG Σ} : NonExpansive lty_ref_shr.
  Proof. solve_proper. Qed.

  Global Instance lty_chan_ne `{heapG Σ, chanG Σ} : NonExpansive lty_chan.
  Proof. solve_proper. Qed.
End term_types.
