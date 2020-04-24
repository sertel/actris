From iris.bi.lib Require Import core.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Export spin_lock.
From actris.logrel Require Export subtyping.
From actris.channel Require Export channel.

Definition lty_any {Σ} : ltty Σ := Ltty (λ w, True%I).

Definition lty_copy {Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w, □ ltty_car A w)%I.
Definition lty_copy_inv {Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w, coreP (ltty_car A w)).
Definition lty_copyable {Σ} (A : ltty Σ) : iProp Σ :=
  tc_opaque (A <: lty_copy A)%I.

Definition lty_unit {Σ} : ltty Σ := Ltty (λ w, ⌜ w = #() ⌝%I).
Definition lty_bool {Σ} : ltty Σ := Ltty (λ w, ∃ b : bool, ⌜ w = #b ⌝)%I.
Definition lty_int {Σ} : ltty Σ := Ltty (λ w, ∃ n : Z, ⌜ w = #n ⌝)%I.

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

Definition lty_ref_mut `{heapG Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w,
  ∃ (l : loc) (v : val), ⌜w = #l⌝ ∗ l ↦ v ∗ ▷ ltty_car A v)%I.
Definition ref_shrN := nroot .@ "shr_ref".
Definition lty_ref_shr `{heapG Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w,
  ∃ l : loc, ⌜w = #l⌝ ∗ inv (ref_shrN .@ l) (∃ v, l ↦ v ∗ ltty_car A v))%I.

Definition lty_mutex `{heapG Σ, lockG Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w,
  ∃ (γ : gname) (l : loc) (lk : val),
    ⌜ w = PairV lk #l ⌝ ∗
    is_lock γ lk (∃ v_inner, l ↦ v_inner ∗ ltty_car A v_inner))%I.
Definition lty_mutexguard `{heapG Σ, lockG Σ} (A : ltty Σ) : ltty Σ := Ltty (λ w,
  ∃ (γ : gname) (l : loc) (lk : val) (v : val),
    ⌜ w = PairV lk #l ⌝ ∗
    is_lock γ lk (∃ v_inner, l ↦ v_inner ∗ ltty_car A v_inner) ∗
    spin_lock.locked γ ∗ l ↦ v)%I.

Definition lty_chan `{heapG Σ, chanG Σ} (P : lsty Σ) : ltty Σ :=
  Ltty (λ w, w ↣ lsty_car P)%I.

Instance: Params (@lty_copy) 1 := {}.
Instance: Params (@lty_copy_inv) 1 := {}.
Instance: Params (@lty_copyable) 1 := {}.
Instance: Params (@lty_arr) 2 := {}.
Instance: Params (@lty_prod) 1 := {}.
Instance: Params (@lty_sum) 1 := {}.
Instance: Params (@lty_forall) 2 := {}.
Instance: Params (@lty_sum) 1 := {}.
Instance: Params (@lty_ref_mut) 2 := {}.
Instance: Params (@lty_ref_shr) 2 := {}.
Instance: Params (@lty_mutex) 3 := {}.
Instance: Params (@lty_mutexguard) 3 := {}.
Instance: Params (@lty_chan) 3 := {}.

Notation any := lty_any.
Notation "()" := lty_unit : lty_scope.
Notation "'copy' A" := (lty_copy A) (at level 10) : lty_scope.
Notation "'copy-' A" := (lty_copy_inv A) (at level 10) : lty_scope.

Notation "A ⊸ B" := (lty_arr A B)
  (at level 99, B at level 200, right associativity) : lty_scope.
Notation "A → B" := (lty_copy (lty_arr A B)) : lty_scope.
Infix "*" := lty_prod : lty_scope.
Infix "+" := lty_sum : lty_scope.

Notation "∀ A1 .. An , C" :=
  (lty_forall (λ A1, .. (lty_forall (λ An, C%lty)) ..)) : lty_scope.
Notation "∃ A1 .. An , C" :=
  (lty_exist (λ A1, .. (lty_exist (λ An, C%lty)) ..)) : lty_scope.

Notation "'ref_mut' A" := (lty_ref_mut A) (at level 10) : lty_scope.
Notation "'ref_shr' A" := (lty_ref_shr A) (at level 10) : lty_scope.

Notation "'mutex' A" := (lty_mutex A) (at level 10) : lty_scope.
Notation "'mutexguard' A" := (lty_mutexguard A) (at level 10) : lty_scope.

Notation "'chan' A" := (lty_chan A) (at level 10) : lty_scope.

Section term_types.
  Context {Σ : gFunctors}.
  Implicit Types A : ltty Σ.

  Global Instance lty_copy_ne : NonExpansive (@lty_copy Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_copy_inv_ne : NonExpansive (@lty_copy_inv Σ).
  Proof. solve_proper. Qed.

  Global Instance lty_copyable_plain A : Plain (lty_copyable A).
  Proof. rewrite /lty_copyable /=. apply _. Qed.
  Global Instance lty_copyable_ne : NonExpansive (@lty_copyable Σ).
  Proof. rewrite /lty_copyable /=. solve_proper. Qed.

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

  Global Instance lty_ref_mut_contractive `{heapG Σ} : Contractive lty_ref_mut.
  Proof. solve_contractive. Qed.
  Global Instance lty_ref_mut_ne `{heapG Σ} : NonExpansive lty_ref_mut.
  Proof. solve_proper. Qed.

  Global Instance lty_ref_shr_contractive `{heapG Σ} : Contractive lty_ref_shr.
  Proof. solve_contractive. Qed.
  Global Instance lty_ref_shr_ne `{heapG Σ} : NonExpansive lty_ref_shr.
  Proof. solve_proper. Qed.

  Global Instance lty_mutex_contractive `{heapG Σ, lockG Σ} : Contractive lty_mutex.
  Proof. solve_contractive. Qed.
  Global Instance lty_mutex_ne `{heapG Σ, lockG Σ} : NonExpansive lty_mutex.
  Proof. solve_proper. Qed.

  Global Instance lty_mutexguard_contractive `{heapG Σ, lockG Σ} :
    Contractive lty_mutexguard.
  Proof. solve_contractive. Qed.
  Global Instance lty_mutexguard_ne `{heapG Σ, lockG Σ} : NonExpansive lty_mutexguard.
  Proof. solve_proper. Qed.

  Global Instance lty_chan_ne `{heapG Σ, chanG Σ} : NonExpansive lty_chan.
  Proof. solve_proper. Qed.
End term_types.