(** This file contains definitions related to type environments. The following
relations on environments are defined:

- [env_ltyped Γ vs]: This relation indicates that the value map [vs] contains a
  value for each type in the semantic type environment [Γ].
- [env_split Γ Γ1 Γ2]: The semantic type environment [Γ] can be split into
  (semantically disjoint) [Γ1] and [Γ2].
- [env_copy Γ Γ']: [Γ'] is a copyable sub-environment of [Γ].

In addition, some lemmas/rules about these definitions are proved, corresponding
to the syntactic typing rules that are typically found in substructural type
systems. *)
From actris.logrel Require Export term_types subtyping.
From iris.proofmode Require Import tactics.
From iris.algebra Require Export list.

Inductive env_item Σ := EnvItem {
  env_item_name : string;
  env_item_type : ltty Σ;
}.
Add Printing Constructor env_item.
Arguments EnvItem {_} _ _.
Arguments env_item_name {_} _.
Arguments env_item_type {_} _.
Instance: Params (@EnvItem) 2 := {}.
Instance: Params (@env_item_type) 1 := {}.

Section env_item_ofe.
  Context {Σ : gFunctors}.
  Instance env_item_equiv : Equiv (env_item Σ) := λ xA1 xA2,
    env_item_name xA1 = env_item_name xA2 ∧ env_item_type xA1 ≡ env_item_type xA2.
  Instance env_item_dist : Dist (env_item Σ) := λ n xA1 xA2,
    env_item_name xA1 = env_item_name xA2 ∧ env_item_type xA1 ≡{n}≡ env_item_type xA2.
  Lemma env_item_ofe_mixin : OfeMixin (env_item Σ).
  Proof.
    by apply (iso_ofe_mixin (A:=prodO (leibnizO string) (lttyO Σ))
      (λ xA, (env_item_name xA, env_item_type xA))).
  Qed.
  Canonical Structure env_itemO := OfeT (env_item Σ) env_item_ofe_mixin.
  Global Instance env_item_type_ne : NonExpansive (@env_item_type Σ).
  Proof. by intros n ?? [??]. Qed.
  Global Instance env_item_type_proper : Proper ((≡) ==> (≡)) (@env_item_type Σ).
  Proof. by intros ?? [??]. Qed.
End env_item_ofe.

Notation env Σ := (list (env_item Σ)).

Definition env_filter_eq {Σ} (x : binder) : env Σ → env Σ :=
  filter (λ xA, x = BNamed (env_item_name xA)).
Definition env_filter_ne {Σ} (x : binder) : env Σ → env Σ :=
  filter (λ xA, x ≠ BNamed (env_item_name xA)).

Arguments env_filter_eq _ !_ !_ / : simpl nomatch.
Arguments env_filter_ne _ !_ !_ / : simpl nomatch.
(** TODO: Move to std++, together with some lemmas about filter that can be
factored out. *)
Arguments filter _ _ _ _ _ !_ / : simpl nomatch.

Definition env_cons {Σ} (b : binder) (A : ltty Σ) (Γ : env Σ) : env Σ :=
  if b is BNamed x then EnvItem x A :: env_filter_ne x Γ else Γ.

Definition env_ltyped {Σ} (vs : gmap string val) (Γ : env Σ) : iProp Σ :=
  ([∗ list] iA ∈ Γ, ∃ v,
    ⌜vs !! env_item_name iA = Some v⌝ ∗ ltty_car (env_item_type iA) v)%I.
Instance: Params (@env_ltyped) 2 := {}.

Definition env_le {Σ} (Γ1 Γ2 : env Σ) : iProp Σ :=
  tc_opaque (■ ∀ vs, env_ltyped vs Γ1 -∗ env_ltyped vs Γ2)%I.
Instance: Params (@env_le) 1 := {}.

Section env.
  Context {Σ : gFunctors}.
  Implicit Types A : ltty Σ.
  Implicit Types Γ : env Σ.

  (** env_filter *)
  Lemma env_filter_eq_perm Γ x : Γ ≡ₚ env_filter_eq x Γ ++ env_filter_ne x Γ.
  Proof.
    rewrite /env_filter_eq /env_filter_ne.
    induction Γ as [|[y A] Γ IH]; simpl; [done|].
    rewrite filter_cons. case_decide.
    - rewrite filter_cons_False /=; last naive_solver. by rewrite -IH.
    - rewrite filter_cons_True /=; last naive_solver.
      by rewrite -Permutation_middle -IH.
  Qed.
  Lemma env_filter_eq_perm' Γ Γ' x :
    env_filter_eq x Γ = Γ' →
    Γ ≡ₚ Γ' ++ env_filter_ne x Γ.
  Proof. intros <-. apply env_filter_eq_perm. Qed.

  Lemma env_filter_ne_anon Γ : env_filter_ne BAnon Γ = Γ.
  Proof. induction Γ as [|[y A] Γ IH]; by f_equal/=. Qed.

  Lemma elem_of_env_filter_ne Γ x y B :
    EnvItem y B ∈ env_filter_ne x Γ → x ≠ y.
  Proof. intros ?%elem_of_list_filter. naive_solver. Qed.

  Lemma env_filter_ne_cons Γ (x : string) A :
    env_filter_ne x (EnvItem x A :: Γ) = env_filter_ne x Γ.
  Proof. rewrite /env_filter_ne filter_cons_False; naive_solver. Qed.
  Lemma env_filter_ne_cons_ne Γ x y A :
    x ≠ BNamed y →
    env_filter_ne x (EnvItem y A :: Γ) = EnvItem y A :: env_filter_ne x Γ.
  Proof. intros. rewrite /env_filter_ne filter_cons_True; naive_solver. Qed.

  (** env typing *)
  Global Instance env_ltyped_Permutation vs :
    Proper ((≡ₚ) ==> (⊣⊢)) (@env_ltyped Σ vs).	
  Proof. intros Γ Γ' HΓ. by rewrite /env_ltyped HΓ. Qed.
  Global Instance env_ltyped_ne vs : NonExpansive (@env_ltyped Σ vs).
  Proof.
    intros n Γ Γ' HΓ. rewrite /env_ltyped.
    apply big_opL_gen_proper_2; [done|apply _|]. intros k.
    assert (Γ !! k ≡{n}≡ Γ' !! k) as HΓk by (by rewrite HΓ).
    case: HΓk=> // -[x1 A1] [x2 A2] [/= -> ?]. by repeat f_equiv.
  Qed.
  Global Instance env_ltyped_proper vs : Proper ((≡) ==> (≡)) (@env_ltyped Σ vs).
  Proof. apply (ne_proper _). Qed.

  Lemma env_ltyped_nil vs : ⊢@{iPropI Σ} env_ltyped vs [].
  Proof. done. Qed.

  Lemma env_ltyped_app Γ1 Γ2 vs :
    env_ltyped vs (Γ1 ++ Γ2) ⊣⊢ env_ltyped vs Γ1 ∗ env_ltyped vs Γ2.
  Proof. apply big_opL_app. Qed.

  Lemma env_ltyped_cons Γ vs x A : 
    env_ltyped vs (EnvItem x A :: Γ) ⊣⊢ ∃ v,
    ⌜vs !! x = Some v⌝ ∗ ltty_car A v ∗ env_ltyped vs Γ.
  Proof.
    iSplit; [by iIntros "[HA $]"|].
    iDestruct 1 as (v ?) "[HA $]"; eauto.
  Qed.

  Lemma env_ltyped_insert Γ vs x A v :
    ltty_car A v -∗
    env_ltyped vs (env_filter_ne x Γ) -∗
    env_ltyped (binder_insert x v vs) (env_cons x A Γ).
  Proof.
    iIntros "HA HΓ".
    destruct x as [|x]; simpl; [rewrite env_filter_ne_anon; auto|].
    iApply env_ltyped_cons. iExists _; iSplit; [by rewrite lookup_insert|].
    iFrame "HA". iApply (big_sepL_impl with "HΓ").
    iIntros "!>" (k [j B] ?%elem_of_list_lookup_2%elem_of_env_filter_ne).
    iDestruct 1 as (w ?) "HB". iExists w. iIntros "{$HB} !%".
    apply lookup_insert_Some; naive_solver.
  Qed.

  Lemma env_ltyped_delete Γ x v vs :
    env_ltyped (binder_insert x v vs) Γ -∗
    env_ltyped vs (env_filter_ne x Γ).
  Proof.
    rewrite {1}(env_filter_eq_perm Γ x) env_ltyped_app. iIntros "[_ HΓ]".
    iApply (big_sepL_impl with "HΓ").
    iIntros "!>" (k [j B] ?%elem_of_list_lookup_2%elem_of_env_filter_ne).
    iDestruct 1 as (w Hx) "HB". simpl in *. iExists w. iIntros "{$HB} !%".
    destruct x as [|x]; simplify_eq/=; auto.
    revert Hx. rewrite lookup_insert_Some. naive_solver.
  Qed.

  (** Environment subtyping *)
  Global Instance env_le_plain Γ1 Γ2 : Plain (env_le Γ1 Γ2).
  Proof. rewrite /env_le /=. apply _. Qed.

  Global Instance env_le_Permutation : Proper ((≡ₚ) ==> (≡ₚ) ==> (≡)) (@env_le Σ).
  Proof.
    intros Γ1 Γ1' HΓ1 Γ2 Γ2' HΓ2. rewrite /env_le /=.
    setoid_rewrite HΓ1; by setoid_rewrite HΓ2.
  Qed.
  Global Instance env_le_ne : NonExpansive2 (@env_le Σ).
  Proof. solve_proper. Qed.
  Global Instance env_le_proper : Proper ((≡) ==> (≡) ==> (≡)) (@env_le Σ).
  Proof. apply (ne_proper_2 _). Qed.

  Lemma env_le_refl Γ : ⊢ env_le Γ Γ.
  Proof. iIntros (vs); auto. Qed.
  Lemma env_le_trans Γ1 Γ2 Γ3 : env_le Γ1 Γ2 -∗ env_le Γ2 Γ3 -∗ env_le Γ1 Γ3.
  Proof.
    rewrite /env_le /=.
    iIntros "#H1 #H2 !>" (vs) "Hvs". iApply "H2". by iApply "H1".
  Qed.
  Lemma env_le_nil Γ : ⊢ env_le Γ [].
  Proof. iIntros (vs) "!> _". iApply env_ltyped_nil. Qed.
  Lemma env_le_cons x Γ1 Γ2 A1 A2 :
    A1 <: A2 -∗ env_le Γ1 Γ2 -∗ env_le (EnvItem x A1 :: Γ1) (EnvItem x A2 :: Γ2).
  Proof.
    rewrite /env_le /=. iIntros "#H #H' !>" (vs) "Hvs".
    iDestruct (env_ltyped_cons with "Hvs") as (v ?) "[Hv Hvs]".
    iApply env_ltyped_cons. iExists _; iSplit; [done|].
    iSplitL "Hv"; [by iApply "H"|by iApply "H'"].
  Qed.
  Lemma env_le_app Γ1 Γ2 Γ1' Γ2' :
    env_le Γ1 Γ2 -∗ env_le Γ1' Γ2' -∗ env_le (Γ1 ++ Γ1') (Γ2 ++ Γ2').
  Proof.
    rewrite /env_le /=. iIntros "#H #H' !>" (vs) "Hvs".
    iDestruct (env_ltyped_app with "Hvs") as "[Hvs1 Hvs2]".
    iApply env_ltyped_app. iSplitL "Hvs1"; [by iApply "H"|by iApply "H'"].
  Qed.
End env.
