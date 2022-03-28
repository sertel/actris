(** This file contains definitions related to type contexts.
Contexts are encoded as lists of value and type pairs, for which
lifted operations are defined such as [ctx_cons x A Γ].

The following relations on contexts are defined:
- [ctx_ltyped Γ vs]: This relation indicates that the value map [vs] contains a
  value for each type in the semantic type context [Γ].
- [ctx_le Γ Γ']: This relation indicates that the context [Γ]
  subsumes that of [Γ'].

In addition, some lemmas/rules about these definitions are proved, corresponding
to the syntactic typing rules that are typically found in substructural type
systems. *)
From iris.algebra Require Export list.
From iris.bi.lib Require Import core.
From iris.proofmode Require Import proofmode.
From actris.logrel Require Export term_types subtyping_rules.

Inductive ctx_item Σ := CtxItem {
  ctx_item_name : string;
  ctx_item_type : ltty Σ;
}.
Add Printing Constructor ctx_item.
Arguments CtxItem {_} _ _.
Arguments ctx_item_name {_} _.
Arguments ctx_item_type {_} _.
Global Instance: Params (@CtxItem) 2 := {}.
Global Instance: Params (@ctx_item_type) 1 := {}.

Section ctx_item_ofe.
  Context {Σ : gFunctors}.
  Instance ctx_item_equiv : Equiv (ctx_item Σ) := λ xA1 xA2,
    ctx_item_name xA1 = ctx_item_name xA2 ∧ ctx_item_type xA1 ≡ ctx_item_type xA2.
  Instance ctx_item_dist : Dist (ctx_item Σ) := λ n xA1 xA2,
    ctx_item_name xA1 = ctx_item_name xA2 ∧ ctx_item_type xA1 ≡{n}≡ ctx_item_type xA2.
  Lemma ctx_item_ofe_mixin : OfeMixin (ctx_item Σ).
  Proof.
    by apply (iso_ofe_mixin (A:=prodO (leibnizO string) (lttyO Σ))
      (λ xA, (ctx_item_name xA, ctx_item_type xA))).
  Qed.
  Canonical Structure ctx_itemO := Ofe (ctx_item Σ) ctx_item_ofe_mixin.
  Global Instance ctx_item_type_ne : NonExpansive (@ctx_item_type Σ).
  Proof. by intros n ?? [??]. Qed.
  Global Instance ctx_item_type_proper : Proper ((≡) ==> (≡)) (@ctx_item_type Σ).
  Proof. by intros ?? [??]. Qed.
End ctx_item_ofe.

Notation ctx Σ := (list (ctx_item Σ)).

Definition ctx_filter_eq {Σ} (x : binder) : ctx Σ → ctx Σ :=
  filter (λ xA, x = BNamed (ctx_item_name xA)).
Definition ctx_filter_ne {Σ} (x : binder) : ctx Σ → ctx Σ :=
  filter (λ xA, x ≠ BNamed (ctx_item_name xA)).

Arguments ctx_filter_eq _ !_ !_ / : simpl nomatch.
Arguments ctx_filter_ne _ !_ !_ / : simpl nomatch.
(** TODO: Move to std++, together with some lemmas about filter that can be
factored out. *)
Arguments filter _ _ _ _ _ !_ / : simpl nomatch.

Global Instance ctx_lookup {Σ} : Lookup string (ltty Σ) (ctx Σ) := λ x Γ,
  match ctx_filter_eq x Γ with
  | [CtxItem _ A] => Some A
  | _ => None
  end.

Definition ctx_cons {Σ} (b : binder) (A : ltty Σ) (Γ : ctx Σ) : ctx Σ :=
  if b is BNamed x then CtxItem x A :: ctx_filter_ne x Γ else Γ.

Definition ctx_ltyped {Σ} (vs : gmap string val) (Γ : ctx Σ) : iProp Σ :=
  ([∗ list] iA ∈ Γ, ∃ v,
    ⌜vs !! ctx_item_name iA = Some v⌝ ∗ ltty_car (ctx_item_type iA) v)%I.
Global Instance: Params (@ctx_ltyped) 2 := {}.

Definition ctx_le {Σ} (Γ1 Γ2 : ctx Σ) : iProp Σ :=
  tc_opaque (■ ∀ vs, ctx_ltyped vs Γ1 -∗ ctx_ltyped vs Γ2)%I.
Global Instance: Params (@ctx_le) 1 := {}.
Infix "<ctx:" := ctx_le (at level 70) : bi_scope.
Notation "Γ1 <ctx: Γ2" := (⊢ Γ1 <ctx: Γ2) (at level 70) : type_scope.

Section ctx.
  Context {Σ : gFunctors}.
  Implicit Types A : ltty Σ.
  Implicit Types Γ : ctx Σ.

  (** ctx_filter *)
  Lemma ctx_filter_eq_perm Γ x : Γ ≡ₚ ctx_filter_eq x Γ ++ ctx_filter_ne x Γ.
  Proof.
    rewrite /ctx_filter_eq /ctx_filter_ne.
    induction Γ as [|[y A] Γ IH]; simpl; [done|].
    rewrite filter_cons. case_decide.
    - rewrite filter_cons_False /=; last naive_solver. by rewrite -IH.
    - rewrite filter_cons_True /=; last naive_solver.
      by rewrite -Permutation_middle -IH.
  Qed.

  Lemma ctx_filter_eq_cons (Γ : ctx Σ) (x:string) A :
    ctx_filter_eq x (CtxItem x A :: Γ) = CtxItem x A :: ctx_filter_eq x Γ.
  Proof. rewrite /ctx_filter_eq filter_cons_True; naive_solver. Qed.
  Lemma ctx_filter_eq_cons_ne Γ x y A :
    x ≠ BNamed y →
    ctx_filter_eq x (CtxItem y A :: Γ) = ctx_filter_eq x Γ.
  Proof. intros. rewrite /ctx_filter_eq filter_cons_False; naive_solver. Qed.

  Lemma ctx_filter_ne_anon Γ : ctx_filter_ne BAnon Γ = Γ.
  Proof. induction Γ as [|[y A] Γ IH]; by f_equal/=. Qed.

  Lemma elem_of_ctx_filter_ne Γ x y B :
    CtxItem y B ∈ ctx_filter_ne x Γ → x ≠ y.
  Proof. intros ?%elem_of_list_filter. naive_solver. Qed.

  Lemma ctx_filter_ne_cons Γ (x : string) A :
    ctx_filter_ne x (CtxItem x A :: Γ) = ctx_filter_ne x Γ.
  Proof. rewrite /ctx_filter_ne filter_cons_False; naive_solver. Qed.
  Lemma ctx_filter_ne_cons_ne Γ x y A :
    x ≠ BNamed y →
    ctx_filter_ne x (CtxItem y A :: Γ) = CtxItem y A :: ctx_filter_ne x Γ.
  Proof. intros. rewrite /ctx_filter_ne filter_cons_True; naive_solver. Qed.

  Lemma ctx_filter_ne_idemp Γ x :
    ctx_filter_ne x (ctx_filter_ne x Γ) = ctx_filter_ne x Γ.
  Proof.
    induction Γ as [|[y A] Γ HI].
    - eauto.
    - destruct (decide (x = y)) as [->|].
      + rewrite ctx_filter_ne_cons. apply HI.
      + rewrite ctx_filter_ne_cons_ne; [ | done ].
        rewrite ctx_filter_ne_cons_ne; [ | done ].
        f_equiv. apply HI.
  Qed.

  Lemma ctx_filter_eq_ne_nil (Γ : ctx Σ) x :
    ctx_filter_eq x (ctx_filter_ne x Γ) = [].
  Proof.
    induction Γ as [|[y A] Γ HI].
    - done.
    - destruct (decide (x = y)) as [-> | ].
      + rewrite ctx_filter_ne_cons. apply HI.
      + rewrite ctx_filter_ne_cons_ne; [ | done ];
          rewrite ctx_filter_eq_cons_ne; [ apply HI | done ].
  Qed.

  Lemma ctx_lookup_perm Γ x A:
    Γ !! x = Some A →
    Γ ≡ₚ CtxItem x A :: ctx_filter_ne x Γ.
  Proof.
    rewrite /lookup /ctx_lookup=> ?.
    destruct (ctx_filter_eq x Γ) as [|[x' ?] [|??]] eqn:Hx; simplify_eq/=.
    assert (CtxItem x' A ∈ ctx_filter_eq x Γ)
      as [? _]%elem_of_list_filter; simplify_eq/=.
    { rewrite Hx. set_solver. }
    by rewrite {1}(ctx_filter_eq_perm Γ x') Hx.
  Qed.

  Lemma ctx_insert_lookup Γ x A :
    (CtxItem x A :: (ctx_filter_ne x Γ)) !! x = Some A.
  Proof.
    by rewrite /lookup /ctx_lookup ctx_filter_eq_cons ctx_filter_eq_ne_nil.
  Qed.

  (** ctx typing *)
  Global Instance ctx_ltyped_Permutation vs :
    Proper ((≡ₚ) ==> (⊣⊢)) (@ctx_ltyped Σ vs).
  Proof. intros Γ Γ' HΓ. by rewrite /ctx_ltyped HΓ. Qed.
  Global Instance ctx_ltyped_ne vs : NonExpansive (@ctx_ltyped Σ vs).
  Proof.
    intros n Γ Γ' HΓ. rewrite /ctx_ltyped.
    apply big_opL_gen_proper_2; [done|apply _|]. intros k.
    assert (Γ !! k ≡{n}≡ Γ' !! k) as HΓk by (by rewrite HΓ).
    case: HΓk=> // -[x1 A1] [x2 A2] [/= -> ?]. by repeat f_equiv.
  Qed.
  Global Instance ctx_ltyped_proper vs : Proper ((≡) ==> (≡)) (@ctx_ltyped Σ vs).
  Proof. apply (ne_proper _). Qed.

  Lemma ctx_ltyped_nil vs : ⊢@{iPropI Σ} ctx_ltyped vs [].
  Proof. done. Qed.

  Lemma ctx_ltyped_app Γ1 Γ2 vs :
    ctx_ltyped vs (Γ1 ++ Γ2) ⊣⊢ ctx_ltyped vs Γ1 ∗ ctx_ltyped vs Γ2.
  Proof. apply big_opL_app. Qed.

  Lemma ctx_ltyped_cons Γ vs x A :
    ctx_ltyped vs (CtxItem x A :: Γ) ⊣⊢ ∃ v,
    ⌜vs !! x = Some v⌝ ∗ ltty_car A v ∗ ctx_ltyped vs Γ.
  Proof.
    iSplit; [by iIntros "[HA $]"|].
    iDestruct 1 as (v ?) "[HA $]"; eauto.
  Qed.

  Lemma ctx_ltyped_insert Γ vs x A v :
    ltty_car A v -∗
    ctx_ltyped vs (ctx_filter_ne x Γ) -∗
    ctx_ltyped (binder_insert x v vs) (ctx_cons x A Γ).
  Proof.
    iIntros "HA HΓ".
    destruct x as [|x]; simpl; [rewrite ctx_filter_ne_anon; auto|].
    iApply ctx_ltyped_cons. iExists _; iSplit; [by rewrite lookup_insert|].
    iFrame "HA". iApply (big_sepL_impl with "HΓ").
    iIntros "!>" (k [j B] ?%elem_of_list_lookup_2%elem_of_ctx_filter_ne).
    iDestruct 1 as (w ?) "HB". iExists w. iIntros "{$HB} !%".
    apply lookup_insert_Some; naive_solver.
  Qed.

  Lemma ctx_ltyped_insert' Γ vs x A v :
    ltty_car A v -∗
    ctx_ltyped vs Γ -∗
    ctx_ltyped (binder_insert x v vs) (ctx_cons x A Γ).
  Proof.
    rewrite {1}(ctx_filter_eq_perm Γ x) ctx_ltyped_app.
    iIntros "HA [_ HΓ]". by iApply (ctx_ltyped_insert with "HA").
  Qed.

  Lemma ctx_ltyped_delete Γ x v vs :
    ctx_ltyped (binder_insert x v vs) Γ -∗
    ctx_ltyped vs (ctx_filter_ne x Γ).
  Proof.
    rewrite {1}(ctx_filter_eq_perm Γ x) ctx_ltyped_app. iIntros "[_ HΓ]".
    iApply (big_sepL_impl with "HΓ").
    iIntros "!>" (k [j B] ?%elem_of_list_lookup_2%elem_of_ctx_filter_ne).
    iDestruct 1 as (w Hx) "HB". simpl in *. iExists w. iIntros "{$HB} !%".
    destruct x as [|x]; simplify_eq/=; auto.
    revert Hx. rewrite lookup_insert_Some. naive_solver.
  Qed.

  (** Context subtyping *)
  Global Instance ctx_le_plain Γ1 Γ2 : Plain (Γ1 <ctx: Γ2).
  Proof. rewrite /ctx_le /=. apply _. Qed.

  Global Instance ctx_le_Permutation : Proper ((≡ₚ) ==> (≡ₚ) ==> (≡)) (@ctx_le Σ).
  Proof.
    intros Γ1 Γ1' HΓ1 Γ2 Γ2' HΓ2. rewrite /ctx_le /=.
    setoid_rewrite HΓ1; by setoid_rewrite HΓ2.
  Qed.
  Global Instance ctx_le_ne : NonExpansive2 (@ctx_le Σ).
  Proof. solve_proper. Qed.
  Global Instance ctx_le_proper : Proper ((≡) ==> (≡) ==> (≡)) (@ctx_le Σ).
  Proof. apply (ne_proper_2 _). Qed.

  Lemma ctx_le_refl Γ : Γ <ctx: Γ.
  Proof. iIntros (vs); auto. Qed.
  Lemma ctx_le_trans Γ1 Γ2 Γ3 : Γ1 <ctx: Γ2 -∗ Γ2 <ctx: Γ3 -∗ Γ1 <ctx: Γ3.
  Proof.
    rewrite /ctx_le /=.
    iIntros "#H1 #H2 !>" (vs) "Hvs". iApply "H2". by iApply "H1".
  Qed.
  Lemma ctx_le_nil Γ : Γ <ctx: [].
  Proof. iIntros (vs) "!> _". iApply ctx_ltyped_nil. Qed.
  Lemma ctx_le_cons x Γ1 Γ2 A1 A2 :
    A1 <: A2 -∗ Γ1 <ctx: Γ2 -∗ CtxItem x A1 :: Γ1 <ctx: CtxItem x A2 :: Γ2.
  Proof.
    rewrite /ctx_le /=. iIntros "#H #H' !>" (vs) "Hvs".
    iDestruct (ctx_ltyped_cons with "Hvs") as (v ?) "[Hv Hvs]".
    iApply ctx_ltyped_cons. iExists _; iSplit; [done|].
    iSplitL "Hv"; [by iApply "H"|by iApply "H'"].
  Qed.
  Lemma ctx_le_app Γ1 Γ2 Γ1' Γ2' :
    Γ1 <ctx: Γ2 -∗ Γ1' <ctx: Γ2' -∗ Γ1 ++ Γ1' <ctx: Γ2 ++ Γ2'.
  Proof.
    rewrite /ctx_le /=. iIntros "#H #H' !>" (vs) "Hvs".
    iDestruct (ctx_ltyped_app with "Hvs") as "[Hvs1 Hvs2]".
    iApply ctx_ltyped_app. iSplitL "Hvs1"; [by iApply "H"|by iApply "H'"].
  Qed.
  Lemma ctx_le_copy x A :
    [CtxItem x A] <ctx: [CtxItem x A; CtxItem x (copy- A)].
  Proof.
    iIntros "!>" (vs) "Hvs".
    iDestruct (ctx_ltyped_cons with "Hvs") as (v ?) "[HA _]".
    iAssert (ltty_car (copy- A) v)%lty as "#HAm"; [by iApply coreP_intro|].
    iApply ctx_ltyped_cons. iExists _; iSplit; [done|]. iFrame "HA".
    iApply ctx_ltyped_cons. iExists _; iSplit; [done|]. iFrame "HAm".
    iApply ctx_ltyped_nil.
  Qed.
  Lemma ctx_le_copyable x A :
    lty_copyable A -∗
    [CtxItem x A] <ctx: [CtxItem x A; CtxItem x A].
  Proof.
    iIntros "#H". iApply ctx_le_trans; [iApply ctx_le_copy|].
    iApply ctx_le_cons; [iApply lty_le_refl|].
    iApply ctx_le_cons; [by iApply lty_le_copy_inv_elim_copyable|iApply ctx_le_nil].
  Qed.
End ctx.
