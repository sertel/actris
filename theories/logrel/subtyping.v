(** This file contains the definition of the semantic subtyping relation
[A <: B], where [A] and [B] can be either term types or session types, as
well as a semantic type equivalence relation [A <:> B], which is essentially
equivalent to having both [A <: B] and [B <: A]. Finally, the notion of a
*copyable type* is defined in terms of subtyping: a type [A] is copyable
when [A <: copy A]. *)
From actris.logrel Require Export model term_types.

Definition lsty_le_def {Σ} (P1 P2 : lsty Σ) :=
  iProto_le (lsty_car P1) (lsty_car P2).
Definition lsty_le_aux : seal (@lsty_le_def). by eexists. Qed.
Definition lsty_le := lsty_le_aux.(unseal).
Definition lsty_le_eq : @lsty_le = @lsty_le_def := lsty_le_aux.(seal_eq).
Arguments lsty_le {_} _ _.

Definition lty_le {Σ k} : lty Σ k → lty Σ k → iProp Σ :=
  match k with
  | tty_kind => λ A1 A2, ■ ∀ v, ltty_car A1 v -∗ ltty_car A2 v
  | lty_kind => λ P1 P2, ■ lsty_le P1 P2
  end%I.
Arguments lty_le : simpl never.
Infix "<:" := lty_le (at level 70) : bi_scope.
Instance: Params (@lty_le) 2 := {}.

Definition lty_bi_le {Σ k} (M1 M2 : lty Σ k) : iProp Σ :=
  tc_opaque (M1 <: M2 ∧ M2 <: M1)%I.
Arguments lty_bi_le : simpl never.
Infix "<:>" := lty_bi_le (at level 70) : bi_scope.
Instance: Params (@lty_bi_le) 2 := {}.

Definition lty_copyable {Σ} (A : ltty Σ) : iProp Σ :=
  tc_opaque (A <: lty_copy A)%I.
Instance: Params (@lty_copyable) 1 := {}.

Section subtyping.
  Context {Σ : gFunctors}.

  Global Instance lty_le_plain {k} (M1 M2 : lty Σ k) : Plain (M1 <: M2).
  Proof. destruct k; apply _. Qed.
  Global Instance lty_bi_le_plain {k} (M1 M2 : lty Σ k) : Plain (M1 <:> M2).
  Proof. rewrite /lty_bi_le /=. apply _. Qed.

  Global Instance lty_le_ne : NonExpansive2 (@lty_le Σ k).
  Proof.
    rewrite /lty_le lsty_le_eq. destruct k; rewrite ?/lsty_le_def; solve_proper.
  Qed.
  Global Instance lty_le_proper {k} : Proper ((≡) ==> (≡) ==> (≡)) (@lty_le Σ k).
  Proof. apply (ne_proper_2 _). Qed.
  Global Instance lty_bi_le_ne {k} : NonExpansive2 (@lty_bi_le Σ k).
  Proof. solve_proper. Qed.
  Global Instance lty_bi_le_proper {k} : Proper ((≡) ==> (≡) ==> (≡)) (@lty_bi_le Σ k).
  Proof. solve_proper. Qed.

  Global Instance lty_copyable_plain A : Plain (@lty_copyable Σ A).
  Proof. rewrite /lty_copyable /=. apply _. Qed.
  Global Instance lty_copyable_ne : NonExpansive (@lty_copyable Σ).
  Proof. rewrite /lty_copyable /=. solve_proper. Qed.
End subtyping.
