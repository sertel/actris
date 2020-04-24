From actris.logrel Require Export model.

Definition lty_le {Σ k} : lty Σ k → lty Σ k → iProp Σ :=
  match k with
  | tty_kind => λ A1 A2, ■ ∀ v, ltty_car A1 v -∗ ltty_car A2 v
  | lty_kind => λ P1 P2, ■ iProto_le (lsty_car P1) (lsty_car P2)
  end%I.
Arguments lty_le : simpl never.
Infix "<:" := lty_le (at level 70) : bi_scope.
Instance: Params (@lty_le) 2 := {}.

Definition lty_bi_le {Σ k} (M1 M2 : lty Σ k) : iProp Σ :=
  tc_opaque (M1 <: M2 ∧ M2 <: M1)%I.
Arguments lty_bi_le : simpl never.
Infix "<:>" := lty_bi_le (at level 70) : bi_scope.
Instance: Params (@lty_bi_le) 2 := {}.

Section subtyping.
  Context {Σ : gFunctors}.

  Global Instance lty_le_plain {k} (M1 M2 : lty Σ k) : Plain (M1 <: M2).
  Proof. destruct k; apply _. Qed.
  Global Instance lty_bi_le_plain {k} (M1 M2 : lty Σ k) : Plain (M1 <:> M2).
  Proof. rewrite /lty_bi_le /=. apply _. Qed.

  Global Instance lty_le_ne : NonExpansive2 (@lty_le Σ k).
  Proof. destruct k; solve_proper. Qed.
  Global Instance lty_le_proper {k} : Proper ((≡) ==> (≡) ==> (≡)) (@lty_le Σ k).
  Proof. apply (ne_proper_2 _). Qed.
  Global Instance lty_bi_le_ne {k} : NonExpansive2 (@lty_bi_le Σ k).
  Proof. solve_proper. Qed.
  Global Instance lty_bi_le_proper {k} : Proper ((≡) ==> (≡) ==> (≡)) (@lty_bi_le Σ k).
  Proof. solve_proper. Qed.
End subtyping.
