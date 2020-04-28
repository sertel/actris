From iris.algebra Require Export gmap.
From actris.logrel Require Export model.
From actris.channel Require Export channel.

Definition lty_end {Σ} : lsty Σ := Lsty END.

Definition lty_message {Σ} (a : action) (A : ltty Σ) (S : lsty Σ) : lsty Σ :=
  Lsty (<a@v> MSG v {{ ▷ ltty_car A v }}; lsty_car S).

Definition lty_choice {Σ} (a : action) (Ss : gmap Z (lsty Σ)) : lsty Σ :=
  Lsty (<a@(x : Z)> MSG #x {{ ⌜is_Some (Ss !! x)⌝ }}; lsty_car (Ss !!! x)).

Definition lty_dual {Σ} (S : lsty Σ) : lsty Σ :=
  Lsty (iProto_dual (lsty_car S)).
Definition lty_app {Σ} (S1 S2 : lsty Σ) : lsty Σ :=
  Lsty (lsty_car S1 <++> lsty_car S2).

Instance: Params (@lty_message) 2 := {}.
Instance: Params (@lty_choice) 2 := {}.
Instance: Params (@lty_dual) 1 := {}.
Instance: Params (@lty_app) 1 := {}.

Notation "'END'" := lty_end : lty_scope.
Notation "<!!> A ; S" :=
  (lty_message Send A S) (at level 20, A, S at level 200) : lty_scope.
Notation "<??> A ; S" :=
  (lty_message Recv A S) (at level 20, A, S at level 200) : lty_scope.
Notation lty_select := (lty_choice Send).
Notation lty_branch := (lty_choice Recv).
Infix "<++>" := lty_app (at level 60) : lty_scope.
Notation "( S <++>.)" := (lty_app S) (only parsing) : lty_scope.
Notation "(.<++> T )" := (λ S, lty_app S T) (only parsing) : lty_scope.

Section session_types.
  Context {Σ : gFunctors}.

  Global Instance lty_message_ne a : NonExpansive2 (@lty_message Σ a).
  Proof. solve_proper. Qed.
  Global Instance lty_message_proper a :
    Proper ((≡) ==> (≡) ==> (≡)) (@lty_message Σ a).
  Proof. apply ne_proper_2, _. Qed.
  Global Instance lty_message_contractive n a :
    Proper (dist_later n ==> dist_later n ==> dist n) (@lty_message Σ a).
  Proof. solve_contractive. Qed.

  Global Instance lty_choice_ne a : NonExpansive (@lty_choice Σ a).
  Proof. solve_proper. Qed.
  Global Instance lty_choice_proper a : Proper ((≡) ==> (≡)) (@lty_choice Σ a).
  Proof. apply ne_proper, _. Qed.
(* FIXME
  Global Instance lty_choice_contractive a : Contractive (@lty_choice Σ a).
  Proof. solve_contractive. Qed.
*)
  Global Instance lty_dual_ne : NonExpansive (@lty_dual Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_dual_proper : Proper ((≡) ==> (≡)) (@lty_dual Σ).
  Proof. apply ne_proper, _. Qed.

  Global Instance lty_app_ne : NonExpansive2 (@lty_app Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_app_proper : Proper ((≡) ==> (≡) ==> (≡)) (@lty_app Σ).
  Proof. apply ne_proper_2, _. Qed.
End session_types.
